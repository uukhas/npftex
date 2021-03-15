(* Author: Uladzimir Khasianevich *)

BeginPackage@"npftex`";
initialize; texify; processRules; matchRules; addRule; real; length; vertex;

$stringLength = 100;
$Factor = 16*Pi^2;
Begin@"`Private`";

secure[s_Symbol] := s;

$Diagrams = Null;
$Model = "";
$Particles = {};
$NPF = {};
Protect[$Diagrams, $Model, $Particles, $NPF];

$texRules =
{  SARAH`Delta[a_, b_] :> "\\delta_{"<>index@a<>index@b<>"}",
   SARAH`Mass[e_] :> "m_{"<>eField@gField[e]<>"}",
   Power[s_String, i_Integer /; i>0] :> s<>"^{"<>ToString@i<>"}",
   Power[e_, -1] :> String["\\frac{1}{", e, "}"],
   Power[s_String, i_Integer /; i<0] :> "\\frac{1}{"<>s<>"^{"<>ToString[-i]<>"}}"};
Protect[$texRules];

length[] := If[$NPF === 0, 0, Length@$NPF[[2, 1, 1]]];
length // secure;

real[s__Symbol] :=
   With[{one=#}, Susyno`LieGroups`conj@one = one;] &/@ {s};
real // secure;

addRule[r_RuleDelayed] :=
(  Unprotect@$texRules;
   PrependTo[$texRules, r];
   Protect@$texRules;);
addRule // secure;


name[i_Integer -> s_String] :=
(  Unprotect@$Particles;
   $Particles[[i]] = $Particles[[i,1]] -> s;
   Protect@$Particles;);
name // secure;

makePlain[expr_] :=
Module[{plus, times, res},
   plus[e__] := Riffle[{e}, "+"];
   times[e__] := times /@ {e};
   times[s_Symbol] := s;
   times[s_String] := s;
   times[-1] := "-";
   times[i_Integer] := ToString@i;
   times[l_List] := Sequence["(", Sequence @@ l, ")"];
   times[e_] := ToString@TeXForm@e;
   List[expr //. {Plus->plus, Times->times, String->List, List->Sequence}]];
makePlain // secure;

restore[] :=
(  Unprotect[$Diagrams, $Model, $Particles, $NPF];
   $Diagrams = Null;
   $Model = "";
   $Particles = {};
   $NPF = {};
   Protect[$Diagrams, $Model, $Particles, $NPF];);
restore // secure;

privateGet[file_String?FileExistsQ] :=
Module[{res},
   BeginPackage@"npftex`";
   Begin@"`Private`";
   res = Get@file;
   End[];
   EndPackage[];
   $ContextPath = DeleteCases[$ContextPath, "npftex`"];
   res];
privateGet // secure;

initialize[fafile:_String, npffile:_String:""] :=
Module[{npfs, pos},
   If[FileExistsQ@fafile,
      Unprotect[$Diagrams, $Model, $Particles];
      $Diagrams = List @@ privateGet[fafile][[1,All,1,1]];
      $ContextPath = DeleteCases[$ContextPath, "npftex`"];
      $Model = FileNameSplit[fafile][[-4]];
      $Name = StringDrop[FileNameSplit[fafile][[-1]], -2];
      $Particles = #->#& /@ DeleteDuplicates@Cases[$Diagrams,
         PropagatorGraphics[_, name_String ,_] :> name, Infinity,
         Heads -> True];
      Protect[$Diagrams, $Model, $Particles];,
      Print[fafile, " doesn't exist."];
      restore[];
      Abort[];];
   If[npffile === "", Return@Null];
   If[FileExistsQ@npffile,
      Needs@"SARAH`";
      SARAH`Start@$Model;
      Unprotect@$NPF;
      $NPF = First@Get@npffile;
      Protect@$NPF;
      name /@  MapAt[eField, processRules[], {All, 2}];,
      Print[npffile, " doesn't exist."];
      restore[];
      Abort[];];];
initialize // secure;

gIntegral[full:int_[s_, __], {num_}] :=
   Rule[full, intName[int, s]<>"^{("<>ToString@num<>")}"];
gIntegral // secure;

intName[int_Symbol, s_Symbol] :=
   StringTake[SymbolName@int, {-3}]<>"_{"<>StringDrop[SymbolName@s, 2]<>"}";
intName // secure;

gField[SARAH`bar@e_] := SARAH`bar@gField@e;
gField[Susyno`LieGroups`conj@e_] := Susyno`LieGroups`conj@gField@e;
gField[g_@_@i_Integer] :=
   StringTake[SymbolName@g, -1] <> "_{" <> ToString@i <> "}";
gField[e_] := e;
gField // secure;

eField[SARAH`bar@e_Symbol@{i__Symbol}] := getLaTeX[e, 2, i];
eField[SARAH`bar@e_Symbol] := getLaTeX[e, 2];
eField[SARAH`bar@s_String] := "\\bar{"<>s<>"}";
eField[e_Symbol@{i__Symbol}] := getLaTeX[e, 1, i];
eField[e_Symbol] := getLaTeX[e, 1];
eField[Susyno`LieGroups`conj@e_] := "{" <> eField@e <> "}^{*}";
eField[s_String] := s;
eField // secure;

getLaTeX::usage =
"@brief Return LaTeX form of a given particle";
getLaTeX[e_Symbol, pos:1|2, i_Symbol:Null, c_Symbol:Null] :=
Module[{latex},
   latex = SARAH`LaTeX /. #[[Position[#, e][[1, 1]], 2]] &@
      SARAH`ParticleDefinitions[SARAH`EWSB];
   Switch[latex,
      _List, latex[[pos]],
      _, If[pos==2,"\\bar{"<>latex<>"}", latex]] <>
      If[i=!=Null, "_{" <> index@i <> If[c=!=Null, index@c,""] <> "}", ""]];
getLaTeX // secure;

gTable[fields_, subst_] :=
Module[{table},
   table = Prepend[eField/@#&/@subst, gField/@fields];
   table = Transpose@table;
   "\\begin{equation}\\begin{array}{l|" <>
      StringRepeat["l", Length@table[[1]] - 1] <> "}\n" <>
   StringRiffle[StringRiffle[#, " & "] & /@ table, " \\\\ \n"] <> "\n" <>
   "\\end{array}\\end{equation}"];
gTable // secure;

Module[{cache, type, i=0},
   index[Plus[i_Integer, s_Symbol]] := index@i <>"+"<>index@s;
   index[i_Integer] := ToString@i;
   index[s_Symbol] := cache@s;
   cache[s_Symbol] := cache@s =
   Module[{color={"red", "green", "blue", "magenta"}},
      type = StringCases[SymbolName@s, LetterCharacter];
      Switch[type,
         {"l", _},
            "{\\color{brown}l_{",
         {"g", _},
            "{\\color{"<>color[[Mod[i++, Length@color]+1]]<>"}g_{",
         {"c", _},
            "{\\color{gray}c_{",
         {"j"},
            "{\\color{gray}i_{"] <> StringDrop[SymbolName@s,
               Length@type]<>"}}"];];
index // secure;

gCoupling[all : SARAH`Cp[fields__][mod_]] :=
 all -> "g_{["<>eField@*gField/@{fields}<>"]}"<>
   Switch[mod, SARAH`PL, "^{L}", SARAH`PR, "^{R}", _, ""];
gCoupling // secure;

processRules[] := MapIndexed[#2[[1]] -> #1&, Join@@First@$NPF];
processRules // secure;

matchRules[basis:{Rule[_, _]..}] :=
Module[{res},
   res = Extract[$NPF, Position[$NPF, #[[2]]] /. {e__, 2} :> {e, 1}];
   If[res =!= {},
      NPointFunctions`Mat@res[[1]] -> #[[1]],
      ##&[]]] &/@ basis;
matchRules // secure;

clean[expr_] :=
expr /.
   {  SARAH`sum[__] -> 0,
      LoopTools`B0i[i_, _, mm__] :> LoopTools`B0i[i, 0, mm],
      LoopTools`C0i[i_, Repeated[_, {3}], mm__] :>
         LoopTools`C0i[i, Sequence@@Array[0&, 3], mm],
      LoopTools`D0i[i_, Repeated[_, {6}], mm__] :>
         LoopTools`D0i[i, Sequence@@Array[0&, 6], mm]};
clean // secure;

dress[_[Straight, l_, None]@args__] := implDress["plain", l, args];
dress[_[Straight, l_, Forward]@args__] := implDress["fermion", l, args];
dress[_[Straight, l_, Backward][v1_, v2_, c_, s_, d_]] :=
  implDress["fermion", l, v2, v1, c, s, d];
dress[_[ScalarDash, l_, _]@args__] := implDress["dashes", l, args];
dress[_[Sine, l_, _]@args__] := implDress["boson", l, args];
dress // secure;

implDress[t_, l_, v1_, v2_, c_, s_, depth_] :=
StringReplace["\\fmf{@t,label=$@l$,@clabel.side=@s,tension=@d}{@1,@2}",
   {  "@1" -> v1, "@2" -> v2, "@t" -> t, "@l" -> l,
      "@s" -> Switch[s, 1., "right", _, "left"],
      "@c" -> Switch[Sign@c, -1, "left,", +1, "right,", _, ""],
      "@d" -> ToString@If[depth > Length@$Particles, 2-Abs@Sign@c, 3]}];
implDress // secure;

numberLines[prop:PropagatorGraphics[_, label_, _][__], {num_}] :=
Append[
   If[FreeQ[label, _String],
      prop /. label -> ComposedChar[SymbolName@label, ToString@num],
      prop],
   num];
numberLines // secure;

ComposedChar[sym_, bot_, top_: "", above_: ""] :=
   sym<>"_{"<>bot<>"}"<>If[#!="", "^{"<>#<>"}", #]&@top;
ComposedChar // secure;

texify[Graphics, num:_Integer] :=
Module[{diagram, props, names, i, l, r, v},
   diagram = $Diagrams[[num]];
   props = MapIndexed[numberLines, Cases[diagram, PropagatorGraphics[__]@__]];
   l = Cases[props[[All, {1, 2}]], {0., _}, Infinity];
   r = Cases[props[[All, {1, 2}]], {20, _}, Infinity];
   i = Cases[diagram, VertexGraphics[0][v_] :> v];
   v = MapIndexed[#1 -> "v" <> ToString@#2[[1]] &, Join[l, r, i]];
   StringReplace[
   "{\\centering
   \\begin{fmffile}{"<>ToString@Unique@$Name<>"}
   \\unitlength = 1mm
   \\fmfframe(0,3)(4,3){
    \\begin{fmfgraph*}(30, 30)
    \\fmfpen{0.7}\\fmfstraight\\fmfset{arrow_len}{2.5mm}
    \\fmfleft{@left@}\\fmfright{@right@}
    @props@
    \\end{fmfgraph*}}\\end{fmffile}\\par}",
    {  "@left@" -> StringJoin@Reverse@Riffle[l /. v, ","],
       "@right@" -> StringJoin@Reverse@Riffle[r /. v, ","],
       "@props@" -> StringJoin@Riffle[dress /@ (props /. v /. $Particles), "\n    "]}]];
texify[e:{__}] :=
   "\\begin{equation}\n" <>
   "\\begin{aligned}\n" <>
   StringReplace[
      StringJoin[StringJoin /@ Riffle[e, ",\\\\\n"]] <> ".\n",
      "+-" -> "-"] <>
   "\\end{aligned}\n" <>
   "\\end{equation}";
texify[num_, basis_] :=
Module[{all, res},
   all = raw[basis, num];
   res = "\\begin{minipage}[c]{0.2\\textwidth}\n" <>
      texify[Graphics, num] <>
      "\\end{minipage}\n\\hfill\n" <>
      "\\begin{minipage}[c]{0.79\\textwidth}\n" <>
      (Table /. all) <> "\n\n" <>
      (Integrate /. all) <> "\n" <>
      "\\end{minipage}\n" <>
      (Sum /. all) <> "\n" <>
      "\\par\\noindent\\rule{\\textwidth}{0.4pt}" <> "\n" <>
      StringJoin@Riffle[Replace /. all, "\n\n"]];
texify // secure;

texSum::usage = "
@note The basis names can contain minus sign.";
texSum[sum_, int_, coupl_, b_] :=
Module[{name, factor = 1, coeff, i, c},
   If[MatchQ[#[[2]], _Times],
      name = -#[[2]]; factor = -1,
      name = #[[2]]];
   coeff = Simplify@Coefficient[$Factor*factor*sum, #[[1]]];
   i = MapIndexed[gIntegral, int];
   c = gCoupling /@ coupl;
   If[coeff === 0,
      ##&[],
      makePlain@{name, "&=", coeff /. i /. c //. $texRules}]] &/@ matchRules@b;
texSum // secure;

texIntegrate[int_] :=
Module[{lhs, rhs, RHS},
   lhs = int /. MapIndexed[gIntegral, int];
   RHS[i_[s_, args__]] := StringJoin[intName[i, s], "(",
      Sequence@@Riffle[ToString /@ {args}, ","], ")"];
   rhs = RHS /@ (int //. $texRules);
   MapThread[{#1, "&=", #2}&, {lhs, rhs}]];
texIntegrate // secure;

Module[{pos, cache},
   parseSymbol[s_Symbol] := cache@s;
   cache[s_] := cache@s =
   (  pos = Cases[Position[SARAH`ParameterDefinitions, s], {e_, 1} :> e];
      If[pos === {}, Return@s];
      SARAH`LaTeX /. SARAH`ParameterDefinitions[[pos[[1]], 2]]);
   parseSymbol // secure;];

Module[{pos, h, cache},
   parseMatrix[expr:head_Symbol[i1_, i2_]] := cache@expr;
   cache[expr:head_[i1_, i2_]] := cache@expr =
   (  pos = Cases[Position[SARAH`ParameterDefinitions, head], {e_, 1} :> e];
      If[pos === {}, Return@expr];
      h = SARAH`LaTeX /. SARAH`ParameterDefinitions[[pos[[1]], 2]];
      "{" <> h <> "}_{" <> index@i1 <> "," <> index@i2 <> "}");
   parseMatrix // secure;];

stripField[] := f_[{_Symbol}] :> f;

Module[{v},
   v[SARAH`PR, fields__] := v[SARAH`PR, fields] =
      {eField /@ #[[1]], #[[3, 1]]} &@ SARAH`Vertex[{fields}];
   v[t : 1 | SARAH`PL | _Plus, fields__] :=  v[t, fields] =
      {eField /@ #[[1]], #[[2, 1]]} &@ SARAH`Vertex[{fields}];
   vertex[SARAH`Cp[f__][t_]] := v[t, f][[2]];
   rCoupl[coupl_, fields : {__}, repl : {{__} ..}] :=
      rCoupl[coupl, MapThread[Rule, {fields, #}]] & /@ repl;
   rCoupl[coupl_, rules_] :=
   Module[{CP, res, matrix, gen, patt, tostr},
      patt = _Symbol | _Integer | Plus[_Symbol, _Integer];
      tostr[e_] := ToString /@ makePlain[e //. $texRules];
      gen = coupl /. gCoupling /@ coupl;
      res = coupl /. rules /. stripField[] /. SARAH`Cp[f__][t_] :> v[t, f];
      res = res //. SARAH`sum[__, e_] :> e;
      res = res /. all : _Symbol[patt, patt] :> parseMatrix@all;
      res = res /. s_Symbol :> parseSymbol@s;
      res = res /. Susyno`LieGroups`conj[e_String] :> e <> "^*";
      res = MapThread[
         divideString@StringJoin[#1, "&\\to ", "g_{[", StringJoin@#2, "]}=",
            Sequence@tostr@#3]&, {gen, res[[All, 1]], res[[All, 2]]}];
      texify@StringReplace[res, "+-" -> "-"]<>"\n"<>
      "\\par\\noindent\\rule{\\textwidth}{0.4pt}"];
   rCoupl // secure;];

divideString[str_String] :=
Module[{count = 0, level = 0, depth = 0, bracket = {"\\Big", "\\big"}},
   nl[sym:"+"|"-"] :=
      If[level == 0 && count > $stringLength, count = 0; "\\\\\n&" <> sym, sym];
   nl[sym:"("] := If[depth <= Length@bracket, bracket[[depth]], ""]<>sym;
   nl[sym:")"] := If[depth <= Length@bracket-1, bracket[[depth+1]], ""]<>sym;
   nl[sym_] := sym;
   StringReplace[str, x_ :>
      (  Switch[x,
            "{", level++,
            "}", level--,
            "^", Null,
            "_", Null,
            _, count++];
         Switch[x,
            "(", If[level == 0, depth++],
            ")", If[level == 0, depth--]];
         nl@x)]];
divideString // secure;

raw[basis_, i_] :=
Module[{sum, int, coupl, mass, fields, subst, temp = {}, rule},
   sum = clean@$NPF[[2, 1, 1, i, 1, 1]];
   fields = First /@ $NPF[[2, 1, 1, i, 2]];
   int = DeleteDuplicates@Cases[sum,
      (LoopTools`B0i | LoopTools`C0i | LoopTools`D0i)@__, Infinity];
   coupl = DeleteDuplicates@Cases[sum, SARAH`Cp[__][_], Infinity, Heads -> True];
   subst = $NPF[[2, 1, 2, i]];
   mass = DeleteDuplicates@Cases[sum,
      HoldPattern@SARAH`Mass[_], Infinity, Heads -> True];
   Do[rule = MapThread[Rule, {fields, subst[[el]]}];
      If[(sum /. rule /. v : SARAH`Cp[__][_] :> vertex@v) =!= 0,
         AppendTo[temp, subst[[el]]];];,
      {el, Length@subst}];
   If[temp === {},
      Return[{Sum -> "", Integrate -> "", Replace -> {""}, Table -> ""}]];
   {  Sum -> texify@texSum[sum, int, coupl, basis],
      Integrate -> texify@texIntegrate@int,
      Replace -> rCoupl[coupl, fields, temp],
      Table -> gTable[fields, temp]}];
raw // secure;

End[];
EndPackage[];
$ContextPath = DeleteCases[$ContextPath, "npftex`"];
