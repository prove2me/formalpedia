-- Prove2me | Definitions.Def_OAICatalanBarrierPolynomials
-- name    : OAICatalanBarrierPolynomials
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-07T20:43:49.193263+00:00
-- url     : https://prove2.me/theorems/de369dbe-f2f7-4f38-be6a-96567f8db6e6
-- title:
--   OpenAI's Catalan barrier polynomials — the derivative numerator A_X of X₂ and its explicit form
-- statement:
--   Two further definitions behind OpenAI's proof that Catalan's constant is irrational, from OpenAI's Lean development `lean/OAI/NumberTheory/Catalan` (github.com/openai/math, Apache License 2.0), carved out without change; they extend the bundle `OAICatalanIrrationality` and are needed to state the root-exhaustion step for the barrier function $X_2$.
--
--   **The derivative numerator** (paper, §7.2, Eq. (92)–(93)). The derivative of the case-$\kappa=2$ barrier function $X_2$ is a sum of rational functions: the terms $\frac{19}{48x}$, $-\frac{1}{12(1-x)}$, $-\frac{65}{24}\frac{x}{1+x^2}$, the polynomial derivatives of the finite parts of the trial sequences, and one term $\frac{A_z(x)}{Q_z(x)}$ for each exponential tail term of $p$ (Chebyshev kind, denominators $1-2xz+z^2$) and of $v$ (power kind, denominators $1-xz$), real bases and conjugate pairs combined into real quadratics. `barrierCase2XFractions` is this list of numerator–denominator pairs in $\mathbb Q[x]$, and `barrierCase2AX` $=$ `barrierFractionNumerator barrierCase2XFractions` is the numerator of their sum over the product of all denominators (for a list $(a_1,q_1),\dots,(a_m,q_m)$: $\sum_i a_i\prod_{j\ne i}q_j$, built recursively). This is the polynomial $A_X=Q_X X_2'$ of Eq. (93), up to the normalization of $Q_X$.
--
--   **The explicit form.** `barrierCase2AXExplicit` is a polynomial with $37$ explicit rational coefficients (degree $36$, matching $d_0=36$ in the root table on p. 37).
--
--   The remaining declarations (`barrierLinearFractions`, `barrierQuadraticFractions`, `barrierPairLinearA`, …, `barrierP2PairRows`, `barrierV2RealRows`, the structure `BarrierRationalPairRow` of four rationals) encode the trial-sequence tails of §7.1 as rational data for these fractions.
--
--   **Source and credit.** OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math), [paper](https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf); Lean in `lean/OAI/NumberTheory/Catalan`, Apache License 2.0. The code of this bundle is OpenAI's, with comments removed.
--
--   **Formalization note.** The declarations live in OpenAI's namespace `OAI.InternalCatalan` under their own names.
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), §7.2 Eq. (92)-(93) pp. 36-37 (the derivative numerator A_X of the case-two barrier function X_2); the definitions are OpenAI's Lean definitions, carved from the development

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAICatalanIrrationality

/-!
# Catalan's constant is irrational: the barrier polynomials

OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026,
https://github.com/openai/math (paper:
`preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf`).

The definitions below are taken from OpenAI's Lean development `lean/OAI/NumberTheory/Catalan`
in that repository (Apache License, Version 2.0), with comments removed and line-level edits for
this Lean and Mathlib version. They are the declarations needed to state the published lemmas
of the proof.
-/

section

namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial

def barrierFractionProduct (fs : List (ℚ[X] × ℚ[X])) : ℚ[X] :=
  (fs.map Prod.snd).prod

def barrierFractionNumerator : List (ℚ[X] × ℚ[X]) → ℚ[X]
  | [] => 0
  | aq :: fs => aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierTailQuadraticDen (z : ℂ) (x : ℝ) : ℂ :=
  1 - 2 * (x : ℂ) * z + z ^ 2

open Polynomial

def barrierPairLinearQ (a b : ℚ) : ℚ[X] :=
  (1 - C a * X) ^ 2 + (C b * X) ^ 2

def barrierPairLinearA (a b c d : ℚ) : ℚ[X] :=
  2 * (C (c * a - d * b) * (1 - C a * X) - C (c * b + d * a) * C b * X)

def barrierPairQuadraticQ (a b : ℚ) : ℚ[X] :=
  (1 - 2 * C a * X + C (a ^ 2 - b ^ 2)) ^ 2 +
    (2 * C b * (C a - X)) ^ 2

def barrierPairQuadraticA (a b c d : ℚ) : ℚ[X] :=
  2 * (C (c * a - d * b) * (1 - 2 * C a * X + C (a ^ 2 - b ^ 2)) +
    C (c * b + d * a) * (2 * C b * (C a - X)))

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

def barrierFiniteUDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * Chebyshev.U ℚ (k : ℤ)

def barrierFinitePowerDerivative (cs : List ℤ) : ℚ[X] :=
  ∑ k ∈ Finset.range cs.length,
    C ((cs.getD k 0 : ℚ) / 100000000) * X ^ k

end

section

open Polynomial

end

section

open Polynomial
open scoped BigOperators

end

open Polynomial

open Polynomial

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

structure BarrierRationalPairRow where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

def barrierP2RealRows : List (ℚ × ℚ) :=
  [(85 / 100, -9338452 / 100000000), (94 / 100, -2141509 / 100000000)]

def barrierP2PairRows : List BarrierRationalPairRow :=
  [⟨0, 7 / 10, -66277922 / 200000000, 31907569 / 200000000⟩,
   ⟨0, 85 / 100, -1231651 / 200000000, -6002645 / 200000000⟩,
   ⟨92 / 1000, 92 / 100, -3225918 / 200000000, -8928234 / 200000000⟩,
   ⟨-92 / 1000, 92 / 100, -2105536 / 200000000, 9091287 / 200000000⟩]

def barrierV2RealRows : List (ℚ × ℚ) :=
  [(-8 / 10, 15199211 / 100000000), (-96 / 100, 4451662 / 100000000),
   (88 / 100, 2545398 / 100000000), (95 / 100, -4932634 / 100000000),
   (984 / 1000, 11618157 / 100000000)]

def barrierV2PairRows : List BarrierRationalPairRow :=
  [⟨0, 78 / 100, 27238714 / 200000000, 38447936 / 200000000⟩,
   ⟨0, 9 / 10, -31341084 / 200000000, 30188786 / 200000000⟩,
   ⟨0, 955 / 1000, -6693542 / 200000000, -11912254 / 200000000⟩,
   ⟨0, 984 / 1000, 2055213 / 200000000, 21715849 / 200000000⟩]

open Polynomial

def barrierRealLinearQ (a : ℚ) : ℚ[X] := 1 - C a * X

def barrierRealQuadraticQ (a : ℚ) : ℚ[X] := 1 - 2 * C a * X + C (a ^ 2)

open Polynomial

def barrierLinearFractions (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : List (ℚ[X] × ℚ[X]) :=
  rs.map (fun ac : ℚ × ℚ => (C (ac.2 * ac.1), barrierRealLinearQ ac.1)) ++
    ps.map (fun row : BarrierRationalPairRow =>
      (barrierPairLinearA row.a row.b row.c row.d, barrierPairLinearQ row.a row.b))

def barrierQuadraticFractions (rs : List (ℚ × ℚ))
    (ps : List BarrierRationalPairRow) : List (ℚ[X] × ℚ[X]) :=
  rs.map (fun ac : ℚ × ℚ => (C (ac.2 * ac.1), barrierRealQuadraticQ ac.1)) ++
    ps.map (fun row : BarrierRationalPairRow =>
      (barrierPairQuadraticA row.a row.b row.c row.d, barrierPairQuadraticQ row.a row.b))

def barrierScaleFractions (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) : List (ℚ[X] × ℚ[X]) :=
  fs.map (fun aq : ℚ[X] × ℚ[X] => (C c * aq.1, aq.2))

def barrierCase2XFractions : List (ℚ[X] × ℚ[X]) :=
  [(C (19 / 48), X), (-C (1 / 12), 1 - X), (-C (65 / 24) * X, 1 + X ^ 2),
   (-(C 4 * barrierFiniteUDerivative barrierP2Finite +
       barrierFinitePowerDerivative barrierV2Finite), 1)] ++
  barrierScaleFractions (-4) (barrierQuadraticFractions barrierP2RealRows barrierP2PairRows) ++
  barrierScaleFractions (-1) (barrierLinearFractions barrierV2RealRows barrierV2PairRows)

def barrierCase2AX : ℚ[X] := barrierFractionNumerator barrierCase2XFractions

def barrierCase2AXExplicit : ℚ[X] :=
  C (30307837230416268959058568549773/390625000000000000000000000000000000) +
  C (-388916241323180816905894669551174674670591/1220703125000000000000000000000000000000000000) * X ^ 1 +
  C (-4006784573305776602421578075882271527736951993/1220703125000000000000000000000000000000000000000) * X ^ 2 +
  C (1096183954671168725038063556149715387207630523987/61035156250000000000000000000000000000000000000000) * X ^ 3 +
  C (-7952498478159654485025286927264757800766806449689461/91552734375000000000000000000000000000000000000000000) * X ^ 4 +
  C (-173251421552630457395123417783409511688090895941195417/4577636718750000000000000000000000000000000000000000000) * X ^ 5 +
  C (1222120559292925857030215856817101460328272419116765158471/228881835937500000000000000000000000000000000000000000000) * X ^ 6 +
  C (-9002153638868141433199303807358329862172831171827356580769/762939453125000000000000000000000000000000000000000000000) * X ^ 7 +
  C (-20430716055979141452221343027896515893162803128568450962685989/286102294921875000000000000000000000000000000000000000000000) * X ^ 8 +
  C (1551532006333267422675951782124692841597537382079615796002800463/7152557373046875000000000000000000000000000000000000000000000) * X ^ 9 +
  C (3430606054133072949419772876756861170914507767290711053103959413/11920928955078125000000000000000000000000000000000000000000000) * X ^ 10 +
  C (-505916145739811163969788025388361352785579438858951141108745471259/357627868652343750000000000000000000000000000000000000000000000) * X ^ 11 +
  C (170660418192088844983109244182859397071662139279111654553014694589/357627868652343750000000000000000000000000000000000000000000000) * X ^ 12 +
  C (111802796781702066809285191673959138398105580484717994246462464509/37252902984619140625000000000000000000000000000000000000000000) * X ^ 13 +
  C (-45027051395514975383376671261049412207657650433594188527438870439467/8940696716308593750000000000000000000000000000000000000000000000) * X ^ 14 +
  C (16509003686870615770955343186283294035863361608791696629553878592691/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 15 +
  C (39466767544097375649642054097024548875637201165892323429352340271739/8940696716308593750000000000000000000000000000000000000000000000) * X ^ 16 +
  C (-26755287098024999828824584679516056137747845043276649132658782483257/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 17 +
  C (168070108726307711595570993536980340222190659762943286668833668339249/8940696716308593750000000000000000000000000000000000000000000000) * X ^ 18 +
  C (-832051437619875563928237488265539747452368600303675116627132838151/596046447753906250000000000000000000000000000000000000000000000) * X ^ 19 +
  C (-1606955218748669940170405173174994300085549469536010604897519048427/74505805969238281250000000000000000000000000000000000000000000) * X ^ 20 +
  C (2433137840814792444702356102800877012295375212980653188941121382049/59604644775390625000000000000000000000000000000000000000000000) * X ^ 21 +
  C (-51739167878202129506248629638529892446087925833524235401379411247437/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 22 +
  C (-1082632152122822888597045006113490327710626764705887378288008787721/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 23 +
  C (4986802693523860777269281537299839923932961413477019773621637642489/149011611938476562500000000000000000000000000000000000000000000) * X ^ 24 +
  C (-4416319363306657399702427900939605066393368736600070485184725132417/93132257461547851562500000000000000000000000000000000000000000) * X ^ 25 +
  C (430725170281186155782445052791711482276044238852484890595621567703/11641532182693481445312500000000000000000000000000000000000000) * X ^ 26 +
  C (-5858283778532255307754122045950281887663478271777393285415699291/1164153218269348144531250000000000000000000000000000000000000) * X ^ 27 +
  C (-9526115897201306594135430784633925777531015543666247018754883/465661287307739257812500000000000000000000000000000000000) * X ^ 28 +
  C (627455201464947631518402076531001458986822444066613529731827/23283064365386962890625000000000000000000000000000000000) * X ^ 29 +
  C (-1505504840851826080906317395924633616756101528774509886831583/72759576141834259033203125000000000000000000000000000000) * X ^ 30 +
  C (6417086791213399557054520364584799762086047849866994798447/909494701772928237915039062500000000000000000000000000) * X ^ 31 +
  C (463404787046380243295539802625032027305554181181839276149/145519152283668518066406250000000000000000000000000000) * X ^ 32 +
  C (-79635932674577498395062383173973277954089807724779169/14551915228366851806640625000000000000000000000000) * X ^ 33 +
  C (306952565700894986183323747480996064114191827407661/72759576141834259033203125000000000000000000000) * X ^ 34 +
  C (-29493660039437141081639612350479227384504308233/14551915228366851806640625000000000000000000) * X ^ 35 +
  C (60188546402546646873910140358666064623915029/145519152283668518066406250000000000000000) * X ^ 36

end InternalCatalan

end

end OAI

end


