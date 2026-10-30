-- Prove2me | Definitions.Def_OAIQ117R002
-- name    : OAIQ117R002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:07:57.400364+00:00
-- url     : https://prove2.me/theorems/453919b2-c6b8-4901-94f6-7e14daef7e79
-- title:
--   Definitions bundle OAIQ117R002 of the split of OpenAI, Randomized quasipolynomial-time mean-payoff games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.randomized_quasipolynomial_mean_payoff`, carved from OpenAI's openai/math development (OpenAI, *Randomized quasipolynomial-time mean-payoff games*, OpenAI Math Release, September 25, 2026, result family 104, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 787 declarations of OpenAI's Lean: 452 definitions, 15 inductive types or structures and 320 theorems. The definitions and types are `OAI.MeanPayoff.FairBits.acc`, `OAI.MeanPayoff.FairBits.draw`, `OAI.MeanPayoff.HighBad`, `OAI.MeanPayoff.HighStep`, `OAI.MeanPayoff.LowAlternative`, `OAI.MeanPayoff.LowBad`, `OAI.MeanPayoff.LowStep`, `OAI.MeanPayoff.LowerComparisons`, `OAI.MeanPayoff.RandomTable.cfg`, `OAI.MeanPayoff.RandomTable.edge`, `OAI.MeanPayoff.RandomTable.flow`, `OAI.MeanPayoff.RandomTable.program`, `OAI.MeanPayoff.RandomTree.Path`, `OAI.MeanPayoff.RandomTree.traverse`, `OAI.MeanPayoff.RandomTree.trials`, `OAI.MeanPayoff.Realizer.amount`, `OAI.MeanPayoff.Realizer.answer`, `OAI.MeanPayoff.Realizer.aux`, `OAI.MeanPayoff.Realizer.iterations`, `OAI.MeanPayoff.Realizer.limit`, `OAI.MeanPayoff.Realizer.post`, `OAI.MeanPayoff.Realizer.postBudget`, `OAI.MeanPayoff.Realizer.postCost`, `OAI.MeanPayoff.Realizer.pre`, `OAI.MeanPayoff.Realizer.preCost`, `OAI.MeanPayoff.Realizer.preTail`, `OAI.MeanPayoff.Realizer.program`, `OAI.MeanPayoff.Realizer.total`, `OAI.MeanPayoff.RegisterBits.Compile.bound`, `OAI.MeanPayoff.RegisterBits.Compile.clock`, `OAI.MeanPayoff.RegisterBits.Compile.embed`, `OAI.MeanPayoff.RegisterBits.Compile.initializedTree`, `OAI.MeanPayoff.RegisterBits.Compile.localDest`, `OAI.MeanPayoff.RegisterBits.Compile.localEmit`, `OAI.MeanPayoff.RegisterBits.Compile.localOp`, `OAI.MeanPayoff.RegisterBits.Compile.machine`, `OAI.MeanPayoff.RegisterBits.Compile.schedule`, `OAI.MeanPayoff.RegisterBits.Sequence5.flow`, `OAI.MeanPayoff.RegisterBits.Sequence5.program`, `OAI.MeanPayoff.RegisterBits.Traces` and 427 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MeanPayoff_Allocation`, `MeanPayoff_Alternatives`, `MeanPayoff_ArenaParsing`, `MeanPayoff_ArithmeticBounds`, `MeanPayoff_BatchDevices`, `MeanPayoff_BitDepth`, `MeanPayoff_Budgets`, `MeanPayoff_CountedTraversal`, `MeanPayoff_Counters`, `MeanPayoff_Deviation`, `MeanPayoff_Drift`, `MeanPayoff_DriverExecution`, `MeanPayoff_EncodedArithmetic`, `MeanPayoff_ErrorBounds`, `MeanPayoff_FiniteBox`, `MeanPayoff_FiniteIteration`, `MeanPayoff_FiniteTrees`, `MeanPayoff_InputCode`, `MeanPayoff_Instructions`, `MeanPayoff_Normalization`, `MeanPayoff_OperatorCosts`, `MeanPayoff_OperatorDevices`, `MeanPayoff_Orientation`, `MeanPayoff_ParserCosts`, `MeanPayoff_Realizer`, `MeanPayoff_Recursion`, `MeanPayoff_Registers`, `MeanPayoff_RootBox`, `MeanPayoff_Sampling`, `MeanPayoff_SizeBounds`, `MeanPayoff_Sorting`, `MeanPayoff_Stack`, `MeanPayoff_StackSimulation`, `MeanPayoff_Tightening`, `MeanPayoff_Volume`, `MeanPayoff_WordDecoding`, `RandomMean_Allocation`, `RandomMean_Chunks`, `RandomMean_Complexity`, `RandomMean_Control`, `RandomMean_ControlCorrectness`, `RandomMean_DispatchBounds`, `RandomMean_Growth`, `RandomMean_Loop`, `RandomMean_Orientation`, `RandomMean_Preparation`, `RandomMean_RandomTables`, `RandomMean_Realizer`, `RandomMean_SizeBounds`, `RandomMean_StateGrowth`, `RandomMean_Traces`.
--
--   **Imports.** It imports the published bundle `Def_RandomizedMeanPayoff`; the bundles `OAIQ117R000` and `OAIQ117R001` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.MeanPayoff.Realizer.tree_law`; the proofs of `OAI.MeanPayoff.Realizer.tree_law` and `OAI.randomized_quasipolynomial_mean_payoff`.
-- source:
--   OpenAI, Randomized quasipolynomial-time mean-payoff games, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 104; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Randomized-quasipolynomial-time-mean-payoff-games-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_RandomizedMeanPayoff
import Definitions.Def_OAIQ117R000
import Definitions.Def_OAIQ117R001

section
-- module Solutions.OAIQ117_RM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

def subSupport {V : Type} (a y : Vec V) : Set V := {i | a i < y i}
def superSupport {V : Type} (b z : Vec V) : Set V := {i | z i < b i}

section Projections
variable {V : Type} {F : Vec V → Vec V}

def centerSub (y q : Vec V) (d A : ℤ) : Vec V :=
  fun i => max (y i - d + A) (q i - A)

def centerSuper (z q : Vec V) (e A : ℤ) : Vec V :=
  fun i => min (z i + e - A) (q i + A)

end Projections

def averageStep {V : Type} (a b r₁ r₂ : Vec V) : Vec V :=
  clip a b (fun i => (r₁ i + r₂ i) / 2)

def weightBound (G : Game) : ℤ :=
  max 1 ((Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) : ℕ) : ℤ)

def topWidth (G : Game) : ℤ := 8 * G.n * weightBound G

theorem weightBound_positive (G : Game) : 0 < weightBound G := by
  have := le_max_left (1 : ℤ) ((Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) : ℕ) : ℤ)
  change 0 < max 1 _
  omega

end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Budgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff

namespace RandomTree

open scoped Classical

def trials {α : Type} (t : RandomTree α) : ℕ → RandomTree (List α)
  | 0 => .leaf []
  | j + 1 => t.bind (fun a => (trials t j).map (fun as => a :: as))

end RandomTree
end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

namespace SolveBox

def repeated {n Bmax : ℕ} (I : SolveBox n Bmax) (t : RandomTree (BoxVector I))
    (J : ℕ) : RandomTree (BoxVector I) := (RandomTree.trials t J).map I.medianBox

end SolveBox

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Recursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def centerUpdate {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) (q : BoxVector I) : RandomTree (BoxVector I) :=
  let K := I.narrowCentered hB q.val
  (K.repeated (lower P.reduceK (P.reduceK_rank hR) K) (globalJ n Bmax)).bind fun r₁ =>
  (K.repeated (lower P.reduceM (P.reduceM_rank hR) K) (globalJ n Bmax)).map fun r₂ =>
    I.averageClipped r₁.val r₂.val

def centerSteps {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) :
    ℕ → BoxVector I → RandomTree (List (BoxVector I))
  | 0, q => .leaf [q]
  | t + 1, q =>
    (centerUpdate P hR lower I hB q).bind fun q' =>
    (centerSteps P hR lower I hB t q').map (q :: ·)

def orientationTail (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (qs : List (BoxVector I)) (child : BoxVector I → RandomTree (Orientation P)) :
    RandomTree (Orientation P) :=
  let H := PositiveDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  let N := NegativeDisplacement I (qs.getD (globalS Bmax) I.midpoint)
  if hH : 1 / 2 < P.measure H then
    .leaf ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else if hN : 1 / 2 < P.measure N then
    .leaf ⟨false, [⟨Nᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩
  else
    (RandomTree.uniformBelow (sampleExponent Bmax)).bind fun j =>
      (child (qs.getD j I.midpoint)).map fun O =>
        ⟨O.chooseY, O.exceptions ++ [⟨H, le_of_not_gt hH⟩, ⟨N, le_of_not_gt hN⟩]⟩

def orient (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) :
    RandomTree (Orientation P) :=
  if hB : I.width ≤ 128 * globalS Bmax then
    .leaf (orientBase G P I)
  else
    let hb : 128 * globalS Bmax < I.width := lt_of_not_ge hB
    (centerSteps P hR lower I hb (globalS Bmax) I.midpoint).bind fun qs =>
      orientationTail G P I qs (fun q => orient G P hR lower (I.wideCentered hb q.val))
termination_by I.width
decreasing_by exact I.E_smaller

def orientPlus {n : ℕ} {P : Budgets n} (t : RandomTree (Orientation P)) (J : ℕ) :
    RandomTree (Orientation P) :=
  (RandomTree.trials t J).map combineOrientations



def tighten {n Bmax : ℕ} (P : Budgets n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox n Bmax)
    (hB : 128 * globalS Bmax < I.width) : RandomTree (InnerBox I) :=
  (I.repeated (lower P.reduceK (P.reduceK_rank hR) I) (globalJ n Bmax)).bind fun r₁ =>
  if _h₁ : ∃ i, (I.delta : ℤ) ≤ r₁.val i - I.a i then
    let K := I.withFloor r₁
    (tighten P hR lower K hB).map fun T =>
      ⟨T.box, T.width_eq, r₁.property.1.trans T.floor_le, T.ceiling_le⟩
  else
    (I.repeated (lower P.reduceM (P.reduceM_rank hR) I) (globalJ n Bmax)).bind fun r₂ =>
    if _h₂ : ∃ i, (I.delta : ℤ) ≤ I.b i - r₂.val i then
      let K := I.withCeiling r₂
      (tighten P hR lower K hB).map fun T =>
        ⟨T.box, T.width_eq, T.floor_le, T.ceiling_le.trans r₂.property.2⟩
    else .leaf ⟨I, rfl, le_refl _, le_refl _⟩
termination_by volume I.b I.a
decreasing_by
  · apply volume_decreases r₁.property.1 r₁.property.2
    obtain ⟨i, hi⟩ := _h₁
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega
  · apply volume_ceiling_decreases r₂.property.1 r₂.property.2
    obtain ⟨i, hi⟩ := _h₂
    have hd := I.delta_positive hB
    intro heq
    have he := congrFun heq i
    omega

namespace RandomTree

def traverse {α β : Type} (f : α → RandomTree β) : List α → RandomTree (List β)
  | [] => .leaf []
  | a :: as => (f a).bind fun b => (traverse f as).map (b :: ·)

end RandomTree

def finishChoice (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax)
    (hB : 128 * globalS Bmax < I.width) (O : Orientation P)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le))) :
    RandomTree (BoxVector I) :=
  if O.chooseY then
    (RandomTree.traverse (fun H : SmallSet P =>
      I.repeated (lower (P.reweightM H.val)
        (P.reweightM_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    up.map fun p => rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le p)
  else
    (RandomTree.traverse (fun H : SmallSet P =>
      I.repeated (lower (P.reweightK H.val)
        (P.reweightK_rank G.positive hR H.property) I) (globalJ G.n Bmax)) O.exceptions).bind fun rs =>
    lo.map fun p => rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le p)

def solveWidth (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (I : SolveBox G.n Bmax) : RandomTree (BoxVector I) :=
  if hB : I.width ≤ 128 * globalS Bmax then .leaf (I.exactVector G)
  else
    (tighten P hR lower I (lt_of_not_ge hB)).bind fun T =>
    let K := T.box
    have hK : 128 * globalS Bmax < K.width := by rw [T.width_eq]; omega
    let c := K.C
    have hc : 0 < c := K.C_positive
    have hcsmall : c < K.width := K.C_smaller hK
    (orientPlus (orient G P hR lower K) (globalJ G.n Bmax)).bind fun O =>
    (finishChoice G P hR lower K hK O
      (solveWidth G P hR lower (K.capHigh c hc hcsmall.le))
      (solveWidth G P hR lower (K.capLow c hc hcsmall.le))).map T.include
termination_by I.width
decreasing_by
  all_goals
    change c < I.width
    rw [← T.width_eq]
    exact hcsmall

def solve (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax) :
    RandomTree (BoxVector I) :=
  if hR : P.parameter < 1 then .leaf (I.smallVector P)
  else solveWidth G P (le_of_not_gt hR) (fun Q _ K => solve G Q K) I
termination_by parameterRank P.parameter

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Deviation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def deviation (G : Game) (y q : Vec (Fin G.n)) : ℤ :=
  Finset.univ.sup' ⟨⟨0, G.positive⟩, Finset.mem_univ _⟩ (fun i => y i - q i)

def highCore {n Bmax : ℕ} (I : SolveBox n Bmax) (y : Vec (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (globalS Bmax : ℤ) * I.width - I.width ≤
    (globalS Bmax : ℤ) * (y i - I.a i))
def lowCore {n Bmax : ℕ} (I : SolveBox n Bmax) (z : Vec (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (globalS Bmax : ℤ) * I.width - I.width ≤
    (globalS Bmax : ℤ) * (I.b i - z i))

def nearHigh (G : Game) (y q : Vec (Fin G.n)) (A : ℕ) : Finset (Fin G.n) :=
  Finset.univ.filter (fun i => deviation G y q - 2 * A < y i - q i)
def nearLow (G : Game) (z q : Vec (Fin G.n)) (A : ℕ) : Finset (Fin G.n) :=
  Finset.univ.filter (fun i => deviation G q z - 2 * A < q i - z i)

def LowerComparisons (G : Game) {Bmax : ℕ} (P : Budgets G.n)
    (lower : LowerSolver (Bmax := Bmax) P) : Prop :=
  ∀ Q hQ, Comparisons G Q (lower Q hQ)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Drift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def epsilon (n Bmax : ℕ) : ℚ := (1 / 2) ^ globalJ n Bmax

def HighStep (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (P : Budgets G.n)
    (y : Vec (Fin G.n)) (q q' : BoxVector I) : Prop :=
  deviation G y q'.val ≤ deviation G y q.val ∧
  (mass P.alpha (nearHigh G y q.val I.D) ≤ (4 / 5) * P.k →
    deviation G y q'.val ≤ deviation G y q.val - I.D)

def LowStep (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (P : Budgets G.n)
    (z : Vec (Fin G.n)) (q q' : BoxVector I) : Prop :=
  deviation G q'.val z ≤ deviation G q.val z ∧
  (mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m →
    deviation G q'.val z ≤ deviation G q.val z - I.D)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Alternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
open scoped Classical

def HighBad (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (P : Budgets G.n)
    (y : Vec (Fin G.n)) (q : BoxVector I) : Prop :=
  mass P.alpha (nearHigh G y q.val I.D) ≤ (4 / 5) * P.k

def LowBad (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (P : Budgets G.n)
    (z : Vec (Fin G.n)) (q : BoxVector I) : Prop :=
  mass P.beta (nearLow G z q.val I.D) ≤ (4 / 5) * P.m

end MeanPayoff

namespace MeanPayoff
open scoped Classical

def LowAlternative {n Bmax : ℕ} (I : SolveBox n Bmax) (P : Budgets n)
    (z : Vec (Fin n)) : Orientation P → Prop :=
  Alternative false P.beta (upperActive I.b z) P.m

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Orientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def orientationError (n Bmax : ℕ) : ℚ :=
  256 / (globalS Bmax : ℚ) + 2 * globalS Bmax * epsilon n Bmax

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Tightening
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
open scoped Classical

def tightSub (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (y : Vec (Fin G.n)) : Vec (Fin G.n) :=
  fun i => max (y i - deviation G y I.a + I.delta) (I.a i)
def tightSuper (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) (z : Vec (Fin G.n)) : Vec (Fin G.n) :=
  fun i => min (z i + deviation G I.b z - I.delta) (I.b i)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Volume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def globalListBound (n Bmax : ℕ) : ℕ := globalJ n Bmax * (2 * globalG Bmax + 3)


open scoped Classical

def TightHigh (G : Game) {Bmax : ℕ} (P : Budgets G.n) {I : SolveBox G.n Bmax}
    (y : Vec (Fin G.n)) (T : InnerBox I) : Prop :=
  ∃ u, y ≤ u ∧ AdmissibleSub (operator G) T.box.a T.box.b u P ∧
    ((T.box.C : ℤ) < deviation G u T.box.a → (4 / 5) * P.k < mass P.alpha (highCore T.box u))

def TightLow (G : Game) {Bmax : ℕ} (P : Budgets G.n) {I : SolveBox G.n Bmax}
    (z : Vec (Fin G.n)) (T : InnerBox I) : Prop :=
  ∃ u, u ≤ z ∧ AdmissibleSuper (operator G) T.box.a T.box.b u P ∧
    ((T.box.C : ℤ) < deviation G T.box.b u → (4 / 5) * P.m < mass P.beta (lowCore T.box u))

def TightHighRequest (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (y : Vec (Fin G.n)) (r : BoxVector I) : Prop :=
  (I.C : ℤ) < deviation G y I.a → mass P.alpha (highCore I y) ≤ (4 / 5) * P.k →
    tightSub G I y ≤ r.val

def TightLowRequest (G : Game) {Bmax : ℕ} (P : Budgets G.n) (I : SolveBox G.n Bmax)
    (z : Vec (Fin G.n)) (r : BoxVector I) : Prop :=
  (I.C : ℤ) < deviation G I.b z → mass P.beta (lowCore I z) ≤ (4 / 5) * P.m →
    r.val ≤ tightSuper G I z

end MeanPayoff

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ErrorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def nodeError (n Bmax : ℕ) : ℚ :=
  (2 * (n : ℚ) * Bmax + globalListBound n Bmax + 3) * epsilon n Bmax

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_CountedTraversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff



def rootBudgets (G : Game) : Budgets G.n where
  alpha := fun _ => 1
  beta := fun _ => 1
  k := G.n
  m := G.n
  alpha_pos := fun _ => by norm_num
  beta_pos := fun _ => by norm_num
  k_pos := by exact_mod_cast G.positive
  m_pos := by exact_mod_cast G.positive

theorem topWidth_positive (G : Game) : 0 < topWidth G := by
  unfold topWidth
  exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast G.positive)) (weightBound_positive G)

def rootBox (G : Game) : SolveBox G.n (topWidth G).toNat where
  a := fun _ => 0
  b := fun _ => topWidth G
  ordered := fun _ => (topWidth_positive G).le
  width := (topWidth G).toNat
  positive := by have h := topWidth_positive G; omega
  bounded := le_rfl
  width_bound := fun _ => by rw [Int.toNat_of_nonneg (topWidth_positive G).le]; omega

def gameSolve (G : Game) : RandomTree (Fin G.n → Bool) :=
  (solve G (rootBudgets G) (rootBox G)).map fun p v => decide (topWidth G / 2 < p.val v)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_RootBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

def auxiliaryCalls (n Bmax : ℕ) : ℕ :=
  (16 * n * globalS Bmax + 2) * globalJ n Bmax +
  globalJ n Bmax * ((globalG Bmax + 1) * (globalS Bmax * (2 * globalJ n Bmax))) +
  globalListBound n Bmax * globalJ n Bmax

def chainBound (Bmax : ℕ) : ℕ := 8 * globalS Bmax * (Nat.log 2 Bmax + 2) + 1

def callBase (n Bmax : ℕ) : ℕ := chainBound Bmax * (auxiliaryCalls n Bmax + 1) + 1

def callBound (n Bmax d : ℕ) : ℕ := callBase n Bmax ^ (d + 1)

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BitDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff

noncomputable def rootInvocationBound (G : Game) : ℕ :=
  callBound G.n (topWidth G).toNat (parameterRank (rootBudgets G).parameter)


namespace RandomTree

inductive Path {α : Type} : RandomTree α → α → ℕ → Prop
  | leaf (a) : Path (.leaf a) a 0
  | left {l r a d} : Path l a d → Path (.coin l r) a (d + 1)
  | right {l r a d} : Path r a d → Path (.coin l r) a (d + 1)

end RandomTree

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Registers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits.Compile
open BinaryStack (advance)

theorem advance_add (P : BinaryStack.Program) (bits : ℕ → Bool)
    (c : BinaryStack.Config P) (a b : ℕ) :
    _root_.OAI.MeanPayoff.BinaryStack.advance P bits c (a + b) =
      _root_.OAI.MeanPayoff.BinaryStack.advance P (fun j => bits (a + j)) (_root_.OAI.MeanPayoff.BinaryStack.advance P bits c a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change BinaryStack.step P (_root_.OAI.MeanPayoff.BinaryStack.advance P bits c (a + b)) (bits (a + b)) = _
    rw [ih]
    rfl

theorem seek_one {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool)
    (left : Fin (K + 1)) (h : left.val ≠ 0) (xs tail ys out : List Bool) (bits : ℕ → Bool) :
    _root_.OAI.MeanPayoff.BinaryStack.advance (program P) bits (cfg P (.seek q coin left) (encode xs ++ tail) ys out)
        (encode xs).length =
      cfg P (.seek q coin ⟨left.val - 1, by omega⟩) tail ((encode xs).reverse ++ ys) out := by
  induction xs generalizing ys bits with
  | nil => simpa only [encode, List.singleton_append, List.length_singleton, _root_.OAI.MeanPayoff.BinaryStack.advance,
      List.reverse_singleton] using step_seek_delim P q coin (bits 0) left h tail ys out
  | cons b xs ih =>
    simp only [encode, List.cons_append, List.length_cons]
    rw [BinaryStack.advance_front, step_seek_tag P q coin _ left h,
      BinaryStack.advance_front, step_skip]
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

theorem seek_prefix {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool)
    (prefx : List (List Bool)) (hp : prefx.length ≤ K) (tail ys out : List Bool)
    (bits : ℕ → Bool) :
    _root_.OAI.MeanPayoff.BinaryStack.advance (program P) bits
      (cfg P (.seek q coin ⟨prefx.length, by omega⟩) (encodeAll prefx ++ tail) ys out)
      (encodeAll prefx).length =
      cfg P (.seek q coin 0) tail ((encodeAll prefx).reverse ++ ys) out := by
  induction prefx generalizing ys bits with
  | nil => simp [encodeAll, _root_.OAI.MeanPayoff.BinaryStack.advance]
  | cons xs pref ih =>
    simp only [List.length_cons, encodeAll, List.length_append]
    rw [List.append_assoc, advance_add, seek_one P q coin _ (by simp)]
    simp only [List.length_cons] at hp
    have he : (⟨pref.length + 1 - 1, by omega⟩ : Fin (K + 1)) =
        ⟨pref.length, by omega⟩ := by
      apply Fin.ext; simp
    rw [he, ih (by omega)]
    simp [List.reverse_append, List.append_assoc]

theorem restore_all {K : ℕ} (P : Program K) (dest : Option (Fin P.states))
    (xs ys out : List Bool) (bits : ℕ → Bool) :
    _root_.OAI.MeanPayoff.BinaryStack.advance (program P) bits (cfg P (.restore dest) xs ys out) (ys.length + 1) =
      sourceCfg P dest (ys.reverse ++ xs) [] out := by
  induction ys generalizing xs bits with
  | nil => simp [_root_.OAI.MeanPayoff.BinaryStack.advance]
  | cons b ys ih =>
    rw [List.length_cons, BinaryStack.advance_front, step_restore_some, ih]
    simp [List.reverse_cons, List.append_assoc]

end MeanPayoff.RegisterBits.Compile

namespace MeanPayoff.RegisterBits.Compile
open BinaryStack (advance applyOp)

def localOp {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool) (xs : List Bool) :=
  ((P.transition q xs.head? coin).map Act.work).getD .keep

def localDest {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool) (xs : List Bool) :=
  (P.transition q xs.head? coin).map Act.next

def localEmit {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool) (xs : List Bool) :=
  (P.transition q xs.head? coin).bind Act.emit

theorem local_update {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool)
    (xs tail ys out : List Bool) :
    ∃ n, 1 ≤ n ∧ n ≤ 4 ∧ ∀ bits : ℕ → Bool,
      _root_.OAI.MeanPayoff.BinaryStack.advance (program P) bits (cfg P (.seek q coin 0) (encode xs ++ tail) ys out) n =
        cfg P (.restore (localDest P q coin xs))
          (encode (applyOp (localOp P q coin xs) xs) ++ tail) ys
          (out ++ (localEmit P q coin xs).toList) := by
  cases xs with
  | nil =>
    cases he : P.transition q none coin with
    | none =>
      refine ⟨1, by omega, by omega, ?_⟩
      intro bits
      apply BinaryStack.Config.ext
      all_goals first
        | solve | simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
        | solve | funext i; fin_cases i <;> simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
    | some a =>
      obtain ⟨dest, op, emit⟩ := a
      cases op with
      | keep =>
        refine ⟨1, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
      | pop =>
        refine ⟨1, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
      | push b =>
        refine ⟨2, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
  | cons b xs =>
    cases he : P.transition q (some b) coin with
    | none =>
      refine ⟨2, by omega, by omega, ?_⟩
      intro bits
      apply BinaryStack.Config.ext
      all_goals first
        | solve | simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
        | solve | funext i; fin_cases i <;> simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
    | some a =>
      obtain ⟨dest, op, emit⟩ := a
      cases op with
      | keep =>
        refine ⟨2, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
      | pop =>
        refine ⟨2, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
      | push x =>
        refine ⟨4, by omega, by omega, ?_⟩
        intro bits
        apply BinaryStack.Config.ext
        all_goals first
          | solve | simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]
          | solve | funext i; fin_cases i <;> simp [_root_.OAI.MeanPayoff.BinaryStack.advance, BinaryStack.step, cfg, program, dispatch, localDest, localOp, localEmit, encode, he, applyOp]

end MeanPayoff.RegisterBits.Compile
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Instructions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.RegisterBits.Compile
open BinaryStack (advance applyOp)

theorem instruction {K : ℕ} (P : Program K) (q : Fin P.states) (coin : Bool)
    (prefx : List (List Bool)) (hp : prefx.length = (P.read q).val)
    (xs tail out : List Bool) :
    ∃ n, 1 ≤ n ∧ n ≤ 2 * (encodeAll prefx).length + 6 ∧
      ∀ bits : ℕ → Bool, bits 0 = coin →
      _root_.OAI.MeanPayoff.BinaryStack.advance (program P) bits
        (cfg P (.source q) (encodeAll prefx ++ encode xs ++ tail) [] out) n =
        sourceCfg P (localDest P q coin xs)
          (encodeAll prefx ++ encode (applyOp (localOp P q coin xs) xs) ++ tail) []
          (out ++ (localEmit P q coin xs).toList) := by
  obtain ⟨u, hu, hu4, hupdate⟩ := local_update P q coin xs tail (encodeAll prefx).reverse out
  let a := (encodeAll prefx).length
  refine ⟨(a + u + (a + 1)) + 1, by omega, by dsimp [a]; omega, ?_⟩
  intro bits hc
  rw [BinaryStack.advance_front, hc, step_source]
  have hfin : (⟨(P.read q).val, by omega⟩ : Fin (K + 1)) =
      ⟨prefx.length, by have := (P.read q).isLt; omega⟩ := by
    apply Fin.ext; exact hp.symm
  rw [hfin, List.append_assoc]
  rw [advance_add (a := a + u) (b := a + 1), advance_add (a := a) (b := u)]
  rw [seek_prefix P q coin prefx (by have := (P.read q).isLt; omega)]
  simp only [List.append_nil]
  rw [hupdate, show a + 1 = ((encodeAll prefx).reverse).length + 1 by simp [a], restore_all]
  simp [List.append_assoc]

end MeanPayoff.RegisterBits.Compile

namespace MeanPayoff.RegisterBits

namespace Compile

noncomputable def embed {K : ℕ} (P : Program K) (c : Config P) : BinaryStack.Config (program P) :=
  sourceCfg P c.control (encodeAll (List.ofFn c.stack)) [] c.output

theorem encode_split {K : ℕ} (s : Fin K → List Bool) (k : Fin K) :
    encodeAll (List.ofFn s) = encodeAll ((List.ofFn s).take k.val) ++
      encode (s k) ++ encodeAll ((List.ofFn s).drop (k.val + 1)) := by
  conv_lhs => rw [ofFn_split s k]
  simp [encodeAll, List.append_assoc]

theorem encode_update {K : ℕ} (s : Fin K → List Bool) (k : Fin K) (xs : List Bool) :
    encodeAll (List.ofFn (Function.update s k xs)) = encodeAll ((List.ofFn s).take k.val) ++
      encode xs ++ encodeAll ((List.ofFn s).drop (k.val + 1)) := by
  rw [ofFn_update, List.set_eq_take_cons_drop xs (by simp)]
  simp [encodeAll, List.append_assoc]

theorem step_simulation {K : ℕ} (P : Program K) (c : Config P) (q : Fin P.states)
    (hq : c.control = some q) (coin : Bool) :
    ∃ n, 1 ≤ n ∧ n ≤ 4 * storeSize c.stack + 2 * K + 6 ∧
      ∀ bits : ℕ → Bool, bits 0 = coin →
        BinaryStack.advance (program P) bits (embed P c) n = embed P (RegisterBits.step P c coin) := by
  let k := P.read q
  let pref := (List.ofFn c.stack).take k.val
  have hp : pref.length = k.val := by simp [pref]
  obtain ⟨n, hn, hnb, hs⟩ := instruction P q coin pref hp (c.stack k)
    (encodeAll ((List.ofFn c.stack).drop (k.val + 1))) c.output
  have hpBound : (encodeAll pref).length ≤ 2 * storeSize c.stack + K := by
    have h := encode_split c.stack k
    have hl := congrArg List.length h
    simp only [encoded_size, List.length_append] at hl
    dsimp [pref]
    omega
  refine ⟨n, hn, by omega, ?_⟩
  intro bits hc
  have hin : embed P c = cfg P (.source q)
      (encodeAll pref ++ encode (c.stack k) ++ encodeAll ((List.ofFn c.stack).drop (k.val + 1))) [] c.output := by
    unfold embed
    rw [encode_split c.stack k, hq]
    rfl
  rw [hin, hs bits hc]
  cases he : P.transition q (c.stack k).head? coin with
  | none =>
    simp only [localDest, localOp, localEmit, he, Option.map_none, Option.getD_none, Option.bind_none,
      BinaryStack.applyOp, Option.toList_none, List.append_nil]
    change sourceCfg P none _ [] c.output = _
    rw [← encode_split c.stack k]
    have he' : P.transition q (c.stack (P.read q)).head? coin = none := he
    simp only [embed, RegisterBits.step, hq, he']
  | some a =>
    simp only [localDest, localOp, localEmit, he, Option.map_some, Option.getD_some, Option.bind_some]
    have he' : P.transition q (c.stack (P.read q)).head? coin = some a := he
    unfold embed
    simp only [RegisterBits.step, hq, he']
    rw [encode_update]

end Compile


namespace Compile

 theorem step_simulation_all {K : ℕ} (P : Program K) (c : Config P) (coin : Bool) :
    ∃ n, 1 ≤ n ∧ n ≤ 4 * storeSize c.stack + 2 * K + 6 ∧
      ∀ bits : ℕ → Bool, bits 0 = coin →
        BinaryStack.advance (program P) bits (embed P c) n = embed P (RegisterBits.step P c coin) := by
  cases hc : c.control with
  | none =>
    refine ⟨1, by omega, by omega, ?_⟩
    intro bits _
    have hh : (embed P c).control = none := by simp [embed, sourceCfg, hc] ; rfl
    rw [BinaryStack.advance_halted _ _ _ hh]
    simp [RegisterBits.step, hc]
  | some q => exact step_simulation P c q hc coin

noncomputable def clock {K : ℕ} (P : Program K) (c : Config P) (coin : Bool) : ℕ :=
  (step_simulation_all P c coin).choose

end Compile


def initial {K : ℕ} (P : Program K) (input : List Bool) : Config P :=
  ⟨some P.start, fun i => if i.val = 0 then input else [], []⟩

namespace Compile
open BinaryStack (advance applyOp)

@[simp] theorem encodeAll_replicate_nil (n : ℕ) :
    encodeAll (List.replicate n []) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, encodeAll, encode, ih]

end Compile
end MeanPayoff.RegisterBits
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits
open RandomTree

def tree {K : ℕ} (P : Program K) : ℕ → Config P → RandomTree (Config P)
  | 0, c => .leaf c
  | n + 1, c => .coin (tree P n (step P c false)) (tree P n (step P c true))

namespace Compile

noncomputable def schedule {K : ℕ} (P : Program K) : ℕ → Config P → RandomTree (Config P)
  | 0, c => .leaf c
  | n + 1, c => .coin
      (wait (clock P c false - 1) (schedule P n (step P c false)))
      (wait (clock P c true - 1) (schedule P n (step P c true)))

noncomputable def initializedTree {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) :
    RandomTree (Config P) :=
  wait (3 * input.length + K + 3) (schedule P n (initial P input))

end Compile
end MeanPayoff.RegisterBits

namespace MeanPayoff.RegisterBits.Compile
open RandomTree

def bound {K : ℕ} (P : Program K) (input : List Bool) (n : ℕ) : ℕ :=
  3 * input.length + K + 3 + overhead K (storeSize (initial P input).stack) n

noncomputable def machine {K : ℕ} (P : Program K) : MeanPayoff.Machine :=
  BinaryStack.machine (program P)

open scoped Classical

end MeanPayoff.RegisterBits.Compile
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Stack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff
namespace SourceControl

inductive Result (G : Game) (B : ℕ) where
  | vector (I : SolveBox G.n B)
  | vectors (I : SolveBox G.n B)
  | orientation (P : Budgets G.n)
  | orientations (P : Budgets G.n)
  | inner (I : SolveBox G.n B)

abbrev Result.Value {G : Game} {B : ℕ} : Result G B → Type
  | .vector I => BoxVector I
  | .vectors I => List (BoxVector I)
  | .orientation P => Orientation P
  | .orientations P => List (Orientation P)
  | .inner I => InnerBox I

inductive Job (G : Game) (B : ℕ) : Result G B → Type where
  | solve (P : Budgets G.n) (I : SolveBox G.n B) : Job G B (.vector I)
  | ask (P : Budgets G.n) (I : SolveBox G.n B) : Job G B (.vector I)
  | trials (P : Budgets G.n) (I : SolveBox G.n B) (J : ℕ) : Job G B (.vectors I)
  | update (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (q : BoxVector I) : Job G B (.vector I)
  | centers (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (t : ℕ) (q : BoxVector I) : Job G B (.vectors I)
  | orient (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B) : Job G B (.orientation P)
  | orientTrials (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B) (J : ℕ) :
      Job G B (.orientations P)
  | orientPlus (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B) : Job G B (.orientation P)
  | tighten (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Job G B (.inner I)
  | reweight (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (side : Bool) (Hs : List (SmallSet P)) : Job G B (.vectors I)

inductive Frame (G : Game) (B : ℕ) : Result G B → Result G B → Type where
  | trialsHead (P : Budgets G.n) (I : SolveBox G.n B) (J : ℕ) :
      Frame G B (.vector I) (.vectors I)
  | vectorCons {I : SolveBox G.n B} (a : BoxVector I) :
      Frame G B (.vectors I) (.vectors I)
  | median (I : SolveBox G.n B) : Frame G B (.vectors I) (.vector I)
  | centerFirst (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (q : BoxVector I) :
      Frame G B (.vector (I.narrowCentered hB q.val)) (.vector I)
  | centerSecond (I : SolveBox G.n B) (hB : 128 * globalS B < I.width) (q : BoxVector I)
      (r : BoxVector (I.narrowCentered hB q.val)) :
      Frame G B (.vector (I.narrowCentered hB q.val)) (.vector I)
  | centersHead (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (t : ℕ) (q : BoxVector I) :
      Frame G B (.vector I) (.vectors I)
  | orientLoop (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.vectors I) (.orientation P)
  | orientTail {P : Budgets G.n} (H N : SmallSet P) : Frame G B (.orientation P) (.orientation P)
  | orientHead (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B) (J : ℕ) :
      Frame G B (.orientation P) (.orientations P)
  | orientCons {P : Budgets G.n} (O : Orientation P) :
      Frame G B (.orientations P) (.orientations P)
  | combine (P : Budgets G.n) : Frame G B (.orientations P) (.orientation P)
  | tightenFirst (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.vector I) (.inner I)
  | tightenSecond (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.vector I) (.inner I)
  | floor (I : SolveBox G.n B) (q : BoxVector I) : Frame G B (.inner (I.withFloor q)) (.inner I)
  | ceiling (I : SolveBox G.n B) (q : BoxVector I) : Frame G B (.inner (I.withCeiling q)) (.inner I)
  | solveTight (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.inner I) (.vector I)
  | solveOriented (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) : Frame G B (.orientation P) (.vector I)
  | reweightHead (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (side : Bool) (Hs : List (SmallSet P)) : Frame G B (.vector I) (.vectors I)
  | solveReweighted (P : Budgets G.n) (hR : 1 ≤ P.parameter) (I : SolveBox G.n B)
      (hB : 128 * globalS B < I.width) (side : Bool) : Frame G B (.vectors I) (.vector I)
  | capHigh (I : SolveBox G.n B) (hB : 128 * globalS B < I.width) (rs : List (BoxVector I)) :
      Frame G B (.vector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)) (.vector I)
  | capLow (I : SolveBox G.n B) (hB : 128 * globalS B < I.width) (rs : List (BoxVector I)) :
      Frame G B (.vector (I.capLow I.C I.C_positive (I.C_smaller hB).le)) (.vector I)
  | includeInner {I : SolveBox G.n B} (T : InnerBox I) : Frame G B (.vector T.box) (.vector I)

inductive Kont (G : Game) (B : ℕ) : Result G B → Result G B → Type where
  | done {R : Result G B} : Kont G B R R
  | push {A C R : Result G B} (f : Frame G B A C) (k : Kont G B C R) : Kont G B A R

inductive State (G : Game) (B : ℕ) (R : Result G B) where
  | call {A : Result G B} (j : Job G B A) (k : Kont G B A R)
  | ret {A : Result G B} (k : Kont G B A R) (v : A.Value)

def resume {G : Game} {B : ℕ} {A C R : Result G B} (f : Frame G B A C) (v : A.Value)
    (k : Kont G B C R) : Counted (State G B R) :=
  match f with
  | .trialsHead P I J => Counted.pure (.call (.trials P I J) (.push (.vectorCons v) k))
  | .vectorCons a => Counted.pure (.ret k (a :: v))
  | .median I => Counted.pure (.ret k (I.medianBox v))
  | .centerFirst P _ I hB q =>
      Counted.pure (.call (.ask P.reduceM (I.narrowCentered hB q.val)) (.push (.centerSecond I hB q v) k))
  | .centerSecond I _ _ r => Counted.pure (.ret k (I.averageClipped r.val v.val))
  | .centersHead P hR I hB t q =>
      Counted.pure (.call (.centers P hR I hB t v) (.push (.vectorCons q) k))
  | .orientLoop P hR I hB =>
      let H := PositiveDisplacement I (v.getD (globalS B) I.midpoint)
      let N := NegativeDisplacement I (v.getD (globalS B) I.midpoint)
      if hH : 1 / 2 < P.measure H then
        Counted.pure (.ret k ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩)
      else if hN : 1 / 2 < P.measure N then
        Counted.pure (.ret k ⟨false, [⟨Nᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩)
      else
        (Counted.lift (RandomTree.uniformBelow (sampleExponent B))).map fun j =>
          .call (.orient P hR (I.wideCentered hB (v.getD j I.midpoint).val))
            (.push (.orientTail ⟨H, le_of_not_gt hH⟩ ⟨N, le_of_not_gt hN⟩) k)
  | .orientTail H N => Counted.pure (.ret k ⟨v.chooseY, v.exceptions ++ [H, N]⟩)
  | .orientHead P hR I J => Counted.pure (.call (.orientTrials P hR I J) (.push (.orientCons v) k))
  | .orientCons O => Counted.pure (.ret k (O :: v))
  | .combine _ => Counted.pure (.ret k (combineOrientations v))
  | .tightenFirst P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ v.val i - I.a i then
        Counted.pure (.call (.tighten P hR (I.withFloor v) hB) (.push (.floor I v) k))
      else Counted.pure (.call (.ask P.reduceM I) (.push (.tightenSecond P hR I hB) k))
  | .tightenSecond P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ I.b i - v.val i then
        Counted.pure (.call (.tighten P hR (I.withCeiling v) hB) (.push (.ceiling I v) k))
      else Counted.pure (.ret k ⟨I, rfl, le_refl _, le_refl _⟩)
  | .floor _ q => Counted.pure (.ret k ⟨v.box, v.width_eq, q.property.1.trans v.floor_le, v.ceiling_le⟩)
  | .ceiling _ q => Counted.pure (.ret k ⟨v.box, v.width_eq, v.floor_le, v.ceiling_le.trans q.property.2⟩)
  | .solveTight P hR _ hB =>
      have hK : 128 * globalS B < v.box.width := by rw [v.width_eq]; exact hB
      Counted.pure (.call (.orientPlus P hR v.box) (.push (.solveOriented P hR v.box hK) (.push (.includeInner v) k)))
  | .solveOriented P hR I hB =>
      Counted.pure (.call (.reweight P hR I v.chooseY v.exceptions) (.push (.solveReweighted P hR I hB v.chooseY) k))
  | .reweightHead P hR I side Hs => Counted.pure (.call (.reweight P hR I side Hs) (.push (.vectorCons v) k))
  | .solveReweighted P _ I hB side =>
      if side then Counted.pure (.call (.solve P (I.capHigh I.C I.C_positive (I.C_smaller hB).le)) (.push (.capHigh I hB v) k))
      else Counted.pure (.call (.solve P (I.capLow I.C I.C_positive (I.C_smaller hB).le)) (.push (.capLow I hB v) k))
  | .capHigh I hB rs => Counted.pure (.ret k (rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le v)))
  | .capLow I hB rs => Counted.pure (.ret k (rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le v)))
  | .includeInner T => Counted.pure (.ret k (T.include v))

def step {G : Game} {B : ℕ} {R : Result G B} : State G B R → Counted (State G B R)
  | .ret .done v => Counted.pure (.ret .done v)
  | .ret (.push f k) v => resume f v k
  | .call job k => match job with
    | .solve P I => Counted.charge 1 <|
        if hR : P.parameter < 1 then Counted.pure (.ret k (I.smallVector P))
        else if hB : I.width ≤ 128 * globalS B then Counted.pure (.ret k (I.exactVector G))
        else Counted.pure (.call (.tighten P (le_of_not_gt hR) I (by omega)) (.push (.solveTight P (le_of_not_gt hR) I (by omega)) k))
    | .ask P I => Counted.pure (.call (.trials P I (globalJ G.n B)) (.push (.median I) k))
    | .trials P I J => match J with
      | 0 => Counted.pure (.ret k [])
      | J + 1 => Counted.pure (.call (.solve P I) (.push (.trialsHead P I J) k))
    | .update P hR I hB q =>
        Counted.pure (.call (.ask P.reduceK (I.narrowCentered hB q.val)) (.push (.centerFirst P hR I hB q) k))
    | .centers P hR I hB t q => match t with
      | 0 => Counted.pure (.ret k [q])
      | t + 1 => Counted.pure (.call (.update P hR I hB q) (.push (.centersHead P hR I hB t q) k))
    | .orient P hR I =>
        if hB : I.width ≤ 128 * globalS B then Counted.pure (.ret k (orientBase G P I))
        else Counted.pure (.call (.centers P hR I (by omega) (globalS B) I.midpoint) (.push (.orientLoop P hR I (by omega)) k))
    | .orientTrials P hR I J => match J with
      | 0 => Counted.pure (.ret k [])
      | J + 1 => Counted.pure (.call (.orient P hR I) (.push (.orientHead P hR I J) k))
    | .orientPlus P hR I => Counted.pure (.call (.orientTrials P hR I (globalJ G.n B)) (.push (.combine P) k))
    | .tighten P hR I hB => Counted.pure (.call (.ask P.reduceK I) (.push (.tightenFirst P hR I hB) k))
    | .reweight P hR I side Hs => match Hs with
      | [] => Counted.pure (.ret k [])
      | H :: Hs =>
          Counted.pure (.call (.ask (if side then P.reweightM H.val else P.reweightK H.val) I)
            (.push (.reweightHead P hR I side Hs) k))

def Job.tag {G : Game} {B : ℕ} {A : Result G B} : Job G B A → Fin 10
  | .solve .. => 0 | .ask .. => 1 | .trials .. => 2 | .update .. => 3
  | .centers .. => 4 | .orient .. => 5 | .orientTrials .. => 6 | .orientPlus .. => 7
  | .tighten .. => 8 | .reweight .. => 9

def Frame.tag {G : Game} {B : ℕ} {A C : Result G B} : Frame G B A C → Fin 23
  | .trialsHead .. => 0 | .vectorCons .. => 1 | .median .. => 2 | .centerFirst .. => 3
  | .centerSecond .. => 4 | .centersHead .. => 5 | .orientLoop .. => 6 | .orientTail .. => 7
  | .orientHead .. => 8 | .orientCons .. => 9 | .combine .. => 10 | .tightenFirst .. => 11
  | .tightenSecond .. => 12 | .floor .. => 13 | .ceiling .. => 14 | .solveTight .. => 15
  | .solveOriented .. => 16 | .reweightHead .. => 17 | .solveReweighted .. => 18
  | .capHigh .. => 19 | .capLow .. => 20 | .includeInner .. => 21

end SourceControl
namespace SourceControl
abbrev wholeLower {G : Game} {B : ℕ} (P : Budgets G.n) :
    CountedAlgorithm.LowerSolver (Bmax := B) P := fun Q _ I => CountedAlgorithm.solve G Q I

def Job.denote {G : Game} {B : ℕ} {A : Result G B} : Job G B A → Counted A.Value
  | .solve P I => CountedAlgorithm.solve G P I
  | .ask P I => I.repeatedCounted (CountedAlgorithm.solve G P I) (globalJ G.n B)
  | .trials P I J => Counted.trials (CountedAlgorithm.solve G P I) J
  | .update P hR I hB q => CountedAlgorithm.centerUpdate P hR (wholeLower P) I hB q
  | .centers P hR I hB t q => CountedAlgorithm.centerSteps P hR (wholeLower P) I hB t q
  | .orient P hR I => CountedAlgorithm.orient G P hR (wholeLower P) I
  | .orientTrials P hR I J => Counted.trials (CountedAlgorithm.orient G P hR (wholeLower P) I) J
  | .orientPlus P hR I => CountedAlgorithm.orientPlus
      (CountedAlgorithm.orient G P hR (wholeLower P) I) (globalJ G.n B)
  | .tighten P hR I hB => CountedAlgorithm.tighten P hR (wholeLower P) I hB
  | .reweight P _ I side Hs => Counted.traverse (fun H =>
      I.repeatedCounted (CountedAlgorithm.solve G (if side then P.reweightM H.val else P.reweightK H.val) I)
        (globalJ G.n B)) Hs

def Frame.denote {G : Game} {B : ℕ} {A C : Result G B} (f : Frame G B A C) (v : A.Value) :
    Counted C.Value := match f with
  | .trialsHead P I J => (Job.denote (.trials P I J)).map (v :: ·)
  | .vectorCons a => Counted.pure (a :: v)
  | .median I => Counted.pure (I.medianBox v)
  | .centerFirst P _ I hB q => (Job.denote (.ask P.reduceM (I.narrowCentered hB q.val))).map
      (fun r => I.averageClipped v.val r.val)
  | .centerSecond I _ _ r => Counted.pure (I.averageClipped r.val v.val)
  | .centersHead P hR I hB t q => (Job.denote (.centers P hR I hB t v)).map (q :: ·)
  | .orientLoop P hR I hB => CountedAlgorithm.orientationTail G P I v
      (fun q => CountedAlgorithm.orient G P hR (wholeLower P) (I.wideCentered hB q.val))
  | .orientTail H N => Counted.pure ⟨v.chooseY, v.exceptions ++ [H, N]⟩
  | .orientHead P hR I J => (Job.denote (.orientTrials P hR I J)).map (v :: ·)
  | .orientCons O => Counted.pure (O :: v)
  | .combine _ => Counted.pure (combineOrientations v)
  | .tightenFirst P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ v.val i - I.a i then
        (Job.denote (.tighten P hR (I.withFloor v) hB)).map fun T =>
          ⟨T.box, T.width_eq, v.property.1.trans T.floor_le, T.ceiling_le⟩
      else (Job.denote (.ask P.reduceM I)).bind fun r =>
        if _ : ∃ i, (I.delta : ℤ) ≤ I.b i - r.val i then
          (Job.denote (.tighten P hR (I.withCeiling r) hB)).map fun T =>
            ⟨T.box, T.width_eq, T.floor_le, T.ceiling_le.trans r.property.2⟩
        else Counted.pure ⟨I, rfl, le_refl _, le_refl _⟩
  | .tightenSecond P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ I.b i - v.val i then
        (Job.denote (.tighten P hR (I.withCeiling v) hB)).map fun T =>
          ⟨T.box, T.width_eq, T.floor_le, T.ceiling_le.trans v.property.2⟩
      else Counted.pure ⟨I, rfl, le_refl _, le_refl _⟩
  | .floor _ q => Counted.pure ⟨v.box, v.width_eq, q.property.1.trans v.floor_le, v.ceiling_le⟩
  | .ceiling _ q => Counted.pure ⟨v.box, v.width_eq, v.floor_le, v.ceiling_le.trans q.property.2⟩
  | .solveTight P hR _ hB =>
      have hK : 128 * globalS B < v.box.width := by rw [v.width_eq]; exact hB
      (Job.denote (.orientPlus P hR v.box)).bind fun O =>
      (CountedAlgorithm.finishChoice G P hR (wholeLower P) v.box hK O
        (CountedAlgorithm.solve G P (v.box.capHigh v.box.C v.box.C_positive (v.box.C_smaller hK).le))
        (CountedAlgorithm.solve G P (v.box.capLow v.box.C v.box.C_positive (v.box.C_smaller hK).le))).map v.include
  | .solveOriented P hR I hB => CountedAlgorithm.finishChoice G P hR (wholeLower P) I hB v
      (CountedAlgorithm.solve G P (I.capHigh I.C I.C_positive (I.C_smaller hB).le))
      (CountedAlgorithm.solve G P (I.capLow I.C I.C_positive (I.C_smaller hB).le))
  | .reweightHead P hR I side Hs => (Job.denote (.reweight P hR I side Hs)).map (v :: ·)
  | .solveReweighted P _ I hB side =>
      if side then (CountedAlgorithm.solve G P (I.capHigh I.C I.C_positive (I.C_smaller hB).le)).map
        (fun p => v.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le p))
      else (CountedAlgorithm.solve G P (I.capLow I.C I.C_positive (I.C_smaller hB).le)).map
        (fun p => v.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le p))
  | .capHigh I hB rs => Counted.pure (rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le v))
  | .capLow I hB rs => Counted.pure (rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le v))
  | .includeInner T => Counted.pure (T.include v)

def Kont.denote {G : Game} {B : ℕ} {A R : Result G B} : Kont G B A R → A.Value → Counted R.Value
  | .done, v => Counted.pure v
  | .push f k, v => (f.denote v).bind k.denote

def State.denote {G : Game} {B : ℕ} {R : Result G B} : State G B R → Counted R.Value
  | .call j k => j.denote.bind k.denote
  | .ret k v => k.denote v

end SourceControl

end MeanPayoff
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_StackSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.SourceControl

def askCredit (n B : ℕ) : ℕ := trialCredit (globalJ n B)+2
def exceptionCredit (n B : ℕ) : ℕ := askCredit n B+3
def updateCredit (n B : ℕ) : ℕ := 2*askCredit n B+3
def centersCredit (n B t : ℕ) : ℕ := t*(updateCredit n B+3)+1
def orientUnit (n B : ℕ) : ℕ := centersCredit n B (globalS B)+2*exceptionCredit n B+3
def orientCredit (n B w : ℕ) : ℕ := (Nat.clog 2 w+1)*orientUnit n B
def orientTrialsCredit (n B w t : ℕ) : ℕ := t*(orientCredit n B w+3)+1
def orientPlusCredit (n B w : ℕ) : ℕ := orientTrialsCredit n B w (globalJ n B)+2
def tightenUnit (n B : ℕ) : ℕ := 2*askCredit n B+5
def tightenCredit {n B : ℕ} (I : SolveBox n B) : ℕ :=
  (volume I.b I.a / I.delta+1)*tightenUnit n B
def reweightCredit (n B t : ℕ) : ℕ := t*exceptionCredit n B+1

def Result.credit {G : Game} {B : ℕ} (A : Result G B) (v : A.Value) : ℕ :=
  match A with
  | .orientation _ => v.exceptions.length * exceptionCredit G.n B
  | .orientations _ => (v.map Orientation.exceptions).flatten.length * exceptionCredit G.n B
  | .vector _ | .vectors _ | .inner _ => 0

def Job.credit {G : Game} {B : ℕ} {A : Result G B} : Job G B A → ℕ
  | .solve .. => 0
  | .ask .. => askCredit G.n B
  | .trials _ _ t => trialCredit t
  | .update .. => updateCredit G.n B
  | .centers _ _ _ _ t _ => centersCredit G.n B t
  | .orient _ _ I => orientCredit G.n B I.width
  | .orientTrials _ _ I t => orientTrialsCredit G.n B I.width t
  | .orientPlus _ _ I => orientPlusCredit G.n B I.width
  | .tighten _ _ I _ => tightenCredit I
  | .reweight _ _ _ _ Hs => reweightCredit G.n B Hs.length

def Frame.credit {G : Game} {B : ℕ} {A C : Result G B} : Frame G B A C → ℕ
  | .trialsHead _ _ t => trialCredit t+2
  | .vectorCons _ | .median _ | .centerSecond .. => 1
  | .centerFirst .. => askCredit G.n B+2
  | .centersHead _ _ _ _ t _ => centersCredit G.n B t+2
  | .orientLoop _ _ I _ => orientCredit G.n B (2*I.E)+2*exceptionCredit G.n B+2
  | .orientTail .. => 2*exceptionCredit G.n B+1
  | .orientHead _ _ I t => orientTrialsCredit G.n B I.width t+2
  | .orientCons O => O.exceptions.length*exceptionCredit G.n B+1
  | .combine _ => 1
  | .tightenFirst _ _ I _ => (volume I.b I.a / I.delta)*tightenUnit G.n B+askCredit G.n B+4
  | .tightenSecond _ _ I _ => (volume I.b I.a / I.delta)*tightenUnit G.n B+3
  | .floor .. | .ceiling .. => 1
  | .solveTight _ _ I _ => orientPlusCredit G.n B I.width+6
  | .solveOriented .. => 4
  | .reweightHead _ _ _ _ Hs => reweightCredit G.n B Hs.length+2
  | .solveReweighted .. => 2
  | .capHigh .. | .capLow .. | .includeInner _ => 1

def Kont.credit {G : Game} {B : ℕ} {A R : Result G B} : Kont G B A R → ℕ
  | .done => 0
  | .push f k => f.credit+k.credit

def State.credit {G : Game} {B : ℕ} {R : Result G B} : State G B R → ℕ
  | .call j k => j.credit+k.credit
  | .ret (A := A) k v => A.credit v+k.credit

def State.halted {G : Game} {B : ℕ} {R : Result G B} : State G B R → Prop
  | .ret .done _ => True
  | _ => False

def controlAllowance (n B : ℕ) : ℕ :=
  (8*n*globalS B+1)*tightenUnit n B+
    orientPlusCredit n B (B+1)+7

end MeanPayoff.SourceControl
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ArithmeticBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff
namespace SourceControl

def State.rank {G : Game} {B : ℕ} {R : Result G B} (s : State G B R) : ℕ :=
  s.credit+controlAllowance G.n B*s.denote.maximum

def run {G : Game} {B : ℕ} {R : Result G B} : ℕ → State G B R → Counted (State G B R)
  | 0, s => Counted.pure s
  | n+1, s => (step s).bind (run n)

end SourceControl
end MeanPayoff
namespace MeanPayoff.SourceControl

noncomputable def rootControlBound (G : Game) : ℕ :=
  controlAllowance G.n (topWidth G).toNat * rootInvocationBound G

end MeanPayoff.SourceControl
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_OperatorDevices
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.EdgeScan
open BinaryData

def Represents (G : Game) (p : Vec (Fin G.n)) (v : Fin G.n) (z : Pair × List Pair) : Prop :=
  (∀ ab ∈ z.1::z.2, ∃ e ∈ outgoing G v,
    ab.1.val+ab.2.val = transformed G e+p (G.head e)) ∧
  (∀ e ∈ outgoing G v, ∃ ab ∈ z.1::z.2,
    ab.1.val+ab.2.val = transformed G e+p (G.head e))

end MeanPayoff.TreeDevice.EdgeScan
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Sorting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Sort
open BinaryData

theorem fold_sort_perm (xs acc : List W) :
    (xs.foldl (fun a w => insert (w,a)) acc).Perm (acc++xs) := by
  induction xs generalizing acc with
  | nil => simp
  | cons w xs ih =>
    change (xs.foldl _ (insert (w,acc))).Perm _
    apply (ih (insert (w,acc))).trans
    apply ((insert_perm w acc).append_right xs).trans
    simpa only [List.cons_append,List.nil_append,List.append_assoc,List.singleton_append] using
      (show ([w]++acc).Perm (acc++[w]) from List.perm_append_comm).append_right xs

theorem sort_perm (xs : List W) : (sort xs).Perm xs := by
  simpa only [sort,List.nil_append] using fold_sort_perm xs []

end MeanPayoff.TreeDevice.Sort
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_BatchDevices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Graph
open BinaryData

def codeEdge (G : Game) (w : Fin G.m → W) (e : Fin G.m) : Edge :=
  (List.replicate (G.head e).val (),w e)

def codePot {n : ℕ} (p : Fin n → W) : Pot := List.ofFn p

end MeanPayoff.TreeDevice.Graph

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_OperatorCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Graph
open BinaryData

theorem outList_ne_nil (G : Game) (v : Fin G.n) : outList G v ≠ [] := by
  obtain ⟨e,he⟩ := G.total v
  have hm : e ∈ outList G v := by simp [outList,he]
  intro h; simp [h] at hm

noncomputable def firstEdge (G : Game) (v : Fin G.n) : Fin G.m := (outList G v).head (outList_ne_nil G v)

noncomputable def codeVertex (G : Game) (w : Fin G.m → W) (v : Fin G.n) : Vertex :=
  (G.maxOwner v,(codeEdge G w (firstEdge G v),(outList G v).tail.map (codeEdge G w)))

noncomputable def codeVertices (G : Game) (w : Fin G.m → W) : List Vertex :=
  List.ofFn (codeVertex G w)

end MeanPayoff.TreeDevice.Graph

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_WordDecoding
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MeanPayoff.TreeDevice.Prefix
open BinaryData
abbrev Count := Median.Count
abbrev State := Bool × (Count × List Bool)
def countData := listTree Median.unitData
def listsData := product countData (listTree boolData)
def stateData := product Compare.bitTree listsData
def inputData := product stateData boolData

def step (z : State × Bool) : State :=
  if z.1.1 then (true,(z.1.2.1,z.2::z.1.2.2))
  else if z.2 then (false,(()::z.1.2.1,z.1.2.2)) else (true,z.1.2)

noncomputable def countDevice : Device inputData countData (fun z : State × Bool => z.1.2.1) :=
  compose (compose (first stateData boolData) (second Compare.bitTree listsData)) (first countData (listTree boolData))
noncomputable def restDevice : Device inputData (listTree boolData) (fun z : State × Bool => z.1.2.2) :=
  compose (compose (first stateData boolData) (second Compare.bitTree listsData)) (second countData (listTree boolData))
noncomputable def bitDevice : Device inputData boolData (fun z : State × Bool => z.2) := second stateData boolData
noncomputable def doneDevice : Device inputData Compare.bitTree (fun z : State × Bool => z.1.1) :=
  compose (first stateData boolData) (first Compare.bitTree listsData)
noncomputable def testDevice : Device inputData Compare.bitTree (fun z : State × Bool => z.2) :=
  (compose bitDevice Multiply.rawTest).extFun (by intro z; rfl)
noncomputable def putDevice : Device inputData stateData (fun z : State × Bool => (true,(z.1.2.1,z.2::z.1.2.2))) :=
  fanout (constant inputData Compare.bitTree true)
    (fanout countDevice (compose (fanout bitDevice restDevice) (Lists.consDevice boolData)))
noncomputable def incDevice : Device inputData stateData (fun z : State × Bool => (false,(()::z.1.2.1,z.1.2.2))) :=
  fanout (constant inputData Compare.bitTree false)
    (fanout (compose countDevice Median.incrementDevice) restDevice)
noncomputable def stopDevice : Device inputData stateData (fun z : State × Bool => (true,z.1.2)) :=
  fanout (constant inputData Compare.bitTree true)
    (compose (first stateData boolData) (second Compare.bitTree listsData))
noncomputable def stepDevice : Device inputData stateData step :=
  branch doneDevice putDevice (branch testDevice incDevice stopDevice)

def read (xs : List Bool) : Count × List Bool :=
  let s := Fold.fold step (false,([],[])) xs
  (s.2.1,s.2.2.reverse)

noncomputable def initDevice : Device (listTree boolData) (product stateData (listTree boolData))
    (fun xs : List Bool => ((false,([],[])),xs)) :=
  fanout (constant (listTree boolData) stateData (false,([],[]))) (identity (listTree boolData))
noncomputable def finishDevice : Device stateData listsData
    (fun s : State => (s.2.1,s.2.2.reverse)) :=
  compose (second Compare.bitTree listsData) (pairMap (identity countData) (Lists.reverseDevice boolData))
noncomputable def device : Device (listTree boolData) listsData read :=
  compose initDevice (compose (Fold.device stepDevice) finishDevice)

theorem read_from_done (c : Count) (r xs : List Bool) :
    Fold.fold step (true,(c,r)) xs = (true,(c,xs.reverse++r)) := by
  induction xs generalizing r with
  | nil => simp [Fold.fold]
  | cons b bs ih =>
    change Fold.fold step (true,(c,b::r)) bs = _
    rw [ih]
    simp [List.reverse_cons,List.append_assoc]

theorem count_linear : LinearCost countDevice :=
  LinearCost.compose (LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)) (LinearCost.first _ _)
theorem rest_linear : LinearCost restDevice :=
  LinearCost.compose (LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)) (LinearCost.second _ _)
theorem bit_linear : LinearCost bitDevice := LinearCost.second _ _
theorem done_linear : LinearCost doneDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem test_linear : LinearCost testDevice := LinearCost.compose bit_linear Multiply.rawTest_linear
theorem increment_linear : LinearCost Median.incrementDevice :=
  LinearCost.compose (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)) (LinearCost.cons _)
theorem put_linear : LinearCost putDevice :=
  LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.fanout count_linear
    (LinearCost.compose (LinearCost.fanout bit_linear rest_linear) (LinearCost.cons _)))
theorem inc_linear : LinearCost incDevice :=
  LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.fanout
    (LinearCost.compose count_linear increment_linear) rest_linear)
theorem stop_linear : LinearCost stopDevice :=
  LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _))
theorem step_linear : LinearCost stepDevice :=
  LinearCost.branch done_linear put_linear (LinearCost.branch test_linear inc_linear stop_linear)

theorem step_size (s : State) (b : Bool) :
    treeSize (stateData (step (s,b))) ≤ treeSize (stateData s)+treeSize (boolData b)+1 := by
  rcases s with ⟨flag,c,r⟩
  cases flag <;> cases b <;> simp only [step,Bool.false_eq_true,↓reduceIte,
    stateData,listsData,countData,product,listTree,Compare.bitTree,listData,boolData,
    treeSize_pair,treeSize_nil,Median.unitData] <;> omega

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (LinearCost.fanout (LinearCost.constant _ _ _) (LinearCost.identity _)).polynomial
    (PolynomialCost.compose (Fold.polynomial step_linear.polynomial step_size)
      (PolynomialCost.compose (LinearCost.second _ _).polynomial
        (PolynomialCost.pairMap (LinearCost.identity _).polynomial (PolynomialCost.reverse _))))
end MeanPayoff.TreeDevice.Prefix

namespace MeanPayoff.TreeDevice.Split
open BinaryData
def stateData := product (listTree boolData) (listTree boolData)
def inputData := product stateData Median.unitData

noncomputable def fstDevice : Device inputData (listTree boolData) (fun z : State × Unit => z.1.1) :=
  compose (first stateData Median.unitData) (first (listTree boolData) (listTree boolData))
noncomputable def sndDevice : Device inputData (listTree boolData) (fun z : State × Unit => z.1.2) :=
  compose (first stateData Median.unitData) (second (listTree boolData) (listTree boolData))
noncomputable def headDevice : Device inputData boolData (fun z : State × Unit => z.1.2.headD false) :=
  compose sndDevice (Head.device boolData false)
noncomputable def pushDevice : Device inputData (listTree boolData) (fun z : State × Unit => z.1.2.headD false::z.1.1) :=
  compose (fanout headDevice fstDevice) (Lists.consDevice boolData)
noncomputable def stepDevice : Device inputData stateData step := fanout pushDevice (compose sndDevice (Tail.device boolData))

def split (z : List Bool × Median.Count) : List Bool × List Bool :=
  let s := Fold.fold step ([],z.1) z.2
  (s.1.reverse,s.2)
noncomputable def initDevice : Device (product (listTree boolData) Prefix.countData)
    (product stateData Prefix.countData) (fun z : List Bool × Median.Count => (([],z.1),z.2)) :=
  fanout (compose (first (listTree boolData) Prefix.countData) (Lists.nilPrefix (listTree boolData) boolData))
    (second (listTree boolData) Prefix.countData)
noncomputable def finishDevice : Device stateData stateData (fun s : State => (s.1.reverse,s.2)) :=
  pairMap (Lists.reverseDevice boolData) (identity (listTree boolData))
noncomputable def device : Device (product (listTree boolData) Prefix.countData) stateData split :=
  compose initDevice (compose (Fold.device stepDevice) finishDevice)

theorem fst_linear : LinearCost fstDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem snd_linear : LinearCost sndDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem head_linear : LinearCost headDevice := LinearCost.compose snd_linear (LinearCost.head _ _)
theorem push_linear : LinearCost pushDevice :=
  LinearCost.compose (LinearCost.fanout head_linear fst_linear) (LinearCost.cons _)
theorem step_linear : LinearCost stepDevice :=
  LinearCost.fanout push_linear (LinearCost.compose snd_linear (LinearCost.tail _))

theorem step_size (s : State) (u : Unit) :
    treeSize (stateData (step (s,u))) ≤ treeSize (stateData s)+treeSize (Median.unitData u)+1 := by
  rcases s with ⟨acc,xs⟩
  cases xs with
  | nil => simp [step,stateData,product,listTree,boolData,treeSize_pair,Median.unitData]; omega
  | cons b bs => simp [step,stateData,product,listTree,treeSize_pair,Median.unitData]; omega

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose
    (LinearCost.fanout (LinearCost.compose (LinearCost.first _ _) (LinearCost.nilPrefix _ _)) (LinearCost.second _ _)).polynomial
    (PolynomialCost.compose (Fold.polynomial step_linear.polynomial step_size)
      (PolynomialCost.pairMap (PolynomialCost.reverse _) (LinearCost.identity _).polynomial))
end MeanPayoff.TreeDevice.Split

namespace MeanPayoff.TreeDevice.IntegerRead
open BinaryData

noncomputable def positiveDevice : Device (listTree boolData) wordData positive :=
  (Lists.nilPrefix (listTree boolData) boolData).recode (listTree boolData) wordData id positive
    (by intro xs; rfl)
    (by intro xs; simp only [id_eq,product,listTree,positive,wordData,listData,boolData,Halve.listTree_boolData])
noncomputable def decrementDevice : Device (listTree boolData) wordData decrement :=
  compose (fanout positiveDevice (constant (listTree boolData) wordData minusOne)) Add.device

def readNat (xs : List Bool) : W × List Bool :=
  let p := Prefix.read xs
  let q := Split.split (p.2,p.1)
  (decrement q.1,q.2)

noncomputable def natFieldsDevice : Device (listTree boolData) Split.stateData
    (fun xs : List Bool => let p := Prefix.read xs; Split.split (p.2,p.1)) :=
  compose Prefix.device (compose (pairSwap Prefix.countData (listTree boolData)) Split.device)
noncomputable def natDevice : Device (listTree boolData) (product wordData (listTree boolData)) readNat :=
  compose natFieldsDevice (pairMap decrementDevice (identity (listTree boolData)))

abbrev Parsed := Bool × (W × List Bool)
def parsedData := product boolData (product wordData (listTree boolData))

def signed (z : Parsed) : W × List Bool := (if z.1 then Negate.negate z.2.1 else z.2.1,z.2.2)
def readInt (xs : List Bool) : W × List Bool := signed (xs.headD false,readNat xs.tail)

noncomputable def signTest : Device parsedData Compare.bitTree (fun z : Parsed => z.1) :=
  (compose (first boolData (product wordData (listTree boolData))) Multiply.rawTest).extFun (by intro z; rfl)
noncomputable def magnitude : Device parsedData wordData (fun z : Parsed => z.2.1) :=
  compose (second boolData (product wordData (listTree boolData))) (first wordData (listTree boolData))
noncomputable def remainder : Device parsedData (listTree boolData) (fun z : Parsed => z.2.2) :=
  compose (second boolData (product wordData (listTree boolData))) (second wordData (listTree boolData))
noncomputable def negativeMagnitude : Device parsedData wordData (fun z : Parsed => Negate.negate z.2.1) :=
  @compose Parsed W W parsedData wordData wordData (fun z => z.2.1) Negate.negate magnitude Negate.device
noncomputable def chosenMagnitude : Device parsedData wordData
    (fun z : Parsed => if z.1 then Negate.negate z.2.1 else z.2.1) :=
  branch signTest negativeMagnitude magnitude
noncomputable def signedDevice : Device parsedData (product wordData (listTree boolData)) signed :=
  fanout chosenMagnitude remainder
noncomputable def intFieldsDevice : Device (listTree boolData) parsedData
    (fun xs : List Bool => (xs.headD false,readNat xs.tail)) :=
  fanout (Head.device boolData false) (compose (Tail.device boolData) natDevice)
noncomputable def intDevice : Device (listTree boolData) (product wordData (listTree boolData)) readInt :=
  compose intFieldsDevice signedDevice

theorem positive_linear : LinearCost positiveDevice := by
  unfold positiveDevice
  apply LinearCost.recode
  exact LinearCost.nilPrefix _ _
theorem decrement_linear : LinearCost decrementDevice :=
  LinearCost.compose (LinearCost.fanout positive_linear (LinearCost.constant _ _ _)) LinearCost.add

theorem natFields_polynomial : PolynomialCost natFieldsDevice :=
  PolynomialCost.compose Prefix.polynomial
    (PolynomialCost.compose (LinearCost.pairSwap _ _).polynomial Split.polynomial)

theorem nat_polynomial : PolynomialCost natDevice :=
  PolynomialCost.compose natFields_polynomial
    (PolynomialCost.pairMap decrement_linear.polynomial (LinearCost.identity _).polynomial)

theorem signTest_linear : LinearCost signTest := LinearCost.compose (LinearCost.first _ _) Multiply.rawTest_linear
theorem magnitude_linear : LinearCost magnitude := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem remainder_linear : LinearCost remainder := LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)
theorem negative_polynomial : PolynomialCost negativeMagnitude :=
  PolynomialCost.compose magnitude_linear.polynomial Negate.polynomial
theorem chosen_polynomial : PolynomialCost chosenMagnitude :=
  PolynomialCost.branch signTest_linear.polynomial negative_polynomial magnitude_linear.polynomial
theorem signed_polynomial : PolynomialCost signedDevice :=
  PolynomialCost.fanout chosen_polynomial remainder_linear.polynomial

theorem int_polynomial : PolynomialCost intDevice :=
  PolynomialCost.compose
    (PolynomialCost.fanout (LinearCost.head _ _).polynomial
      (PolynomialCost.compose (LinearCost.tail _).polynomial nat_polynomial)) signed_polynomial

end MeanPayoff.TreeDevice.IntegerRead
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Counters
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Address
open BinaryData
abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev State := W × Count
def countData := listTree Median.unitData
def stateData := product wordData countData
def inputData := product stateData boolData

def dec (w : W) : W := Add.sumPair (w,IntegerRead.minusOne)
def test (w : W) : Bool := Compare.testPair (Median.zeroWord,w)
def step (z : State × Bool) : State :=
  if test z.1.1 then (dec z.1.1,()::z.1.2) else z.1

noncomputable def wordDevice : Device inputData wordData (fun z : State × Bool => z.1.1) :=
  compose (first stateData boolData) (first wordData countData)
noncomputable def listDevice : Device inputData countData (fun z : State × Bool => z.1.2) :=
  compose (first stateData boolData) (second wordData countData)
noncomputable def decDevice : Device wordData wordData dec :=
  compose (fanout (identity wordData) (constant wordData wordData IntegerRead.minusOne)) Add.device
noncomputable def testDevice : Device inputData Compare.bitTree (fun z : State × Bool => test z.1.1) :=
  compose (fanout (constant inputData wordData Median.zeroWord) wordDevice) Compare.device
noncomputable def newWordDevice : Device inputData wordData (fun z : State × Bool => dec z.1.1) :=
  @compose _ _ _ inputData wordData wordData (fun z : State × Bool => z.1.1) dec wordDevice decDevice
noncomputable def newCountDevice : Device inputData countData (fun z : State × Bool => ()::z.1.2) :=
  compose listDevice Median.incrementDevice
noncomputable def nextDevice : Device inputData stateData
    (fun z : State × Bool => (dec z.1.1,()::z.1.2)) :=
  fanout newWordDevice newCountDevice
noncomputable def stepDevice : Device inputData stateData step :=
  branch testDevice nextDevice (first stateData boolData)

def read (z : W × List Bool) : Count := (Fold.fold step (z.1,[]) z.2).2
noncomputable def initDevice : Device (product wordData (listTree boolData))
    (product stateData (listTree boolData)) (fun z : W × List Bool => ((z.1,[]),z.2)) :=
  pairMap (Lists.nilSuffix wordData Median.unitData) (identity (listTree boolData))
noncomputable def finishDevice : Device (product stateData (listTree boolData)) countData
    (fun z : State × List Bool => (Fold.fold step z.1 z.2).2) :=
  @compose _ _ _ (product stateData (listTree boolData)) stateData countData
    (fun z : State × List Bool => Fold.fold step z.1 z.2) (fun s : State => s.2)
    (Fold.device stepDevice) (second wordData countData)
noncomputable def device : Device (product wordData (listTree boolData)) countData read :=
  @compose _ _ _ (product wordData (listTree boolData)) (product stateData (listTree boolData)) countData
    (fun z : W × List Bool => ((z.1,[]),z.2))
    (fun z : State × List Bool => (Fold.fold step z.1 z.2).2) initDevice finishDevice

theorem word_linear : LinearCost wordDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem list_linear : LinearCost listDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem dec_linear : LinearCost decDevice :=
  LinearCost.compose (LinearCost.fanout (LinearCost.identity _) (LinearCost.constant _ _ _)) LinearCost.add
theorem test_linear : LinearCost testDevice :=
  LinearCost.compose (LinearCost.fanout (LinearCost.constant _ _ _) word_linear) LinearCost.compare
theorem newWord_linear : LinearCost newWordDevice := LinearCost.compose word_linear dec_linear
theorem newCount_linear : LinearCost newCountDevice := LinearCost.compose list_linear Prefix.increment_linear
theorem next_linear : LinearCost nextDevice := LinearCost.fanout newWord_linear newCount_linear
theorem step_linear : LinearCost stepDevice :=
  LinearCost.branch test_linear next_linear (LinearCost.first _ _)

theorem step_word_length (s : State) (b : Bool) :
    (step (s,b)).1.digits.length ≤ s.1.digits.length+1 := by
  unfold step
  split
  · change (SignedBits.add s.1.sign true false s.1.digits []).digits.length ≤ _
    rw [SignedBits.add_length]
    simp
  · simp

theorem step_count_length (s : State) (b : Bool) :
    (step (s,b)).2.length ≤ s.2.length+1 := by
  unfold step
  split <;> simp

theorem fold_length (s : State) (xs : List Bool) :
    (Fold.fold step s xs).1.digits.length ≤ s.1.digits.length+xs.length ∧
    (Fold.fold step s xs).2.length ≤ s.2.length+xs.length := by
  induction xs generalizing s with
  | nil => simp [Fold.fold]
  | cons x xs ih =>
    have hh := ih (step (s,x))
    have hw := step_word_length s x
    have hc := step_count_length s x
    change (Fold.fold step (step (s,x)) xs).1.digits.length ≤ _ ∧
      (Fold.fold step (step (s,x)) xs).2.length ≤ _
    simp only [List.length_cons]
    omega

theorem count_size (c : Count) : treeSize (countData c)=2*c.length+1 := by
  induction c with
  | nil => rfl
  | cons u c ih => simp only [countData,listTree,treeSize_pair,Median.unitData,treeSize_nil,List.length_cons] at *; omega

theorem fold_polynomial : PolynomialCost (Fold.device stepDevice) := by
  obtain ⟨K,hK⟩ := step_linear
  refine ⟨402+40*K,2,?_⟩
  rintro ⟨s,xs⟩
  let N := treeSize (product stateData (listTree boolData) (s,xs))+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hs₀ : treeSize (wordData s.1)+treeSize (countData s.2)+treeSize (listTree boolData xs)+3 = N := by
    simp only [N,product,stateData,treeSize_pair]; omega
  have hw : s.1.digits.length ≤ N := by have := digits_le_wordSize s.1; omega
  have ha : s.2.length ≤ N := by have := count_size s.2; omega
  have hl : xs.length+1 ≤ N := by have := list_length_le_size boolData xs; omega
  have he : treeSize (listTree boolData xs) ≤ N := by omega
  have hp : ∀ k ≤ xs.length, treeSize (stateData (Fold.fold step s (xs.take k))) ≤ 32*N := by
    intro k hk
    have hw' := wordSize_bound (Fold.fold step s (xs.take k)).1
    have ha' := count_size (Fold.fold step s (xs.take k)).2
    have hd := fold_length s (xs.take k)
    have hx : (xs.take k).length ≤ k := List.length_take_le _ _
    simp only [stateData,product,treeSize_pair]
    omega
  have ht := Fold.time_of_prefix_bound stepDevice K 1 (32*N) N
    (by intro z; simpa only [pow_one,inputData] using hK z) s xs he hp
  have hc : 12*(32*N)+K*(32*N+N+2)^1+11 ≤ (400+40*K)*N := by
    simp only [pow_one]
    nlinarith
  have hbig := Nat.mul_le_mul hl hc
  have htime := ht.trans hbig
  have hpos : 1 ≤ N^2 := one_le_pow₀ hN
  change Fold.time stepDevice s xs+2 ≤ (402+40*K)*N^2
  rw [pow_two] at hpos ⊢
  nlinarith

theorem init_polynomial : PolynomialCost initDevice :=
  (LinearCost.pairMap (LinearCost.nilSuffix _ _) (LinearCost.identity _)).polynomial
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.compose fold_polynomial (LinearCost.second _ _).polynomial
theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose init_polynomial finish_polynomial
end MeanPayoff.TreeDevice.Address
namespace MeanPayoff.TreeDevice.Header
open BinaryData
abbrev W := SignedBits.Word
abbrev Count := Median.Count
abbrev Numbers := W × (W × List Bool)
abbrev Fields := List Bool × Numbers
abbrev Result := Count × (Count × (List Bool × List Bool))
def restData := listTree boolData
def countData := listTree Median.unitData
def numbersData := product wordData (product wordData restData)
def fieldsData := product restData numbersData
def resultData := product countData (product countData (product restData restData))

def numbers (xs : List Bool) : Numbers :=
  let p := IntegerRead.readNat xs
  (p.1,IntegerRead.readNat p.2)
def nCount (p : Fields) := Address.read (p.2.1,p.1)
def mCount (p : Fields) := Address.read (p.2.2.1,p.1)
def partition (p : Fields) := Split.split (p.2.2.2,nCount p)
def finish (p : Fields) : Result := (nCount p,(mCount p,partition p))
def read (xs : List Bool) := finish (xs,numbers xs)

noncomputable def numbersDevice : Device restData numbersData numbers :=
  compose IntegerRead.natDevice (pairMap (identity wordData) IntegerRead.natDevice)
noncomputable def inputDevice : Device fieldsData restData (fun p : Fields => p.1) := first restData numbersData
noncomputable def nWordDevice : Device fieldsData wordData (fun p : Fields => p.2.1) :=
  compose (second restData numbersData) (first wordData (product wordData restData))
noncomputable def moreDevice : Device fieldsData (product wordData restData) (fun p : Fields => p.2.2) :=
  compose (second restData numbersData) (second wordData (product wordData restData))
noncomputable def mWordDevice : Device fieldsData wordData (fun p : Fields => p.2.2.1) :=
  compose moreDevice (first wordData restData)
noncomputable def remainderDevice : Device fieldsData restData (fun p : Fields => p.2.2.2) :=
  compose moreDevice (second wordData restData)
noncomputable def nCountDevice : Device fieldsData countData nCount :=
  compose (fanout nWordDevice inputDevice) Address.device
noncomputable def mCountDevice : Device fieldsData countData mCount :=
  compose (fanout mWordDevice inputDevice) Address.device
noncomputable def partitionDevice : Device fieldsData (product restData restData) partition :=
  compose (fanout remainderDevice nCountDevice) Split.device
noncomputable def finishDevice : Device fieldsData resultData finish :=
  fanout nCountDevice (fanout mCountDevice partitionDevice)
noncomputable def device : Device restData resultData read :=
  compose (fanout (identity restData) numbersDevice) finishDevice

theorem input_linear : LinearCost inputDevice := LinearCost.first _ _
theorem nWord_linear : LinearCost nWordDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem more_linear : LinearCost moreDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)
theorem mWord_linear : LinearCost mWordDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem remainder_linear : LinearCost remainderDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem nCount_polynomial : PolynomialCost nCountDevice :=
  PolynomialCost.compose (LinearCost.fanout nWord_linear input_linear).polynomial Address.polynomial
theorem mCount_polynomial : PolynomialCost mCountDevice :=
  PolynomialCost.compose (LinearCost.fanout mWord_linear input_linear).polynomial Address.polynomial
theorem partition_polynomial : PolynomialCost partitionDevice :=
  PolynomialCost.compose (PolynomialCost.fanout remainder_linear.polynomial nCount_polynomial) Split.polynomial
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.fanout nCount_polynomial (PolynomialCost.fanout mCount_polynomial partition_polynomial)
theorem numbers_polynomial : PolynomialCost numbersDevice :=
  PolynomialCost.compose IntegerRead.nat_polynomial
    (PolynomialCost.pairMap (LinearCost.identity _).polynomial IntegerRead.nat_polynomial)
theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.fanout (LinearCost.identity _).polynomial numbers_polynomial) finish_polynomial

end MeanPayoff.TreeDevice.Header
namespace MeanPayoff.TreeDevice.EdgeRead
open BinaryData
abbrev Words := W × (W × (W × List Bool))
abbrev Fields := List Bool × Words
def restData := listTree boolData
def wordsData := product wordData (product wordData (product wordData restData))
def fieldsData := product restData wordsData

def words (xs : List Bool) : Words :=
  let p := IntegerRead.readNat xs
  let q := IntegerRead.readNat p.2
  (p.1,(q.1,IntegerRead.readInt q.2))
def source (p : Fields) := Address.read (Address.dec p.2.1,p.1)
def target (p : Fields) := Address.read (Address.dec p.2.2.1,p.1)
def edge (p : Fields) : Edge := (source p,(target p,p.2.2.2.1))
def finish (p : Fields) : Edge × List Bool := (edge p,p.2.2.2.2)
def read (z : List Bool × List Bool) := finish (z.1,words z.2)

noncomputable def wordsDevice : Device restData wordsData words :=
  compose IntegerRead.natDevice
    (pairMap (identity wordData) (compose IntegerRead.natDevice (pairMap (identity wordData) IntegerRead.intDevice)))
noncomputable def inputDevice : Device fieldsData restData (fun p : Fields => p.1) := first restData wordsData
noncomputable def sourceWordDevice : Device fieldsData wordData (fun p : Fields => p.2.1) :=
  compose (second restData wordsData) (first wordData (product wordData (product wordData restData)))
noncomputable def moreDevice : Device fieldsData (product wordData (product wordData restData)) (fun p : Fields => p.2.2) :=
  compose (second restData wordsData) (second wordData (product wordData (product wordData restData)))
noncomputable def targetWordDevice : Device fieldsData wordData (fun p : Fields => p.2.2.1) :=
  compose moreDevice (first wordData (product wordData restData))
noncomputable def lastDevice : Device fieldsData (product wordData restData) (fun p : Fields => p.2.2.2) :=
  compose moreDevice (second wordData (product wordData restData))
noncomputable def weightDevice : Device fieldsData wordData (fun p : Fields => p.2.2.2.1) :=
  compose lastDevice (first wordData restData)
noncomputable def remainderDevice : Device fieldsData restData (fun p : Fields => p.2.2.2.2) :=
  compose lastDevice (second wordData restData)
noncomputable def sourceDecDevice : Device fieldsData wordData (fun p : Fields => Address.dec p.2.1) :=
  @compose _ _ _ fieldsData wordData wordData (fun p : Fields => p.2.1) Address.dec sourceWordDevice Address.decDevice
noncomputable def targetDecDevice : Device fieldsData wordData (fun p : Fields => Address.dec p.2.2.1) :=
  @compose _ _ _ fieldsData wordData wordData (fun p : Fields => p.2.2.1) Address.dec targetWordDevice Address.decDevice
noncomputable def sourceDevice : Device fieldsData countData source :=
  compose (fanout sourceDecDevice inputDevice) Address.device
noncomputable def targetDevice : Device fieldsData countData target :=
  compose (fanout targetDecDevice inputDevice) Address.device
noncomputable def edgeDevice : Device fieldsData edgeData edge :=
  fanout sourceDevice (fanout targetDevice weightDevice)
noncomputable def finishDevice : Device fieldsData (product edgeData restData) finish :=
  fanout edgeDevice remainderDevice
noncomputable def device : Device (product restData restData) (product edgeData restData) read :=
  compose (pairMap (identity restData) wordsDevice) finishDevice

theorem words_polynomial : PolynomialCost wordsDevice :=
  PolynomialCost.compose IntegerRead.nat_polynomial
    (PolynomialCost.pairMap (LinearCost.identity _).polynomial
      (PolynomialCost.compose IntegerRead.nat_polynomial (PolynomialCost.pairMap (LinearCost.identity _).polynomial IntegerRead.int_polynomial)))
theorem input_linear : LinearCost inputDevice := LinearCost.first _ _
theorem sourceWord_linear : LinearCost sourceWordDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem more_linear : LinearCost moreDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)
theorem targetWord_linear : LinearCost targetWordDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem last_linear : LinearCost lastDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem weight_linear : LinearCost weightDevice := LinearCost.compose last_linear (LinearCost.first _ _)
theorem remainder_linear : LinearCost remainderDevice := LinearCost.compose last_linear (LinearCost.second _ _)
theorem sourceDec_linear : LinearCost sourceDecDevice := LinearCost.compose sourceWord_linear Address.dec_linear
theorem targetDec_linear : LinearCost targetDecDevice := LinearCost.compose targetWord_linear Address.dec_linear
theorem source_polynomial : PolynomialCost sourceDevice :=
  PolynomialCost.compose (LinearCost.fanout sourceDec_linear input_linear).polynomial Address.polynomial
theorem target_polynomial : PolynomialCost targetDevice :=
  PolynomialCost.compose (LinearCost.fanout targetDec_linear input_linear).polynomial Address.polynomial
theorem edge_polynomial : PolynomialCost edgeDevice :=
  PolynomialCost.fanout source_polynomial (PolynomialCost.fanout target_polynomial weight_linear.polynomial)
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.fanout edge_polynomial remainder_linear.polynomial
theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.pairMap (LinearCost.identity _).polynomial words_polynomial) finish_polynomial
end MeanPayoff.TreeDevice.EdgeRead
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ParserCosts
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice
open BinaryData
namespace Prefix

theorem fold_suffix (c : Count) (xs : List Bool) :
    (Fold.fold step (false,(c,[])) xs).2.2.reverse = suffix xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false =>
      change (Fold.fold step (true,(c,[])) bs).2.2.reverse = bs
      rw [read_from_done]
      simp
    | true =>
      change (Fold.fold step (false,(()::c,[])) bs).2.2.reverse = suffix bs
      exact ih _

theorem read_suffix (xs : List Bool) : (read xs).2=suffix xs := fold_suffix [] xs

end Prefix

theorem listTree_append_right_le {α : Type} (ea : α → Data) (xs ys : List α) :
    treeSize (listTree ea ys) ≤ treeSize (listTree ea (xs++ys)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,listTree,treeSize_pair]; omega

theorem listTree_drop_le {α : Type} (ea : α → Data) (xs : List α) (n : ℕ) :
    treeSize (listTree ea (xs.drop n)) ≤ treeSize (listTree ea xs) := by
  have h := listTree_append_right_le ea (xs.take n) (xs.drop n)
  simpa only [List.take_append_drop] using h

namespace Prefix
theorem remainder_size (xs : List Bool) : treeSize (listTree boolData (read xs).2) ≤ treeSize (listTree boolData xs) := by
  rw [read_suffix]
  obtain ⟨pre,hp⟩ := suffix_isSuffix xs
  simpa only [hp] using listTree_append_right_le boolData pre (suffix xs)
end Prefix

namespace Split
theorem fold_rest (xs acc : List Bool) (ks : Median.Count) :
    (Fold.fold step (acc,xs) ks).2 = xs.drop ks.length := by
  induction ks generalizing xs acc with
  | nil => rfl
  | cons u ks ih =>
    change (Fold.fold step (xs.headD false::acc,xs.tail) ks).2 = _
    rw [ih]
    cases xs <;> simp

theorem rest (xs : List Bool) (ks : Median.Count) : (split (xs,ks)).2 = xs.drop ks.length := fold_rest _ _ _

theorem remainder_size (xs : List Bool) (ks : Median.Count) :
    treeSize (listTree boolData (split (xs,ks)).2) ≤ treeSize (listTree boolData xs) := by
  rw [rest]
  exact listTree_drop_le _ _ _
end Split

namespace IntegerRead
theorem nat_remainder_size (xs : List Bool) :
    treeSize (listTree boolData (readNat xs).2) ≤ treeSize (listTree boolData xs) :=
  (Split.remainder_size (Prefix.read xs).2 (Prefix.read xs).1).trans (Prefix.remainder_size xs)

theorem int_remainder_size (xs : List Bool) :
    treeSize (listTree boolData (readInt xs).2) ≤ treeSize (listTree boolData xs) := by
  have h := nat_remainder_size xs.tail
  have ht : treeSize (listTree boolData xs.tail) ≤ treeSize (listTree boolData xs) := by
    cases xs <;> simp [listTree] ; omega
  exact h.trans ht
end IntegerRead

namespace EdgeRead
theorem remainder_size (env xs : List Bool) :
    treeSize (restData (read (env,xs)).2) ≤ treeSize (restData xs) := by
  exact (IntegerRead.int_remainder_size (IntegerRead.readNat (IntegerRead.readNat xs).2).2).trans
    ((IntegerRead.nat_remainder_size (IntegerRead.readNat xs).2).trans (IntegerRead.nat_remainder_size xs))
end EdgeRead
end MeanPayoff.TreeDevice
namespace MeanPayoff.TreeDevice.EdgesRead
open BinaryData
abbrev Edge := EdgeRead.Edge
abbrev Count := Median.Count
abbrev State := StreamFold.State (List Bool) Edge (List Bool)
abbrev Args := List Bool × (List Bool × Count)
def restData := listTree boolData
def countData := listTree Median.unitData
def edgesData := listTree EdgeRead.edgeData
def stateData := StreamFold.stateData restData EdgeRead.edgeData restData
def argsData := product restData (product restData countData)
def outputData := product edgesData restData

def read (z : Args) : List Edge × List Bool :=
  let s := Fold.fold (StreamFold.step EdgeRead.read) (z.1,([],z.2.1)) z.2.2
  (s.2.1.reverse,s.2.2)

noncomputable def moreDevice : Device argsData (product restData countData) (fun z : Args => z.2) := second restData (product restData countData)
noncomputable def streamDevice : Device argsData restData (fun z : Args => z.2.1) :=
  compose moreDevice (first restData countData)
noncomputable def countDevice : Device argsData countData (fun z : Args => z.2.2) :=
  compose moreDevice (second restData countData)
noncomputable def stateDevice : Device argsData stateData (fun z : Args => (z.1,([],z.2.1))) :=
  fanout (first restData (product restData countData)) (compose streamDevice (Lists.nilPrefix restData EdgeRead.edgeData))
noncomputable def initDevice : Device argsData (product stateData countData)
    (fun z : Args => ((z.1,([],z.2.1)),z.2.2)) := fanout stateDevice countDevice
noncomputable def finishDevice : Device stateData outputData (fun s : State => (s.2.1.reverse,s.2.2)) :=
  compose (second restData (product edgesData restData))
    (pairMap (Lists.reverseDevice EdgeRead.edgeData) (identity restData))
noncomputable def foldDevice : Device (product stateData countData) outputData
    (fun z : State × Count => let s := Fold.fold (StreamFold.step EdgeRead.read) z.1 z.2; (s.2.1.reverse,s.2.2)) :=
  compose (Fold.device (StreamFold.stepDevice EdgeRead.device)) finishDevice
noncomputable def device : Device argsData outputData read := compose initDevice foldDevice

def lower (e : BinaryInput.Edge) : Edge := (List.replicate e.1 (),(List.replicate e.2.1 (),EdgeRead.encodedWord e.2.2))
def code (es : List BinaryInput.Edge) : List Bool := (es.map BinaryInput.encodeEdge).flatten

theorem more_linear : LinearCost moreDevice := LinearCost.second _ _
theorem stream_linear : LinearCost streamDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem count_linear : LinearCost countDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem state_linear : LinearCost stateDevice :=
  LinearCost.fanout (LinearCost.first _ _) (LinearCost.compose stream_linear (LinearCost.nilPrefix _ _))
theorem init_linear : LinearCost initDevice := LinearCost.fanout state_linear count_linear
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.compose (LinearCost.second _ _).polynomial
    (PolynomialCost.pairMap (PolynomialCost.reverse _) (LinearCost.identity _).polynomial)
theorem fold_polynomial : PolynomialCost foldDevice :=
  PolynomialCost.compose (StreamFold.polynomial EdgeRead.device EdgeRead.polynomial EdgeRead.remainder_size) finish_polynomial
theorem polynomial : PolynomialCost device := PolynomialCost.compose init_linear.polynomial fold_polynomial
end MeanPayoff.TreeDevice.EdgesRead
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_ArenaParsing
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.ArenaRead
open BinaryData
abbrev Fields := List Bool × Header.Result
def fieldsData := product restData Header.resultData

def edgeArgs (p : Fields) : EdgesRead.Args := (p.1,(p.2.2.2.2,p.2.2.1))
def finish (p : Fields) : Arena := (p.2.1,(p.2.2.2.1,(EdgesRead.read (edgeArgs p)).1))
def read (xs : List Bool) := finish (xs,Header.read xs)

noncomputable def headerDevice : Device fieldsData Header.resultData (fun p : Fields => p.2) := second restData Header.resultData
noncomputable def nDevice : Device fieldsData countData (fun p : Fields => p.2.1) :=
  compose headerDevice (first countData (product countData (product restData restData)))
noncomputable def moreDevice : Device fieldsData (product countData (product restData restData)) (fun p : Fields => p.2.2) :=
  compose headerDevice (second countData (product countData (product restData restData)))
noncomputable def mDevice : Device fieldsData countData (fun p : Fields => p.2.2.1) :=
  compose moreDevice (first countData (product restData restData))
noncomputable def lastDevice : Device fieldsData (product restData restData) (fun p : Fields => p.2.2.2) :=
  compose moreDevice (second countData (product restData restData))
noncomputable def ownersDevice : Device fieldsData restData (fun p : Fields => p.2.2.2.1) :=
  compose lastDevice (first restData restData)
noncomputable def remainderDevice : Device fieldsData restData (fun p : Fields => p.2.2.2.2) :=
  compose lastDevice (second restData restData)
noncomputable def argsDevice : Device fieldsData EdgesRead.argsData edgeArgs :=
  fanout (first restData Header.resultData) (fanout remainderDevice mDevice)
noncomputable def parseDevice : Device fieldsData EdgesRead.outputData (fun p : Fields => EdgesRead.read (edgeArgs p)) :=
  compose argsDevice EdgesRead.device
noncomputable def edgesDevice : Device fieldsData edgesData (fun p : Fields => (EdgesRead.read (edgeArgs p)).1) :=
  compose parseDevice (first edgesData restData)
noncomputable def finishDevice : Device fieldsData arenaData finish :=
  fanout nDevice (fanout ownersDevice edgesDevice)
noncomputable def device : Device restData arenaData read :=
  compose (fanout (identity restData) Header.device) finishDevice

theorem header_linear : LinearCost headerDevice := LinearCost.second _ _
theorem n_linear : LinearCost nDevice := LinearCost.compose header_linear (LinearCost.first _ _)
theorem more_linear : LinearCost moreDevice := LinearCost.compose header_linear (LinearCost.second _ _)
theorem m_linear : LinearCost mDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem last_linear : LinearCost lastDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem owners_linear : LinearCost ownersDevice := LinearCost.compose last_linear (LinearCost.first _ _)
theorem remainder_linear : LinearCost remainderDevice := LinearCost.compose last_linear (LinearCost.second _ _)
theorem args_linear : LinearCost argsDevice := LinearCost.fanout (LinearCost.first _ _) (LinearCost.fanout remainder_linear m_linear)
theorem parse_polynomial : PolynomialCost parseDevice := PolynomialCost.compose args_linear.polynomial EdgesRead.polynomial
theorem edges_polynomial : PolynomialCost edgesDevice := PolynomialCost.compose parse_polynomial (LinearCost.first _ _).polynomial
theorem finish_polynomial : PolynomialCost finishDevice :=
  PolynomialCost.fanout n_linear.polynomial (PolynomialCost.fanout owners_linear.polynomial edges_polynomial)

theorem polynomial : PolynomialCost device :=
  PolynomialCost.compose (PolynomialCost.fanout (LinearCost.identity _).polynomial Header.polynomial) finish_polynomial
end MeanPayoff.TreeDevice.ArenaRead
namespace MeanPayoff.TreeDevice.Scale
open BinaryData

def stateData := product wordData wordData
def countData := listTree Median.unitData

noncomputable def baseDevice : Device (product stateData Median.unitData) wordData (fun z : State × Unit => z.1.1) :=
  compose (first stateData Median.unitData) (first wordData wordData)
noncomputable def accDevice : Device (product stateData Median.unitData) wordData (fun z : State × Unit => z.1.2) :=
  compose (first stateData Median.unitData) (second wordData wordData)
noncomputable def stepDevice : Device (product stateData Median.unitData) stateData step :=
  fanout baseDevice (compose (fanout accDevice baseDevice) Add.device)

noncomputable def initDevice : Device (product wordData countData) (product stateData countData)
    (fun z : W × Count => ((z.1,z.1),z.2)) :=
  fanout (fanout (first wordData countData) (first wordData countData)) (second wordData countData)
noncomputable def device : Device (product wordData countData) wordData scale :=
  @compose (W × Count) State W (product wordData countData) stateData wordData
    (fun z => Fold.fold step (z.1,z.1) z.2) (fun s => s.2)
    (compose initDevice (Fold.device stepDevice)) (second wordData wordData)

theorem fold_first (s : State) (xs : Count) : (Fold.fold step s xs).1=s.1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons b bs ih => exact (ih (step (s,b))).trans rfl

theorem step_length (s : State) (b : Unit) :
    (step (s,b)).2.digits.length = max s.2.digits.length s.1.digits.length+1 :=
  SignedBits.add_length _ _ _ _ _

theorem fold_length (s : State) (xs : Count) :
    (Fold.fold step s xs).2.digits.length≤ max s.2.digits.length s.1.digits.length+xs.length := by
  induction xs generalizing s with
  | nil => simp only [Fold.fold,List.foldl_nil,List.length_nil,Nat.add_zero]; omega
  | cons b bs ih =>
    have h := ih (step (s,b))
    rw [step_first,step_length] at h
    change (Fold.fold step (step (s,b)) bs).2.digits.length≤_
    simp only [List.length_cons]
    omega

theorem base_linear : LinearCost baseDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.first _ _)
theorem acc_linear : LinearCost accDevice := LinearCost.compose (LinearCost.first _ _) (LinearCost.second _ _)
theorem step_linear : LinearCost stepDevice :=
  LinearCost.fanout base_linear (LinearCost.compose (LinearCost.fanout acc_linear base_linear) LinearCost.add)

theorem fold_polynomial : PolynomialCost (Fold.device stepDevice) := by
  apply Fold.polynomial_of_prefix step_linear.polynomial 32 1
  intro s xs k hk
  let N := treeSize (product stateData countData (s,xs))+1
  have hN : 1≤N := by dsimp [N]; omega
  have he : treeSize (wordData s.1)+treeSize (wordData s.2)+treeSize (countData xs)+3=N := by
    simp only [N,stateData,product,treeSize_pair]; omega
  have hw := digits_le_wordSize s.1
  have ha := digits_le_wordSize s.2
  have hl := list_length_le_size Median.unitData xs
  have hp := fold_length s (xs.take k)
  have ht := List.length_take_le k xs
  have him : (Fold.fold step s (xs.take k)).2.digits.length≤2*N := by dsimp only [countData] at he; omega
  have hb := wordSize_bound (Fold.fold step s (xs.take k)).2
  rw [pow_one]
  change treeSize (stateData (Fold.fold step s (xs.take k)))≤32*N
  simp only [stateData,product,treeSize_pair,fold_first]
  omega

theorem init_linear : LinearCost initDevice :=
  LinearCost.fanout (LinearCost.fanout (LinearCost.first _ _) (LinearCost.first _ _)) (LinearCost.second _ _)
theorem polynomial : PolynomialCost device := by
  exact PolynomialCost.compose (PolynomialCost.compose init_linear.polynomial fold_polynomial) (LinearCost.second _ _).polynomial

noncomputable def transformDevice : Device (product wordData countData) wordData transform :=
  compose (fanout device (constant (product wordData countData) wordData oneWord)) Add.device

theorem transform_polynomial : PolynomialCost transformDevice :=
  PolynomialCost.compose (PolynomialCost.fanout polynomial (LinearCost.constant _ _ _).polynomial) LinearCost.add.polynomial
end MeanPayoff.TreeDevice.Scale
namespace MeanPayoff.TreeDevice.CountTest
open BinaryData

def equal (z : Count × Count) : Bool :=
  if (z.1.drop z.2.length).isEmpty then (z.2.drop z.1.length).isEmpty else false
noncomputable def forwardDevice : Device (product countData countData) Compare.bitTree
    (fun z : Count × Count => (z.1.drop z.2.length).isEmpty) :=
  compose (Median.dropDevice Median.unitData) emptyDevice
noncomputable def backwardDevice : Device (product countData countData) Compare.bitTree
    (fun z : Count × Count => (z.2.drop z.1.length).isEmpty) :=
  compose (pairSwap countData countData) forwardDevice
noncomputable def device : Device (product countData countData) Compare.bitTree equal :=
  branch forwardDevice backwardDevice (constant _ _ false)

theorem forward_polynomial : PolynomialCost forwardDevice :=
  PolynomialCost.compose (Median.drop_polynomial _) empty_polynomial
theorem backward_polynomial : PolynomialCost backwardDevice :=
  PolynomialCost.compose (LinearCost.pairSwap _ _).polynomial forward_polynomial
theorem polynomial : PolynomialCost device :=
  PolynomialCost.branch forward_polynomial backward_polynomial (LinearCost.constant _ _ _).polynomial
end MeanPayoff.TreeDevice.CountTest

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Normalization
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Normalize
open BinaryData

def edge (z : Count × Edge) : Edge := (z.2.1,(z.2.2.1,Scale.transform (z.2.2.2,z.1)))
noncomputable def sourceDevice : Device (product countData edgeData) countData (fun z : Count × Edge => z.2.1) :=
  compose (second countData edgeData) (first countData (product countData wordData))
noncomputable def moreDevice : Device (product countData edgeData) (product countData wordData) (fun z : Count × Edge => z.2.2) :=
  compose (second countData edgeData) (second countData (product countData wordData))
noncomputable def targetDevice : Device (product countData edgeData) countData (fun z : Count × Edge => z.2.2.1) :=
  compose moreDevice (first countData wordData)
noncomputable def weightDevice : Device (product countData edgeData) wordData (fun z : Count × Edge => z.2.2.2) :=
  compose moreDevice (second countData wordData)
noncomputable def scaleArgsDevice : Device (product countData edgeData) (product wordData countData)
    (fun z : Count × Edge => (z.2.2.2,z.1)) := fanout weightDevice (first countData edgeData)
noncomputable def scaleDevice : Device (product countData edgeData) wordData (fun z : Count × Edge => Scale.transform (z.2.2.2,z.1)) :=
  @compose (Count × Edge) (SignedBits.Word × Count) SignedBits.Word (product countData edgeData)
    (product wordData countData) wordData (fun z => (z.2.2.2,z.1)) Scale.transform scaleArgsDevice Scale.transformDevice
noncomputable def edgeDevice : Device (product countData edgeData) edgeData edge :=
  fanout sourceDevice (fanout targetDevice scaleDevice)

def arena (z : Arena) : Arena := (z.1,(z.2.1,z.2.2.map (fun e => edge (z.1,e))))
noncomputable def restDevice : Device arenaData (product ownersData edgesData) (fun z : Arena => z.2) := second countData (product ownersData edgesData)
noncomputable def ownersDevice : Device arenaData ownersData (fun z : Arena => z.2.1) := compose restDevice (first ownersData edgesData)
noncomputable def edgesDevice : Device arenaData edgesData (fun z : Arena => z.2.2) := compose restDevice (second ownersData edgesData)
noncomputable def mapDevice : Device arenaData edgesData (fun z : Arena => z.2.2.map (fun e => edge (z.1,e))) :=
  compose (fanout nDevice edgesDevice) (EnvMap.device edgeDevice)
noncomputable def arenaDevice : Device arenaData arenaData arena :=
  fanout nDevice (fanout ownersDevice mapDevice)

def read (xs : List Bool) := arena (ArenaRead.read xs)
noncomputable def device : Device (listTree boolData) arenaData read := compose ArenaRead.device arenaDevice

theorem source_linear : LinearCost sourceDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem more_linear : LinearCost moreDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)
theorem target_linear : LinearCost targetDevice := LinearCost.compose more_linear (LinearCost.first _ _)
theorem weight_linear : LinearCost weightDevice := LinearCost.compose more_linear (LinearCost.second _ _)
theorem scaleArgs_linear : LinearCost scaleArgsDevice := LinearCost.fanout weight_linear (LinearCost.first _ _)
theorem scale_polynomial : PolynomialCost scaleDevice :=
  PolynomialCost.compose scaleArgs_linear.polynomial Scale.transform_polynomial
theorem edge_polynomial : PolynomialCost edgeDevice :=
  PolynomialCost.fanout source_linear.polynomial (PolynomialCost.fanout target_linear.polynomial scale_polynomial)
theorem n_linear : LinearCost nDevice := LinearCost.first _ _
theorem rest_linear : LinearCost restDevice := LinearCost.second _ _
theorem owners_linear : LinearCost ownersDevice := LinearCost.compose rest_linear (LinearCost.first _ _)
theorem edges_linear : LinearCost edgesDevice := LinearCost.compose rest_linear (LinearCost.second _ _)
theorem map_polynomial : PolynomialCost mapDevice :=
  PolynomialCost.compose (LinearCost.fanout n_linear edges_linear).polynomial (EnvMap.polynomial edge_polynomial)
theorem arena_polynomial : PolynomialCost arenaDevice :=
  PolynomialCost.fanout n_linear.polynomial (PolynomialCost.fanout owners_linear.polynomial map_polynomial)

theorem polynomial : PolynomialCost device := PolynomialCost.compose ArenaRead.polynomial arena_polynomial
end MeanPayoff.TreeDevice.Normalize
namespace MeanPayoff.TreeDevice.Adjacency
open BinaryData
abbrev Count := Median.Count
abbrev Edge := EdgeRead.Edge
abbrev Edges := List Edge

def countData := listTree Median.unitData
def edgeData := EdgeRead.edgeData
def edgesData := listTree edgeData

def test (p : Count × Edge) := CountTest.equal (p.1,p.2.1)
noncomputable def testArgsDevice : Device (product countData edgeData) (product countData countData)
    (fun p : Count × Edge => (p.1,p.2.1)) :=
  fanout (first countData edgeData) (compose (second countData edgeData) (first countData Graph.edgeData))
noncomputable def testDevice : Device (product countData edgeData) Compare.bitTree test :=
  @compose (Count × Edge) (Count × Count) Bool (product countData edgeData) (product countData countData)
    Compare.bitTree (fun p => (p.1,p.2.1)) CountTest.equal testArgsDevice CountTest.device

def select (z : Count × Edges) : List Graph.Edge :=
  (z.2.filter (fun e => test (z.1,e))).map Prod.snd
noncomputable def selectDevice : Device (product countData edgesData) (listTree Graph.edgeData) select :=
  compose (EnvFilter.device testDevice) (Map.device (second countData Graph.edgeData))

def defaultEdge : Graph.Edge := ([],Median.zeroWord)
def nonempty (xs : List Graph.Edge) : Graph.Edges := (xs.headD defaultEdge,xs.tail)
noncomputable def nonemptyDevice : Device (listTree Graph.edgeData) Graph.edgesData nonempty :=
  fanout (Head.device Graph.edgeData defaultEdge) (Tail.device Graph.edgeData)

def vertex (edges : Edges) (p : Count × Bool) : Graph.Vertex :=
  (p.2,nonempty (select (p.1,edges)))
abbrev Args := Edges × (Count × Bool)
def argsData := product edgesData (product countData boolData)
noncomputable def localDevice : Device argsData (product countData boolData) (fun p : Args => p.2) := second edgesData (product countData boolData)
noncomputable def ownerDevice : Device argsData Compare.bitTree (fun p : Args => p.2.2) :=
  (compose (compose localDevice (second countData boolData)) Multiply.rawTest).extFun (by intro p; rfl)
noncomputable def addressDevice : Device argsData countData (fun p : Args => p.2.1) :=
  compose localDevice (first countData boolData)
noncomputable def selectArgsDevice : Device argsData (product countData edgesData) (fun p : Args => (p.2.1,p.1)) :=
  fanout addressDevice (first edgesData (product countData boolData))
noncomputable def selectedDevice : Device argsData (listTree Graph.edgeData) (fun p : Args => select (p.2.1,p.1)) :=
  @compose Args (Count × Edges) (List Graph.Edge) argsData (product countData edgesData)
    (listTree Graph.edgeData) (fun p => (p.2.1,p.1)) select selectArgsDevice selectDevice
noncomputable def vertexDevice : Device argsData Graph.vertexData (fun p : Args => vertex p.1 p.2) :=
  fanout ownerDevice (compose selectedDevice nonemptyDevice)

theorem testArgs_linear : LinearCost testArgsDevice :=
  LinearCost.fanout (LinearCost.first _ _) (LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _))
theorem test_polynomial : PolynomialCost testDevice := PolynomialCost.compose testArgs_linear.polynomial CountTest.polynomial
theorem select_polynomial : PolynomialCost selectDevice :=
  PolynomialCost.compose (EnvFilter.polynomial test_polynomial) (PolynomialCost.map (LinearCost.second _ _).polynomial)
theorem nonempty_linear : LinearCost nonemptyDevice := LinearCost.fanout (LinearCost.head _ _) (LinearCost.tail _)
theorem local_linear : LinearCost localDevice := LinearCost.second _ _
theorem owner_linear : LinearCost ownerDevice :=
  LinearCost.compose (LinearCost.compose local_linear (LinearCost.second _ _)) Multiply.rawTest_linear
theorem address_linear : LinearCost addressDevice := LinearCost.compose local_linear (LinearCost.first _ _)
theorem selectArgs_linear : LinearCost selectArgsDevice := LinearCost.fanout address_linear (LinearCost.first _ _)
theorem selected_polynomial : PolynomialCost selectedDevice := PolynomialCost.compose selectArgs_linear.polynomial select_polynomial
theorem vertex_polynomial : PolynomialCost vertexDevice :=
  PolynomialCost.fanout owner_linear.polynomial (PolynomialCost.compose selected_polynomial nonempty_linear.polynomial)
end MeanPayoff.TreeDevice.Adjacency
namespace MeanPayoff.TreeDevice.Rows
open BinaryData
abbrev Edges := List Edge
abbrev Count := Median.Count
abbrev Arena := ArenaRead.Arena
abbrev State := StreamFold.State Edges Graph.Vertex (List Bool)

def ownersData := listTree boolData
def countData := listTree Median.unitData
def edgesData := listTree EdgeRead.edgeData
def outputData := listTree Graph.vertexData
def rowArgsData := product edgesData ownersData
def rowOutputData := product Graph.vertexData ownersData
def stateData := StreamFold.stateData edgesData Graph.vertexData ownersData

def count (xs : List Bool) : Count := xs.map (fun _ => ())
noncomputable def countDevice : Device ownersData countData count :=
  Map.device (constant boolData Median.unitData ())

def row (p : Edges × List Bool) : Graph.Vertex × List Bool :=
  (Adjacency.vertex p.1 (count p.2.tail,p.2.headD false),p.2.tail)
noncomputable def streamDevice : Device rowArgsData ownersData (fun p : Edges × List Bool => p.2) := second edgesData ownersData
noncomputable def remainderDevice : Device rowArgsData ownersData (fun p : Edges × List Bool => p.2.tail) :=
  compose streamDevice (Tail.device boolData)
noncomputable def addressDevice : Device rowArgsData countData (fun p : Edges × List Bool => count p.2.tail) :=
  compose remainderDevice countDevice
noncomputable def ownerDevice : Device rowArgsData boolData (fun p : Edges × List Bool => p.2.headD false) :=
  compose streamDevice (Head.device boolData false)
noncomputable def vertexArgsDevice : Device rowArgsData Adjacency.argsData
    (fun p : Edges × List Bool => (p.1,(count p.2.tail,p.2.headD false))) :=
  fanout (first edgesData ownersData) (fanout addressDevice ownerDevice)
noncomputable def vertexDevice : Device rowArgsData Graph.vertexData
    (fun p : Edges × List Bool => Adjacency.vertex p.1 (count p.2.tail,p.2.headD false)) :=
  compose vertexArgsDevice Adjacency.vertexDevice
noncomputable def rowDevice : Device rowArgsData rowOutputData row := fanout vertexDevice remainderDevice

def descending (edges : Edges) : List Bool → List Graph.Vertex
  | [] => []
  | b::bs => Adjacency.vertex edges (List.replicate bs.length (),b)::descending edges bs

def build (z : Arena) : List Graph.Vertex :=
  (Fold.fold (StreamFold.step row) (z.2.2,([],z.2.1.reverse)) z.1).2.1
noncomputable def restDevice : Device ArenaRead.arenaData (product ownersData edgesData) (fun z : Arena => z.2) := second countData (product ownersData edgesData)
noncomputable def edgesDevice : Device ArenaRead.arenaData edgesData (fun z : Arena => z.2.2) := compose restDevice (second ownersData edgesData)
noncomputable def ownersDevice : Device ArenaRead.arenaData ownersData (fun z : Arena => z.2.1) := compose restDevice (first ownersData edgesData)
noncomputable def reversedDevice : Device ArenaRead.arenaData ownersData (fun z : Arena => z.2.1.reverse) :=
  compose ownersDevice (Lists.reverseDevice boolData)
noncomputable def stateDevice : Device ArenaRead.arenaData stateData (fun z : Arena => (z.2.2,([],z.2.1.reverse))) :=
  fanout edgesDevice (compose reversedDevice (Lists.nilPrefix ownersData Graph.vertexData))
noncomputable def initDevice : Device ArenaRead.arenaData (product stateData countData)
    (fun z : Arena => ((z.2.2,([],z.2.1.reverse)),z.1)) :=
  fanout stateDevice (first countData (product ownersData edgesData))
noncomputable def resultDevice : Device stateData outputData (fun s : State => s.2.1) :=
  compose (second edgesData (product outputData ownersData)) (first outputData ownersData)
noncomputable def foldedDevice : Device (product stateData countData) outputData
    (fun z : State × Count => (Fold.fold (StreamFold.step row) z.1 z.2).2.1) :=
  @compose (State × Count) State (List Graph.Vertex) (product stateData countData) stateData outputData
    (fun z => Fold.fold (StreamFold.step row) z.1 z.2) (fun s => s.2.1)
    (Fold.device (StreamFold.stepDevice rowDevice)) resultDevice
noncomputable def buildDevice : Device ArenaRead.arenaData outputData build :=
  @compose Arena (State × Count) (List Graph.Vertex) ArenaRead.arenaData (product stateData countData) outputData
    (fun z => ((z.2.2,([],z.2.1.reverse)),z.1)) (fun z => (Fold.fold (StreamFold.step row) z.1 z.2).2.1)
    initDevice foldedDevice

theorem count_polynomial : PolynomialCost countDevice := PolynomialCost.map (LinearCost.constant _ _ _).polynomial
theorem stream_linear : LinearCost streamDevice := LinearCost.second _ _
theorem remainder_linear : LinearCost remainderDevice := LinearCost.compose stream_linear (LinearCost.tail _)
theorem address_polynomial : PolynomialCost addressDevice := PolynomialCost.compose remainder_linear.polynomial count_polynomial
theorem owner_linear : LinearCost ownerDevice := LinearCost.compose stream_linear (LinearCost.head _ _)
theorem vertexArgs_polynomial : PolynomialCost vertexArgsDevice :=
  PolynomialCost.fanout (LinearCost.first _ _).polynomial (PolynomialCost.fanout address_polynomial owner_linear.polynomial)
theorem vertex_polynomial : PolynomialCost vertexDevice := PolynomialCost.compose vertexArgs_polynomial Adjacency.vertex_polynomial
theorem row_polynomial : PolynomialCost rowDevice := PolynomialCost.fanout vertex_polynomial remainder_linear.polynomial

theorem fold_polynomial : PolynomialCost (Fold.device (StreamFold.stepDevice rowDevice)) := by
  apply StreamFold.polynomial rowDevice row_polynomial
  intro edges owners
  change treeSize (ownersData owners.tail)≤treeSize (ownersData owners)
  cases owners <;> simp only [ownersData,List.tail_nil,List.tail_cons,listTree,treeSize_pair] <;> omega

theorem rest_linear : LinearCost restDevice := LinearCost.second _ _
theorem edges_linear : LinearCost edgesDevice := LinearCost.compose rest_linear (LinearCost.second _ _)
theorem owners_linear : LinearCost ownersDevice := LinearCost.compose rest_linear (LinearCost.first _ _)
theorem reversed_polynomial : PolynomialCost reversedDevice := PolynomialCost.compose owners_linear.polynomial (PolynomialCost.reverse _)
theorem state_polynomial : PolynomialCost stateDevice :=
  PolynomialCost.fanout edges_linear.polynomial (PolynomialCost.compose reversed_polynomial (LinearCost.nilPrefix _ _).polynomial)
theorem init_polynomial : PolynomialCost initDevice := PolynomialCost.fanout state_polynomial (LinearCost.first _ _).polynomial
theorem result_linear : LinearCost resultDevice := LinearCost.compose (LinearCost.second _ _) (LinearCost.first _ _)
theorem folded_polynomial : PolynomialCost foldedDevice := PolynomialCost.compose fold_polynomial result_linear.polynomial
theorem build_polynomial : PolynomialCost buildDevice := PolynomialCost.compose init_polynomial folded_polynomial

end MeanPayoff.TreeDevice.Rows
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_EncodedArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

def VectorRep {n : ℕ} (v : Fin n → ℤ) (xs : List W) : Prop :=
  ∃ ws : Fin n → W, xs=List.ofFn ws ∧ ∀ i, (ws i).val=v i

namespace RawBudget

structure Rep {n : ℕ} (P : Budgets n) (p : Data) : Prop where
  kn_pos : 0<p.1.1.val
  kd_pos : 0<p.1.2.val
  mn_pos : 0<p.2.1.1.val
  md_pos : 0<p.2.1.2.val
  k_eq : P.k=(p.1.1.val:ℚ)/(p.1.2.val:ℚ)
  m_eq : P.m=(p.2.1.1.val:ℚ)/(p.2.1.2.val:ℚ)
  coords : ∃ a b : Fin n → W,
    p.2.2.1=List.ofFn a ∧ p.2.2.2=List.ofFn b ∧
    (∀ i, 0<(a i).val) ∧ (∀ i, 0<(b i).val) ∧
    (∀ i, P.alpha i=1/((a i).val:ℚ)) ∧ (∀ i, P.beta i=1/((b i).val:ℚ))

end RawBudget
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_FiniteIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace RawBox

structure Rep {n B : ℕ} (I : SolveBox n B) (b : Data) : Prop where
  width : b.1.val=I.width
  lower : VectorRep I.a b.2.1
  upper : VectorRep I.b b.2.2

end RawBox
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_SizeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Word
theorem unsignedMul_length (x y : W) : (unsignedMul (x,y)).digits.length≤x.digits.length+2*y.digits.length := by
  have h := Multiply.fold_length (x,Median.zeroWord) y.digits.reverse
  change (Multiply.multiply (x,y.digits)).digits.length≤_
  simpa only [Multiply.multiply,List.length_reverse,show Median.zeroWord.digits.length=0 from rfl,zero_max] using h
theorem mul_length (x y : W) : (mul (x,y)).digits.length≤x.digits.length+2*y.digits.length+6 := by
  change (if y.sign then neg (unsignedMul (x,neg y)) else unsignedMul (x,y)).digits.length≤_
  split
  · have h := unsignedMul_length x (neg y)
    rw [neg_length] at h
    rw [neg_length]
    omega
  · have h := unsignedMul_length x y
    omega
theorem shiftRight_length (x : W) (c : Count) : (shiftRight (x,c)).digits.length≤x.digits.length := by
  change (Fold.fold shiftStep.eval x c).digits.length≤_
  induction c generalizing x with
  | nil => exact le_rfl
  | cons u cs ih =>
    have h := ih (half x)
    change (Fold.fold shiftStep.eval (half x) cs).digits.length≤_
    exact h.trans (by rw [half_length]; omega)
end Word
namespace Array
 theorem Bounded.mono {xs : List W} {M N : ℕ} (h : Bounded xs M) (hm : M≤N) : Bounded xs N :=
  fun _ hw => (h _ hw).trans hm
 theorem Bounded.nil (M : ℕ) : Bounded [] M := by simp [Bounded]
 theorem Bounded.cons {x : W} {xs : List W} {M : ℕ} (hx : x.digits.length≤M) (hs : Bounded xs M) : Bounded (x::xs) M := by
  intro y hy; rcases List.mem_cons.mp hy with rfl | hy
  · exact hx
  · exact hs y hy
 theorem bounded_zip_general {xs ys : List W} {M N P : ℕ} (hx : Bounded xs M) (hy : Bounded ys N)
    (f : Code (W×W) W) (hf : ∀ x y, x.digits.length≤M → y.digits.length≤N → (f (x,y)).digits.length≤P) :
    Bounded (zip zero zero f (xs,ys)) P := by
  change Bounded (Zip.zip f.eval zero xs ys) P
  induction xs generalizing ys with
  | nil => exact Bounded.nil _
  | cons x xs ih =>
    have hxs : Bounded xs M := fun w hw => hx w (List.mem_cons_of_mem _ hw)
    cases ys with
    | nil =>
      exact Bounded.cons (hf x zero (hx x (by simp)) (Nat.zero_le _)) (ih hxs (Bounded.nil _))
    | cons y ys =>
      exact Bounded.cons (hf x y (hx x (by simp)) (hy y (by simp)))
        (ih hxs (fun w hw => hy w (List.mem_cons_of_mem _ hw)))
 theorem average_bound {xs ys : List W} {M : ℕ} (hx : Bounded xs M) (hy : Bounded ys M) : Bounded (average (xs,ys)) M :=
  bounded_zip_general hx hy Word.average (by intro x y hx hy; rw [Word.average_length]; omega)
 theorem translate_bound {x : W} {xs : List W} {M : ℕ} (hx : x.digits.length≤M) (hs : Bounded xs M) : Bounded (translate (x,xs)) (M+1) := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  change (Word.add (x,v)).digits.length≤M+1
  rw [Word.add_length]
  have := hs v hv
  omega
 theorem Bounded.headD {xs : List W} {M : ℕ} (h : Bounded xs M) : (xs.headD zero).digits.length≤M := by
  cases xs with
  | nil => exact Nat.zero_le _
  | cons x xs => exact h x (by simp)
end Array
end MeanPayoff.TreeDevice.Certified

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Array
structure Small (n M : ℕ) (xs : List W) : Prop where
  length : xs.length≤n
  digits : Bounded xs M
 theorem Small.mono {n M N : ℕ} {xs : List W} (h : Small n M xs) (hm : M≤N) : Small n N xs := ⟨h.length,h.digits.mono hm⟩
 theorem Small.nil (n M : ℕ) : Small n M [] := ⟨Nat.zero_le _,Bounded.nil _⟩
 theorem Small.zip {n M : ℕ} {xs ys : List W} (hx : Small n M xs) (hy : Small n M ys)
    (f : Code (W×W) W) (hf : ∀ z, f z=z.1 ∨ f z=z.2) : Small n M (zip zero zero f (xs,ys)) :=
  ⟨(zip_length f.eval zero xs ys).le.trans hx.length,bounded_zip hx.digits hy.digits f hf⟩
 theorem Small.min {n M : ℕ} {xs ys : List W} (hx : Small n M xs) (hy : Small n M ys) : Small n M (min (xs,ys)) := hx.zip hy Word.min EdgeScan.low_mem
 theorem Small.max {n M : ℕ} {xs ys : List W} (hx : Small n M xs) (hy : Small n M ys) : Small n M (max (xs,ys)) := hx.zip hy Word.max EdgeScan.high_mem
 theorem Small.average {n M : ℕ} {xs ys : List W} (hx : Small n M xs) (hy : Small n M ys) : Small n M (average (xs,ys)) :=
  ⟨(zip_length Word.average.eval zero xs ys).le.trans hx.length,average_bound hx.digits hy.digits⟩
 theorem Small.translate {n M : ℕ} {w : W} {xs : List W} (hw : w.digits.length≤M) (hx : Small n M xs) : Small n (M+1) (translate (w,xs)) :=
  ⟨by change (xs.map _).length≤n; simpa only [List.length_map] using hx.length,translate_bound hw hx.digits⟩
 theorem Small.getD {n M : ℕ} {xss : List (List W)} (h : ∀ xs∈xss, Small n M xs) (i : ℕ)
    {d : List W} (hd : Small n M d) : Small n M (xss.getD i d) := by
  induction xss generalizing i with
  | nil => exact hd
  | cons xs xss ih => cases i with
    | zero => exact h xs (by simp)
    | succ i => exact ih (fun ys hy => h ys (by simp [hy])) i
 theorem Small.doubleOn {n M : ℕ} {xs : List W} (h : Small n M xs) (bs : List Bool) : Small n (M+1) (doubleOn (xs,bs)) := by
  refine ⟨(zip_length _ false xs bs).le.trans h.length,?_⟩
  change Bounded (Zip.zip _ false xs bs) (M+1)
  have all : ∀ xs bs, Bounded xs M → Bounded (Zip.zip (Code.branch snd (fst.comp Word.double) fst).eval false xs bs) (M+1) := by
    intro xs
    induction xs with
    | nil => intro bs _; exact Bounded.nil _
    | cons x xs ih =>
      intro bs hx
      cases bs with
      | nil =>
        apply Bounded.cons
        · exact (hx x (by simp)).trans (by omega)
        · exact ih [] (fun y hy => hx y (by simp [hy]))
      | cons b bs =>
        apply Bounded.cons
        · change (if b then Word.double x else x).digits.length≤M+1
          split
          · rw [Word.double_length]; have := hx x (by simp); omega
          · exact (hx x (by simp)).trans (by omega)
        · exact ih bs (fun y hy => hx y (by simp [hy]))
  exact all xs bs h.digits
end Array
namespace RawBudget
structure Small (n M : ℕ) (p : Data) : Prop where
  kn : p.1.1.digits.length≤M
  kd : p.1.2.digits.length≤M
  mn : p.2.1.1.digits.length≤M
  md : p.2.1.2.digits.length≤M
  alpha : Array.Small n M p.2.2.1
  beta : Array.Small n M p.2.2.2
 theorem Small.mono {n M N : ℕ} {p : Data} (h : Small n M p) (hm : M≤N) : Small n N p :=
  ⟨h.kn.trans hm,h.kd.trans hm,h.mn.trans hm,h.md.trans hm,h.alpha.mono hm,h.beta.mono hm⟩
 theorem times_length (r : ℤ) (w : W) : (times r w).digits.length≤w.digits.length+2*(EdgeRead.encodedWord r).digits.length+6 := Word.mul_length _ _
 theorem encodedWord_length_nonneg (r : ℤ) (hr : 0 ≤ r) : (EdgeRead.encodedWord r).digits.length=(r.natAbs+1).bits.length+1 := by
  rw [EdgeRead.encodedWord,ite_eq_right (by omega)]
  change (Word.add (IntegerRead.positive _,IntegerRead.minusOne)).digits.length=_
  rw [Word.add_length]
  simp [IntegerRead.positive,IntegerRead.minusOne]
 theorem constant_short (r : ℤ) (hr : r=3 ∨ r=4 ∨ r=5) : (EdgeRead.encodedWord r).digits.length≤4 := by
  rcases hr with rfl | rfl | rfl <;> rw [encodedWord_length_nonneg _ (by omega)] <;> decide
 theorem times_short {M : ℕ} {w : W} (h : w.digits.length≤M) (r : ℤ) (hr : (EdgeRead.encodedWord r).digits.length≤4) :
    (times r w).digits.length≤M+14 := by have := times_length r w; omega
 theorem Small.reduceK {n M : ℕ} {p : Data} (h : Small n M p) : Small n (M+14) (reduceK p) := by
  refine ⟨times_short h.kn 4 (constant_short 4 (by tauto)),times_short h.kd 5 (constant_short 5 (by tauto)),h.mn.trans (by omega),h.md.trans (by omega),h.alpha.mono (by omega),h.beta.mono (by omega)⟩
 theorem Small.reduceM {n M : ℕ} {p : Data} (h : Small n M p) : Small n (M+14) (reduceM p) := by
  refine ⟨h.kn.trans (by omega),h.kd.trans (by omega),times_short h.mn 4 (constant_short 4 (by tauto)),times_short h.md 5 (constant_short 5 (by tauto)),h.alpha.mono (by omega),h.beta.mono (by omega)⟩
 theorem Small.reweightK {n M : ℕ} {p : Data} (h : Small n M p) (bs : List Bool) : Small n (M+14) (reweightK (p,bs)) := by
  refine ⟨times_short h.kn 3 (constant_short 3 (by tauto)),times_short h.kd 5 (constant_short 5 (by tauto)),h.mn.trans (by omega),h.md.trans (by omega),(h.alpha.doubleOn bs).mono (by omega),h.beta.mono (by omega)⟩
 theorem Small.reweightM {n M : ℕ} {p : Data} (h : Small n M p) (bs : List Bool) : Small n (M+14) (reweightM (p,bs)) := by
  refine ⟨h.kn.trans (by omega),h.kd.trans (by omega),times_short h.mn 3 (constant_short 3 (by tauto)),times_short h.md 5 (constant_short 5 (by tauto)),h.alpha.mono (by omega),(h.beta.doubleOn bs).mono (by omega)⟩
end RawBudget
namespace RawBox
structure Small (n M : ℕ) (b : Data) : Prop where
  width : b.1.digits.length≤M
  lower : Array.Small n M b.2.1
  upper : Array.Small n M b.2.2
 theorem Small.mono {n M N : ℕ} {b : Data} (h : Small n M b) (hm : M≤N) : Small n N b := ⟨h.width.trans hm,h.lower.mono hm,h.upper.mono hm⟩
 theorem Small.midpoint {n M : ℕ} {b : Data} (h : Small n M b) : Array.Small n M (midpoint b) := h.lower.average h.upper
 theorem Small.withFloor {n M : ℕ} {b : Data} (h : Small n M b) {xs : List W} (hx : Array.Small n M xs) : Small n M (withFloor (b,xs)) := ⟨h.width,hx,h.upper⟩
 theorem Small.withCeiling {n M : ℕ} {b : Data} (h : Small n M b) {xs : List W} (hx : Array.Small n M xs) : Small n M (withCeiling (b,xs)) := ⟨h.width,h.lower,hx⟩
 theorem Small.clip {n M : ℕ} {b : Data} (h : Small n M b) {xs : List W} (hx : Array.Small n M xs) : Array.Small n M (clip (b,xs)) := h.upper.min (h.lower.max hx)
 theorem Small.averageClipped {n M : ℕ} {b : Data} (h : Small n M b) {xs ys : List W} (hx : Array.Small n M xs) (hy : Array.Small n M ys) : Array.Small n M (averageClipped (b,xs,ys)) := h.clip (hx.average hy)
 theorem centered_small {n M : ℕ} {w : W} (hw : w.digits.length≤M) {xs : List W} (hx : Array.Small n M xs) : Small n (M+3) (centered (w,xs)) := by
  refine ⟨?_,?_,(Array.Small.translate hw hx).mono (by omega)⟩
  · change (Word.double w).digits.length≤_; rw [Word.double_length]; omega
  · apply Array.Small.translate
    · change (Word.neg w).digits.length≤M+2; rw [Word.neg_length]; omega
    · exact hx.mono (by omega)
 theorem Small.capLow {n M : ℕ} {b : Data} (h : Small n M b) {w : W} (hw : w.digits.length≤M) : Small n (M+1) (capLow (b,w)) :=
  ⟨hw.trans (by omega),h.lower.mono (by omega),(h.upper.mono (by omega)).min (Array.Small.translate hw h.lower)⟩
 theorem Small.capHigh {n M : ℕ} {b : Data} (h : Small n M b) {w : W} (hw : w.digits.length≤M) : Small n (M+3) (capHigh (b,w)) := by
  refine ⟨hw.trans (by omega),?_,h.upper.mono (by omega)⟩
  apply (h.lower.mono (by omega)).max
  apply Array.Small.translate
  · change (Word.neg w).digits.length≤M+2; rw [Word.neg_length]; omega
  · exact h.upper.mono (by omega)
end RawBox
end MeanPayoff.TreeDevice.Certified

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Array
 theorem choose_bound {as bs : List W} {M : ℕ} (ha : Bounded as M) (hb : Bounded bs M) (hs : List Bool) :
    Bounded (choose (hs,as,bs)) M := by
  induction hs generalizing as bs with
  | nil => exact Bounded.nil _
  | cons c cs ih =>
    cases as with
    | nil =>
      change Bounded ((if c then zero else zero)::choose (cs,[],bs)) M
      exact Bounded.cons (by cases c <;> exact Nat.zero_le _) (ih (Bounded.nil _) hb)
    | cons a as =>
      cases bs with
      | nil =>
        apply Bounded.cons
        · change (if c then a else zero).digits.length≤M
          cases c
          · exact Nat.zero_le _
          · exact ha a (by simp)
        · exact ih (fun w hw => ha w (by simp [hw])) (Bounded.nil _)
      | cons b bs =>
        apply Bounded.cons
        · change (if c then a else b).digits.length≤M
          cases c
          · exact hb b (by simp)
          · exact ha a (by simp)
        · exact ih (fun w hw => ha w (by simp [hw])) (fun w hw => hb w (by simp [hw]))
 theorem choose_small {as bs : List W} {n M : ℕ} (ha : Small n M as) (hb : Small n M bs) (hs : List Bool) (hl : hs.length≤n) :
    Small n M (choose (hs,as,bs)) :=
  ⟨(zip_length _ _ hs _).le.trans hl,choose_bound ha.digits hb.digits hs⟩
end Array

end MeanPayoff.TreeDevice.Certified

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_DriverExecution
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack _root_.OAI.MeanPayoff.TreeDevice.Certified.instEncodingParsed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Size
theorem list_bound {α : Type} [Encoding α] {xs : List α} {M : ℕ}
    (h : ∀ x∈xs, treeSize (encode x)≤M) : treeSize (encode xs)≤xs.length*(M+1)+1 := by
  induction xs with
  | nil => change 1≤0*(M+1)+1; omega
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    change treeSize (listTree encode (x::xs))≤_
    rw [listTree,treeSize_pair,List.length_cons]
    change treeSize (listTree encode xs)≤_ at ht
    nlinarith
end Size

end MeanPayoff.TreeDevice.Certified

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_InputCode
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Size
 theorem count (xs : Count) : treeSize (encode xs)=2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change treeSize (Data.pair .nil (encode xs))=_
    rw [treeSize_pair,treeSize_nil,ih,List.length_cons]
    omega
end Size
end MeanPayoff.TreeDevice.Certified

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Word

theorem half_size (w : W) : treeSize (encode (half w)) ≤ treeSize (encode w) := by
  change treeSize (wordData (Halve.halve w)) ≤ treeSize (wordData w)
  rcases w with ⟨s,ds⟩
  cases ds with
  | nil => exact le_rfl
  | cons b bs =>
    simp only [Halve.halve,wordData,listData,List.tail_cons,treeSize_pair]
    omega
end Word
namespace NaturalLog
noncomputable def loop : Code (State×Count) State := fold step (by
  rintro ⟨w,c⟩ u
  rw [step_eval]
  dsimp only
  split
  · rw [Size.pair,Size.pair,Size.count,Size.count,List.length_cons]
    have := Word.half_size w
    change _ ≤ _+1+1
    omega
  · omega)
noncomputable def length : Code W Count :=
  (((Code.id ⋏ₚ const []) ⋏ₚ Word.digitCount) ≫ₚ loop) ≫ₚ snd

noncomputable def ceil : Code W Count :=
  ((Code.id ⋏ₚ Word.constant 1) ≫ₚ Word.sub) ≫ₚ length

end NaturalLog
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Word
noncomputable def powerStep : Code (W×Unit) W := fst ≫ₚ double
noncomputable def powerFold : Code (W×Count) W := fold powerStep (by
  intro w u
  change treeSize (wordData (Multiply.double w)) ≤ treeSize (wordData w)+1+1
  simp only [Multiply.double,SignedBits.cons,wordData,listData,treeSize_pair,boolData,treeSize_nil]
  omega)
noncomputable def power : Code Count W := (Word.constant 1 ⋏ₚ Code.id) ≫ₚ powerFold

end Word
namespace Counter

theorem false_data (cs : Count) : listTree boolData (cs.map (fun _ => false))=encode cs := by
  induction cs with
  | nil => rfl
  | cons u us ih =>
    change Data.pair .nil (listTree boolData (us.map (fun _ => false))) = Data.pair .nil (encode us)
    rw [ih]

noncomputable def bounded : Code (W×Count) Count := by
  refine ⟨fun z => Address.read (z.1,z.2.map (fun _ => false)),
    Address.device.recode encode encode (fun z : W×Count => (z.1,z.2.map (fun _ => false)))
      (fun z => Address.read (z.1,z.2.map (fun _ => false))) ?_ (fun _ => rfl), ?_⟩
  · intro z
    change Data.pair (encode z.1) (listTree boolData (z.2.map (fun _ => false)))=Data.pair (encode z.1) (encode z.2)
    rw [false_data]
  · obtain ⟨K,d,h⟩ := Address.polynomial
    refine ⟨K,d,fun z => ?_⟩
    have hh := h (z.1,z.2.map (fun _ => false))
    change Address.device.limit (z.1,z.2.map (fun _ => false)) ≤ K*(treeSize (product wordData (listTree Median.unitData) z)+1)^d
    change Address.device.limit (z.1,z.2.map (fun _ => false)) ≤ K*(treeSize (Data.pair (wordData z.1) (listTree boolData (z.2.map (fun _ => false))))+1)^d at hh
    rw [false_data] at hh
    exact hh
noncomputable def power : Code (Count×Count) Count := ((fst ≫ₚ Word.power) ⋏ₚ snd) ≫ₚ bounded
end Counter
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair

namespace InputCode
noncomputable def parse : Code Digits Parsed := by
  refine ⟨fun d => ⟨Normalize.read d.bits⟩, Normalize.device.recode encode encode Digits.bits
    (fun d => (⟨Normalize.read d.bits⟩ : Parsed)) (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := Normalize.polynomial
  exact ⟨K,d,fun z => h z.bits⟩
noncomputable def edges : Code Parsed (List EdgeRead.Edge) := by
  refine ⟨fun p => p.raw.2.2, Normalize.edgesDevice.recode encode encode Parsed.raw (fun p => p.raw.2.2)
    (fun _ => rfl) (fun _ => rfl), ?_⟩
  have hc : PolynomialCost Normalize.edgesDevice :=
    (LinearCost.compose (LinearCost.second _ _) (LinearCost.second _ _)).polynomial
  obtain ⟨K,d,h⟩ := hc
  exact ⟨K,d,fun p => h p.raw⟩
noncomputable def rows : Code Parsed RawBasic.Arena := by
  refine ⟨fun p => Rows.build p.raw, Rows.buildDevice.recode encode encode Parsed.raw (fun p => Rows.build p.raw)
    (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := Rows.build_polynomial
  exact ⟨K,d,fun p => h p.raw⟩

noncomputable def absolute : Code W W := (Code.id ⋏ₚ Word.neg) ≫ₚ Word.max
noncomputable def maximumFold : Code (W×List W) W := fold Word.max (by
  intro w x
  change treeSize (wordData (Order.high (w,x))) ≤ treeSize (wordData w)+treeSize (wordData x)+1
  unfold Order.high
  split <;> dsimp only [Prod.fst,Prod.snd] <;> omega)
noncomputable def maximum : Code (List W) W := (Word.constant 1 ⋏ₚ Code.id) ≫ₚ maximumFold
noncomputable def bound : Code Parsed W := edges ≫ₚ map (snd ≫ₚ snd ≫ₚ absolute) ≫ₚ maximum
noncomputable def width : Code Parsed W := (((n ≫ₚ Counter.word) ⋏ₚ bound) ≫ₚ Word.mul) ≫ₚ RawBudget.times 8

end InputCode
end MeanPayoff.TreeDevice.Certified
end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Allocation
attribute [-instance] _root_.OAI.MeanPayoff.TreeDevice.Certified.RawControl.instEncodingPack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Allocation
noncomputable def double : Code (Count×Unit) Count := (fst ⋏ₚ fst) ≫ₚ Counter.add
noncomputable def init : Code Count (Count×Count) := const [()] ⋏ₚ Code.id
noncomputable def device : Device encode encode (fun cs : Count => Fold.fold double.eval [()] cs) :=
  @compose Count (Count×Count) Count encode encode encode init.eval (fun z => Fold.fold double.eval z.1 z.2) init.device (Fold.device double.device)

end Allocation
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.MeanPayoff_Realizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RegisterBits.Sequence5
open BinaryData.Take (advance_add)
variable (P Q : Program 5)
def flow : Flow.Program 5 where
  nodes := 2
  start := 0
  block := ![P,Q]
  read _ := 0
  next p _ _ := if p=0 then some ⟨1,.keep,none⟩ else none
noncomputable def program : Program 5 := Flow.compile (flow P Q)
end MeanPayoff.RegisterBits.Sequence5

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Orientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace Counter

theorem canonical (c : Count) : c=List.replicate c.length () :=
  List.eq_replicate_of_mem (fun _ _ => Subsingleton.elim _ _)

theorem enumLoop_eq (c : Count) (acc : List Count) :
    enumLoop (((),acc,c),c)=((),(List.range c.length).map (fun i => List.replicate i ())++acc,[]) := by
  change Fold.fold (StreamFold.step enumRow.eval) ((),acc,c) c=_
  induction c generalizing acc with
  | nil => rfl
  | cons u cs ih =>
    change Fold.fold (StreamFold.step enumRow.eval) ((),cs::acc,cs) cs=_
    rw [ih]
    simp only [List.length_cons,List.range_succ,List.map_append,List.map_cons,List.map_nil,List.append_assoc,
      List.cons_append,List.nil_append]
    rw [←canonical cs]

theorem enum_eq (c : Count) : enum c=(List.range c.length).map (fun i => List.replicate i ()) := by
  change (enumLoop (((),[],c),c)).2.1=_
  rw [enumLoop_eq,List.append_nil]

end Counter

def VectorsRep {n : ℕ} (vs : List (Fin n→ℤ)) (xss : List (List W)) : Prop :=
  List.Forall₂ VectorRep vs xss

end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code

namespace RawOrientation
def Rep {n : ℕ} {P : Budgets n} (O : Orientation P) (o : Data) : Prop :=
  o.1=O.chooseY ∧ List.Forall₂ (fun H hs => MaskRep H.val hs) O.exceptions o.2
def ManyRep {n : ℕ} {P : Budgets n} (os : List (Orientation P)) (rs : List Data) : Prop :=
  List.Forall₂ Rep os rs

end RawOrientation
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Control
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.SourceControl

def sampledResume {G : Game} {B : ℕ} {A C R : Result G B} (f : Frame G B A C) (v : A.Value)
    (k : Kont G B C R) (j : ℕ) : State G B R :=
  match f with
  | .trialsHead P I J => (.call (.trials P I J) (.push (.vectorCons v) k))
  | .vectorCons a => (.ret k (a :: v))
  | .median I => (.ret k (I.medianBox v))
  | .centerFirst P _ I hB q =>
      (.call (.ask P.reduceM (I.narrowCentered hB q.val)) (.push (.centerSecond I hB q v) k))
  | .centerSecond I _ _ r => (.ret k (I.averageClipped r.val v.val))
  | .centersHead P hR I hB t q =>
      (.call (.centers P hR I hB t v) (.push (.vectorCons q) k))
  | .orientLoop P hR I hB =>
      let H := PositiveDisplacement I (v.getD (globalS B) I.midpoint)
      let N := NegativeDisplacement I (v.getD (globalS B) I.midpoint)
      if hH : 1 / 2 < P.measure H then
        (.ret k ⟨true, [⟨Hᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩)
      else if hN : 1 / 2 < P.measure N then
        (.ret k ⟨false, [⟨Nᶜ, by rw [P.measure_compl G.positive]; linarith⟩]⟩)
      else
        .call (.orient P hR (I.wideCentered hB (v.getD j I.midpoint).val))
            (.push (.orientTail ⟨H, le_of_not_gt hH⟩ ⟨N, le_of_not_gt hN⟩) k)
  | .orientTail H N => (.ret k ⟨v.chooseY, v.exceptions ++ [H, N]⟩)
  | .orientHead P hR I J => (.call (.orientTrials P hR I J) (.push (.orientCons v) k))
  | .orientCons O => (.ret k (O :: v))
  | .combine _ => (.ret k (combineOrientations v))
  | .tightenFirst P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ v.val i - I.a i then
        (.call (.tighten P hR (I.withFloor v) hB) (.push (.floor I v) k))
      else (.call (.ask P.reduceM I) (.push (.tightenSecond P hR I hB) k))
  | .tightenSecond P hR I hB =>
      if _ : ∃ i, (I.delta : ℤ) ≤ I.b i - v.val i then
        (.call (.tighten P hR (I.withCeiling v) hB) (.push (.ceiling I v) k))
      else (.ret k ⟨I, rfl, le_refl _, le_refl _⟩)
  | .floor _ q => (.ret k ⟨v.box, v.width_eq, q.property.1.trans v.floor_le, v.ceiling_le⟩)
  | .ceiling _ q => (.ret k ⟨v.box, v.width_eq, v.floor_le, v.ceiling_le.trans q.property.2⟩)
  | .solveTight P hR _ hB =>
      have hK : 128 * globalS B < v.box.width := by rw [v.width_eq]; exact hB
      (.call (.orientPlus P hR v.box) (.push (.solveOriented P hR v.box hK) (.push (.includeInner v) k)))
  | .solveOriented P hR I hB =>
      (.call (.reweight P hR I v.chooseY v.exceptions) (.push (.solveReweighted P hR I hB v.chooseY) k))
  | .reweightHead P hR I side Hs => (.call (.reweight P hR I side Hs) (.push (.vectorCons v) k))
  | .solveReweighted P _ I hB side =>
      if side then (.call (.solve P (I.capHigh I.C I.C_positive (I.C_smaller hB).le)) (.push (.capHigh I hB v) k))
      else (.call (.solve P (I.capLow I.C I.C_positive (I.C_smaller hB).le)) (.push (.capLow I hB v) k))
  | .capHigh I hB rs => (.ret k (rs.foldl I.minVector (I.includeCapHigh I.C I.C_positive (I.C_smaller hB).le v)))
  | .capLow I hB rs => (.ret k (rs.foldl I.maxVector (I.includeCapLow I.C I.C_positive (I.C_smaller hB).le v)))
  | .includeInner T => (.ret k (T.include v))

def sampledStep {G : Game} {B : ℕ} {R : Result G B} (j : ℕ) : State G B R → State G B R
  | .ret .done v => (.ret .done v)
  | .ret (.push f k) v => sampledResume f v k j
  | .call job k => match job with
    | .solve P I => if hR : P.parameter < 1 then (.ret k (I.smallVector P))
        else if hB : I.width ≤ 128 * globalS B then (.ret k (I.exactVector G))
        else (.call (.tighten P (le_of_not_gt hR) I (by omega)) (.push (.solveTight P (le_of_not_gt hR) I (by omega)) k))
    | .ask P I => (.call (.trials P I (globalJ G.n B)) (.push (.median I) k))
    | .trials P I J => match J with
      | 0 => (.ret k [])
      | J + 1 => (.call (.solve P I) (.push (.trialsHead P I J) k))
    | .update P hR I hB q =>
        (.call (.ask P.reduceK (I.narrowCentered hB q.val)) (.push (.centerFirst P hR I hB q) k))
    | .centers P hR I hB t q => match t with
      | 0 => (.ret k [q])
      | t + 1 => (.call (.update P hR I hB q) (.push (.centersHead P hR I hB t q) k))
    | .orient P hR I =>
        if hB : I.width ≤ 128 * globalS B then (.ret k (orientBase G P I))
        else (.call (.centers P hR I (by omega) (globalS B) I.midpoint) (.push (.orientLoop P hR I (by omega)) k))
    | .orientTrials P hR I J => match J with
      | 0 => (.ret k [])
      | J + 1 => (.call (.orient P hR I) (.push (.orientHead P hR I J) k))
    | .orientPlus P hR I => (.call (.orientTrials P hR I (globalJ G.n B)) (.push (.combine P) k))
    | .tighten P hR I hB => (.call (.ask P.reduceK I) (.push (.tightenFirst P hR I hB) k))
    | .reweight P hR I side Hs => match Hs with
      | [] => (.ret k [])
      | H :: Hs =>
          (.call (.ask (if side then P.reweightM H.val else P.reweightK H.val) I)
            (.push (.reweightHead P hR I side Hs) k))

end MeanPayoff.SourceControl

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_ControlCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

abbrev VecsRep {n B : ℕ} (I : SolveBox n B) (vs : List (BoxVector I)) (rs : List (List W)) :=
  List.Forall₂ (fun v r => VectorRep v.val r) vs rs

structure EnvRep (G : Game) (B : ℕ) (e : Env) : Prop where
  graph : ∃ w : Fin G.m→W, e.1=Graph.codeVertices G w ∧ ∀ i, (w i).val=transformed G i
  exponent : e.2.1.length=sampleExponent B
  samples : e.2.2.1.length=globalS B
  trials : e.2.2.2.1.length=globalJ G.n B
  basic : G.n*(128*globalS B)≤e.2.2.2.2.length

def JobPackRep {G : Game} {B : ℕ} {A : SourceControl.Result G B} (j : SourceControl.Job G B A) (z : Pack) : Prop :=
  match j with
  | .solve P I | .ask P I | .orient P _ I | .orientPlus P _ I | .tighten P _ I _ =>
      RawBudget.Rep P z.p ∧ RawBox.Rep I z.b
  | .trials P I J | .orientTrials P _ I J => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.t.length=J
  | .update P _ I _ v => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ VectorRep v.val z.q
  | .centers P _ I _ t v => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.t.length=t ∧ VectorRep v.val z.q
  | .reweight P _ I side hs => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.o.1=side ∧
      List.Forall₂ (fun H r => MaskRep H.val r) hs z.o.2

def FramePackRep {G : Game} {B : ℕ} {A C : SourceControl.Result G B} (f : SourceControl.Frame G B A C) (z : Pack) : Prop :=
  match f with
  | .trialsHead P I J | .orientHead P _ I J => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.t.length=J
  | .vectorCons v => VectorRep v.val z.q
  | .median I => RawBox.Rep I z.b
  | .centerFirst P _ I _ v => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ VectorRep v.val z.q
  | .centerSecond I _ _ r => RawBox.Rep I z.b ∧ VectorRep r.val z.r
  | .centersHead P _ I _ t v => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.t.length=t ∧ VectorRep v.val z.q
  | .orientLoop P _ I _ | .tightenFirst P _ I _ | .tightenSecond P _ I _ |
    .solveTight P _ I _ | .solveOriented P _ I _ => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b
  | .orientTail H N => z.o.2.length=2 ∧ MaskRep H.val (z.o.2.headD []) ∧ MaskRep N.val (z.o.2.tail.headD [])
  | .orientCons O => RawOrientation.Rep O z.o
  | .combine _ | .includeInner _ => True
  | .floor _ _ | .ceiling _ _ => True
  | .reweightHead P _ I side hs => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.o.1=side ∧
      List.Forall₂ (fun H r => MaskRep H.val r) hs z.o.2
  | .solveReweighted P _ I _ side => RawBudget.Rep P z.p ∧ RawBox.Rep I z.b ∧ z.o.1=side
  | .capHigh I _ rs | .capLow I _ rs => VecsRep I rs z.vs

def ValueRep {G : Game} {B : ℕ} (A : SourceControl.Result G B) (v : A.Value) (z : Pack) : Prop :=
  match A,v with
  | .vector _,v => VectorRep v.val z.q
  | .vectors I,vs => VecsRep I vs z.vs
  | .orientation _,O => RawOrientation.Rep O z.o
  | .orientations _,Os => RawOrientation.ManyRep Os z.os
  | .inner _,T => RawBox.Rep T.box z.b

inductive KontRep {G : Game} {B : ℕ} : {A R : SourceControl.Result G B} → SourceControl.Kont G B A R → List Cell → Prop where
  | done {A} : KontRep (SourceControl.Kont.done (R:=A)) []
  | push {A C R} {f : SourceControl.Frame G B A C} {k : SourceControl.Kont G B C R} {c : Cell} {ks : List Cell}
      (tag : c.1.length=f.tag.val) (frame : FramePackRep f c.2) (tail : KontRep k ks) : KontRep (.push f k) (c::ks)

inductive StateRep {G : Game} {B : ℕ} {R : SourceControl.Result G B} : SourceControl.State G B R → State → Prop where
  | call {A} {j : SourceControl.Job G B A} {k : SourceControl.Kont G B A R} {c : Cell} {ks : List Cell}
      (tag : c.1.length=j.tag.val) (job : JobPackRep j c.2) (stack : KontRep k ks) : StateRep (.call j k) (c,ks)
  | ret {A} {k : SourceControl.Kont G B A R} {v : A.Value} {c : Cell} {ks : List Cell}
      (tag : c.1.length=10) (value : ValueRep A v c.2) (stack : KontRep k ks) : StateRep (.ret k v) (c,ks)

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

noncomputable def jobCode {G : Game} {B : ℕ} {A : SourceControl.Result G B} (j : SourceControl.Job G B A) : Code Input State :=
  match j with
  | .solve .. => solveCase | .ask .. => askCase | .trials .. => trialsCase | .update .. => updateCase
  | .centers .. => centersCase | .orient .. => orientCase | .orientTrials .. => orientTrialsCase
  | .orientPlus .. => orientPlusCase | .tighten .. => tightenCase | .reweight .. => reweightCase

end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

noncomputable def frameCode {G : Game} {B : ℕ} {A C : SourceControl.Result G B}
    (f : SourceControl.Frame G B A C) : Code Input State :=
  match f with
  | .trialsHead .. => trialsHeadCase | .vectorCons .. => vectorConsCase | .median .. => medianCase
  | .centerFirst .. => centerFirstCase | .centerSecond .. => centerSecondCase | .centersHead .. => centersHeadCase
  | .orientLoop .. => orientLoopCase | .orientTail .. => orientTailCase | .orientHead .. => orientHeadCase
  | .orientCons .. => orientConsCase | .combine .. => combineCase | .tightenFirst .. => tightenFirstCase
  | .tightenSecond .. => tightenSecondCase | .floor .. => boxPassCase | .ceiling .. => boxPassCase
  | .solveTight .. => solveTightCase | .solveOriented .. => solveOrientedCase | .reweightHead .. => reweightHeadCase
  | .solveReweighted .. => solveReweightedCase | .capHigh .. => capHighCase | .capLow .. => capLowCase
  | .includeInner .. => includeInnerCase

end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace RawBasic
 theorem fold_digits {g : Arena} {b : RawBox.Data} {E M : ℕ} (hg : ArenaBounded g E)
    (ha : Array.Bounded b.2.1 M) (hb : Array.Bounded b.2.2 M) (xs : List W) (cs : Count)
    (hx : Array.Bounded xs M) : Array.Bounded (Fold.fold advance.eval ((g,b),xs) cs).2 (M+cs.length*(E+1)) := by
  induction cs generalizing M xs with
  | nil => simpa only [Fold.fold,List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero] using hx
  | cons u cs ih =>
    have hn : Array.Bounded (next ((g,b),xs)) (M+(E+1)) :=
      clip_bound (ha.mono (by omega)) (hb.mono (by omega)) (by change Array.Bounded (graph (xs,g)) (M+(E+1)); simpa only [Nat.add_assoc] using graph_bound hx hg)
    have h := ih (ha.mono (by omega : M≤M+(E+1))) (hb.mono (by omega : M≤M+(E+1))) (next ((g,b),xs)) hn
    change Array.Bounded (Fold.fold advance.eval ((g,b),next ((g,b),xs)) cs).2 _
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [List.length_cons,Nat.add_mul,Nat.one_mul] ; omega)
 theorem solve_small {g : Arena} {b : RawBox.Data} {n E M : ℕ} (hg : ArenaBounded g E)
    (hb : RawBox.Small n M b) (cs : Count) : Array.Small n (M+cs.length*(E+1)) (solve ((g,b),cs)) := by
  refine ⟨?_,fold_digits hg hb.lower.digits hb.upper.digits b.2.1 cs hb.lower.digits⟩
  change (Fold.fold advance.eval ((g,b),b.2.1) cs).2.length≤n
  rw [(fold_layout (g,b) b.2.1 cs).2]
  split <;> first | exact hb.lower.length | exact hb.upper.length
end RawBasic
namespace Array
 theorem Small.foldMin {n M : ℕ} {xs : List W} {xss : List (List W)} (hx : Small n M xs) (hs : ∀ ys∈xss, Small n M ys) :
    Small n M (foldMin (xs,xss)) :=
  ⟨(fold_select_bound Word.min EdgeScan.low_mem hx.digits (fun ys hy => (hs ys hy).digits)).2.le.trans hx.length,
    (fold_select_bound Word.min EdgeScan.low_mem hx.digits (fun ys hy => (hs ys hy).digits)).1⟩
 theorem Small.foldMax {n M : ℕ} {xs : List W} {xss : List (List W)} (hx : Small n M xs) (hs : ∀ ys∈xss, Small n M ys) :
    Small n M (foldMax (xs,xss)) :=
  ⟨(fold_select_bound Word.max EdgeScan.high_mem hx.digits (fun ys hy => (hs ys hy).digits)).2.le.trans hx.length,
    (fold_select_bound Word.max EdgeScan.high_mem hx.digits (fun ys hy => (hs ys hy).digits)).1⟩
end Array
namespace RawBox
 theorem Small.smallVector {n M : ℕ} {b : Data} (hb : Small n M b) {p : RawBudget.Data} (hp : RawBudget.Small n M p) :
    Array.Small n M (smallVector (p,b)) := by
  apply Array.choose_small hb.upper hb.lower
  change (Zip.zip _ _ _ _).length≤n
  rw [Array.zip_length]
  change (p.2.2.2.map _).length≤n
  simpa only [List.length_map] using hp.beta.length
end RawBox
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Array
 theorem Bounded.nth {M : ℕ} {xs : List W} (h : Bounded xs M) (i : ℕ) : (xs.getD i zero).digits.length≤M := by
  induction xs generalizing i with
  | nil => exact Nat.zero_le _
  | cons x xs ih => cases i with
    | zero => exact h x (by simp)
    | succ i => exact ih (fun y hy => h y (by simp [hy])) i
end Array
namespace RawMedian
 theorem scalar_bound {M : ℕ} {xs : List W} (h : Array.Bounded xs M) : (scalar xs).digits.length≤M := by
  apply Array.Bounded.headD
  intro w hw
  exact h w ((Sort.sort_perm xs).mem_iff.mp (List.mem_of_mem_drop hw))
 theorem column_bound {M : ℕ} {xs : List (List W)} (h : ∀ ys∈xs, Array.Bounded ys M) (c : Count) :
    (column (xs,c)).digits.length≤M := by
  apply scalar_bound
  intro w hw
  obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hw
  change (Code.nth Array.zero (ys,c)).digits.length≤M
  rw [Code.nth_eval]
  exact (h ys hy).nth _
 theorem coordinates_small {M n : ℕ} {xs : List (List W)} (h : ∀ ys∈xs, Array.Bounded ys M) (c : Count) (hc : c.length≤n) :
    Array.Small n M (coordinates (c,xs)) := by
  refine ⟨?_,?_⟩
  · change ((Counter.enum c).map _).length≤n
    rw [List.length_map,Counter.enum_eq,List.length_map,List.length_range]
    exact hc
  · intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact column_bound h i
 theorem boxed_small {n M : ℕ} {b : RawBox.Data} (hb : RawBox.Small n M b) {xs : List (List W)} (h : ∀ ys∈xs, Array.Small n M ys) :
    Array.Small n M (boxed (b,xs)) := by
  simp only [boxed,branch_eval,comp_eval,pair_eval,fst_eval,snd_eval,empty_eval]
  split
  · exact hb.lower
  · apply coordinates_small (fun ys hy => (h ys hy).digits)
    change (b.2.1.map (fun _ => ())).length≤n
    simpa only [List.length_map] using hb.lower.length
end RawMedian
namespace RawOrientation
 def Small (n : ℕ) (o : Data) : Prop := ∀ hs∈o.2, hs.length≤n
 theorem positives_length (b : RawBox.Data) (s : W) (xs : List W) : (positives (b,s,xs)).length=xs.length := by
  change ((_ : List W).map _).length=xs.length
  rw [List.length_map]
  change ((_ : List W).map _).length=xs.length
  rw [List.length_map]
  exact Array.zip_length _ _ _ _
 theorem negatives_length (b : RawBox.Data) (s : W) (xs : List W) : (negatives (b,s,xs)).length=xs.length := by
  change ((_ : List W).map _).length=xs.length
  rw [List.length_map]
  change ((_ : List W).map _).length=xs.length
  rw [List.length_map]
  exact Array.zip_length _ _ _ _
 theorem trueComplement_small {n : ℕ} {bs : List Bool} (h : bs.length≤n) : Small n (trueComplement bs) := by
  intro cs hc
  change cs∈[bs.map Bool.not] at hc
  rcases List.mem_singleton.mp hc with rfl
  simpa only [List.length_map] using h
 theorem falseComplement_small {n : ℕ} {bs : List Bool} (h : bs.length≤n) : Small n (falseComplement bs) := by
  intro cs hc
  change cs∈[bs.map Bool.not] at hc
  rcases List.mem_singleton.mp hc with rfl
  simpa only [List.length_map] using h
 theorem base_small {n M : ℕ} (p : RawBudget.Data) (b : RawBox.Data) {xs : List W} (h : Array.Small n M xs) : Small n (base (p,b,xs)) := by
  have hl : (baseMask (b,xs)).length≤n := by
    change ((_ : List W).map _).length≤n
    rw [List.length_map]
    change ((_ : List W).map _).length≤n
    rw [List.length_map]
    change (Array.sub (xs,b.2.1)).length≤n
    exact (Array.zip_length _ _ _ _).le.trans h.length
  change Small n (if RawBudget.measureLarge (p,baseMask (b,xs)) then _ else _)
  split
  · exact trueComplement_small hl
  · intro cs hc
    change cs∈[baseMask (b,xs)] at hc
    rcases List.mem_singleton.mp hc with rfl
    exact hl
 theorem extend_small {n : ℕ} {o : Data} (ho : Small n o) {hs ns : List Bool} (hh : hs.length≤n) (hn : ns.length≤n) :
    Small n (extend (o,hs,ns)) := by
  intro cs hc
  change cs∈Code.append (o.2,[hs,ns]) at hc
  rw [Code.append_eval] at hc
  rcases List.mem_append.mp hc with hc | hc
  · exact ho cs hc
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl <;> assumption
 theorem combine_small {n : ℕ} {os : List Data} (h : ∀ o∈os, Small n o) : Small n (combine os) := by
  intro cs hc
  change cs∈Code.flatten (os.map Prod.snd) at hc
  rw [Code.flatten_eval] at hc
  obtain ⟨ss,hs,hcs⟩ := List.mem_flatten.mp hc
  obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hs
  exact h o ho cs hcs
end RawOrientation
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_StateGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
structure Pack.Small (n H M : ℕ) (z : Pack) : Prop where
  p : RawBudget.Small n M z.p
  b : RawBox.Small n M z.b
  t : z.t.length≤H
  q : Array.Small n M z.q
  r : Array.Small n M z.r
  vs : ∀ xs∈z.vs, Array.Small n M xs
  o : RawOrientation.Small n z.o
  os : ∀ v∈z.os, RawOrientation.Small n v
 theorem Pack.Small.mono {n H M N : ℕ} {z : Pack} (h : z.Small n H M) (hm : M≤N) : z.Small n H N :=
  ⟨h.p.mono hm,h.b.mono hm,h.t,h.q.mono hm,h.r.mono hm,fun xs hx => (h.vs xs hx).mono hm,h.o,h.os⟩
 theorem zeroBudget_small (n M : ℕ) : RawBudget.Small n M zeroBudget :=
  ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _⟩
 theorem zeroBox_small (n M : ℕ) : RawBox.Small n M zeroBox := ⟨Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _⟩
 theorem zeroOrient_small (n : ℕ) : RawOrientation.Small n (false,[]) := by intro bs hb; cases hb
 theorem Pack.zero_small (n H M : ℕ) : Pack.zero.Small n H M :=
  ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,by simp [Pack.zero],zeroOrient_small _,by simp [Pack.zero]⟩
 def StackSmall (n H M : ℕ) (ks : List Cell) : Prop := ∀ c∈ks, c.2.Small n H M
 def StateSmall (n H M : ℕ) (s : State) : Prop := s.1.2.Small n H M ∧ StackSmall n H M s.2
 theorem StackSmall.mono {n H M N : ℕ} {ks : List Cell} (h : StackSmall n H M ks) (hm : M≤N) : StackSmall n H N ks := fun c hc => (h c hc).mono hm
 theorem StackSmall.tail {n H M : ℕ} {ks : List Cell} (h : StackSmall n H M ks) : StackSmall n H M ks.tail := fun c hc => h c (List.mem_of_mem_tail hc)
 theorem StackSmall.head {n H M : ℕ} {ks : List Cell} (h : StackSmall n H M ks) : (ks.headD ([],Pack.zero)).2.Small n H M := by
  cases ks with
  | nil => exact Pack.zero_small _ _ _
  | cons c cs => exact h c (by simp)
 theorem StackSmall.cons {n H M : ℕ} {ks : List Cell} {c : Cell} (hc : c.2.Small n H M) (h : StackSmall n H M ks) : StackSmall n H M (c::ks) := by
  intro d hd; rcases List.mem_cons.mp hd with rfl | hd
  · exact hc
  · exact h d hd
 theorem narrow_small {n M : ℕ} {x : Input} (bc : Code Input RawBox.Data) (vc : Code Input (List W))
    (hb : RawBox.Small n M (bc x)) (hv : Array.Small n M (vc x)) : RawBox.Small n (M+3) (narrow bc vc x) := by
  apply RawBox.centered_small _ hv
  exact (Word.shiftRight_length _ _).trans hb.width
 theorem wide_small {n M : ℕ} {x : Input} (bc : Code Input RawBox.Data) (vc : Code Input (List W))
    (hb : RawBox.Small n M (bc x)) (hv : Array.Small n M (vc x)) : RawBox.Small n (M+3) (wide bc vc x) := by
  apply RawBox.centered_small _ hv
  exact (Word.shiftRight_length _ _).trans hb.width
 theorem capWidth_small {n M : ℕ} {x : Input} (bc : Code Input RawBox.Data) (hb : RawBox.Small n M (bc x)) :
    (capWidth bc x).digits.length≤M+3 := by
  change (Word.sub ((bc x).1,delta bc x)).digits.length≤_
  rw [Word.sub_length]
  have hd : (delta bc x).digits.length≤M := (Word.shiftRight_length _ _).trans hb.width
  have := hb.width
  omega
 theorem centerAt_small {n M : ℕ} {x : Input} (ic : Code Input Count)
    (hb : RawBox.Small n M ((caller ≫ₚ b) x)) (hv : ∀ xs∈(current x).vs, Array.Small n M xs) :
    Array.Small n M (centerAt ic x) := by
  simp only [centerAt,comp_eval,pair_eval,vs_eval,getD_eval]
  exact Array.Small.getD hv _ hb.midpoint
 theorem lastPositive_small {n M : ℕ} {x : Input}
    (hb : RawBox.Small n M ((caller ≫ₚ b) x)) (hv : ∀ xs∈(current x).vs, Array.Small n M xs) :
    (lastPositive x).length≤n := by
  change (RawOrientation.positives (_,_,centerAt _ x)).length≤n
  rw [RawOrientation.positives_length]
  exact (centerAt_small _ hb hv).length
 theorem lastNegative_small {n M : ℕ} {x : Input}
    (hb : RawBox.Small n M ((caller ≫ₚ b) x)) (hv : ∀ xs∈(current x).vs, Array.Small n M xs) :
    (lastNegative x).length≤n := by
  change (RawOrientation.negatives (_,_,centerAt _ x)).length≤n
  rw [RawOrientation.negatives_length]
  exact (centerAt_small _ hb hv).length
 theorem basic_small {n M E : ℕ} {x : Input} (bc : Code Input RawBox.Data)
    (hb : RawBox.Small n M (bc x)) (he : RawBasic.ArenaBounded x.1.1 E) :
    Array.Small n (M+x.1.2.2.2.2.length*(E+1)) (basic bc x) := RawBasic.solve_small he hb _
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace RawOrientation
 theorem base_length (p : RawBudget.Data) (b : RawBox.Data) (xs : List W) : (base (p,b,xs)).2.length=1 := by
  change (if RawBudget.measureLarge (p,baseMask (b,xs)) then trueComplement (baseMask (b,xs)) else singleton (false,baseMask (b,xs))).2.length=1
  split <;> rfl
 theorem combine_length (os : List Data) : (combine os).2.length=listMass os := by
  change (Code.flatten (os.map Prod.snd)).length=_
  simp only [listMass,Code.flatten_eval,List.length_flatten,List.map_map,Function.comp_def]
 theorem extend_length (o : Data) (hs ns : List Bool) : (extend (o,hs,ns)).2.length=o.2.length+2 := by
  change (Code.append (o.2,[hs,ns])).length=_
  simp only [Code.append_eval,List.length_append,List.length_cons,List.length_nil]
end RawOrientation
namespace RawControl
 def stateMass (s : State) : ℕ := s.1.2.mass+stackMass s.2
end RawControl
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_DispatchBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
noncomputable def JobLabel.code : JobLabel → Code Input State
  | .solve => solveCase
  | .ask => askCase
  | .trials => trialsCase
  | .update => updateCase
  | .centers => centersCase
  | .orient => orientCase
  | .orientTrials => orientTrialsCase
  | .orientPlus => orientPlusCase
  | .tighten => tightenCase
  | .reweight => reweightCase
noncomputable def FrameLabel.code : FrameLabel → Code Input State
  | .trialsHead => trialsHeadCase
  | .vectorCons => vectorConsCase
  | .median => medianCase
  | .centerFirst => centerFirstCase
  | .centerSecond => centerSecondCase
  | .centersHead => centersHeadCase
  | .orientLoop => orientLoopCase
  | .orientTail => orientTailCase
  | .orientHead => orientHeadCase
  | .orientCons => orientConsCase
  | .combine => combineCase
  | .tightenFirst => tightenFirstCase
  | .tightenSecond => tightenSecondCase
  | .floor => boxPassCase
  | .ceiling => boxPassCase
  | .solveTight => solveTightCase
  | .solveOriented => solveOrientedCase
  | .reweightHead => reweightHeadCase
  | .solveReweighted => solveReweightedCase
  | .capHigh => capHighCase
  | .capLow => capLowCase
  | .includeInner => includeInnerCase
 theorem JobLabel.small (j : JobLabel) {n H M E D : ℕ} {x : Input}
    (hc : (current x).Small n H M) (hk : StackSmall n H M (stack x))
    (hs : x.1.2.2.1.length≤H) (hj : x.1.2.2.2.1.length≤H)
    (he : RawBasic.ArenaBounded x.1.1 E) (hd : x.1.2.2.2.2.length*(E+1)+20≤D) :
    StateSmall n H (M+D) (JobLabel.code j x) := by
  have hmd : M≤M+D := by omega
  have hd3 : M+3≤M+D := by omega
  have hd14 : M+14≤M+D := by omega
  have hdB : M+x.1.2.2.2.2.length*(E+1)≤M+D := by omega
  have hc' := hc.mono hmd
  have hk' := hk.mono hmd
  cases j with
  | solve =>
    simp only [JobLabel.code,solveCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,RawBox.Small.smallVector hc'.b hc'.p,
        Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · split
      · refine ⟨?_,hk'⟩
        exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,(basic_small _ hc.b he).mono hdB,
          Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · refine ⟨?_,StackSmall.cons hc' hk'⟩
        exact ⟨hc'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | ask =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc'.p,hc'.b,hj,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | trials =>
    simp only [JobLabel.code,trialsCase,branch_eval]
    split
    · exact ⟨Pack.zero_small _ _ _,hk'⟩
    · refine ⟨hc',StackSmall.cons ?_ hk'⟩
      exact ⟨hc'.p,hc'.b,(by change (current x).t.tail.length≤H; rw [List.length_tail]; have := hc.t; omega),Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | update =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc.p.reduceK.mono hd14,(narrow_small _ _ hc.b hc.q).mono hd3,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centers =>
    simp only [JobLabel.code,centersCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,?_,zeroOrient_small _,(by intro v hv; cases hv)⟩
      intro xs hx
      change xs∈[(current x).q] at hx
      rcases List.mem_singleton.mp hx with rfl
      exact hc'.q
    · refine ⟨hc',StackSmall.cons ?_ hk'⟩
      exact ⟨hc'.p,hc'.b,(by change (current x).t.tail.length≤H; rw [List.length_tail]; have := hc.t; omega),hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orient =>
    simp only [JobLabel.code,orientCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.base_small _ _ ((basic_small _ hc.b he).mono hdB),(by intro v hv; cases hv)⟩
    · refine ⟨?_,StackSmall.cons hc' hk'⟩
      exact ⟨hc'.p,hc'.b,hs,hc'.b.midpoint,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orientTrials =>
    simp only [JobLabel.code,orientTrialsCase,branch_eval]
    split
    · exact ⟨Pack.zero_small _ _ _,hk'⟩
    · refine ⟨hc',StackSmall.cons ?_ hk'⟩
      exact ⟨hc'.p,hc'.b,(by change (current x).t.tail.length≤H; rw [List.length_tail]; have := hc.t; omega),Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orientPlus =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc'.p,hc'.b,hj,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | tighten =>
    refine ⟨?_,StackSmall.cons hc' hk'⟩
    exact ⟨hc.p.reduceK.mono hd14,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | reweight =>
    simp only [JobLabel.code,reweightCase,branch_eval]
    split
    · exact ⟨Pack.zero_small _ _ _,hk'⟩
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · refine ⟨?_,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
        simp only [call,makeCell,pair_eval,pack_eval,branch_eval]
        split
        · exact (hc.p.reweightM _).mono hd14
        · exact (hc.p.reweightK _).mono hd14
      · refine ⟨hc'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),?_,(by intro v hv; cases hv)⟩
        intro xs hx
        exact hc.o xs (List.mem_of_mem_tail hx)
 theorem FrameLabel.small (f : FrameLabel) {n H M D : ℕ} {x : Input}
    (hc : (current x).Small n H M) (hf : (caller x).Small n H M) (hk : StackSmall n H M (rest x))
    (hd : 20≤D) : StateSmall n H (M+D) (FrameLabel.code f x) := by
  have hmd : M≤M+D := by omega
  have hd3 : M+3≤M+D := by omega
  have hd6 : M+3+3≤M+D := by omega
  have hd14 : M+14≤M+D := by omega
  have hc' := hc.mono hmd
  have hf' := hf.mono hmd
  have hk' := hk.mono hmd
  cases f with
  | trialsHead =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,hf'.t,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | vectorCons =>
    refine ⟨?_,hk'⟩
    refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,?_,zeroOrient_small _,(by intro v hv; cases hv)⟩
    intro xs hx
    change xs∈(caller x).q::(current x).vs at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hf'.q
    · exact hc'.vs xs hx
  | median =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,RawMedian.boxed_small hf'.b hc'.vs,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centerFirst =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf.p.reduceM.mono hd14,(narrow_small _ _ hf.b hf.q).mono hd3,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,hc'.q,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centerSecond =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hf'.b.averageClipped hf'.r hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | centersHead =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,hf'.t,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hf'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | orientLoop =>
    have hp := lastPositive_small hf.b hc.vs
    have hn := lastNegative_small hf.b hc.vs
    simp only [FrameLabel.code,orientLoopCase,branch_eval]
    split
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.trueComplement_small hp,(by intro v hv; cases hv)⟩
    · split
      · refine ⟨?_,hk'⟩
        exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.falseComplement_small hn,(by intro v hv; cases hv)⟩
      · refine ⟨?_,StackSmall.cons ?_ hk'⟩
        · exact ⟨hf'.p,(wide_small _ _ hf.b (centerAt_small _ hf.b hc.vs)).mono hd3,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
        · refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),?_,(by intro v hv; cases hv)⟩
          intro bs hbs
          change bs∈[lastPositive x,lastNegative x] at hbs
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hbs
          rcases hbs with rfl | rfl <;> assumption
  | orientTail =>
    refine ⟨?_,hk'⟩
    refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),?_,(by intro v hv; cases hv)⟩
    exact RawOrientation.extend_small hc.o (mask_head hf.o) (mask_head (fun bs hbs => hf.o bs (List.mem_of_mem_tail hbs)))
  | orientHead =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,hf'.t,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),hc.o,(by intro v hv; cases hv)⟩
  | orientCons =>
    refine ⟨?_,hk'⟩
    refine ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,?_⟩
    intro v hv
    change v∈(caller x).o::(current x).os at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hf.o
    · exact hc.os v hv
  | combine =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),RawOrientation.combine_small hc.os,(by intro v hv; cases hv)⟩
  | tightenFirst =>
    simp only [FrameLabel.code,tightenFirstCase,branch_eval]
    split
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,hf'.b.withFloor hc'.q,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · refine ⟨?_,StackSmall.cons hf' hk'⟩
      exact ⟨hf.p.reduceM.mono hd14,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | tightenSecond =>
    simp only [FrameLabel.code,tightenSecondCase,branch_eval]
    split
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,hf'.b.withCeiling hc'.q,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · refine ⟨?_,hk'⟩
      exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | floor | ceiling =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | solveTight =>
    refine ⟨?_,StackSmall.cons ?_ (StackSmall.cons (Pack.zero_small _ _ _) hk')⟩
    · exact ⟨hf'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
    · exact ⟨hf'.p,hc'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | solveOriented =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),hc.o,(by intro v hv; cases hv)⟩
    · exact ⟨hf'.p,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),(by intro v hv; cases hv),(by intro v hv; cases hv)⟩
  | reweightHead =>
    refine ⟨?_,StackSmall.cons ?_ hk'⟩
    · exact ⟨hf'.p,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),hf.o,(by intro v hv; cases hv)⟩
    · exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | solveReweighted =>
    have hw := capWidth_small (x:=x) (caller ≫ₚ b) hf.b
    simp only [FrameLabel.code,solveReweightedCase,branch_eval]
    split
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,((hf.b.mono (by omega : M≤M+3)).capHigh hw).mono hd6,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,hc'.vs,zeroOrient_small _,(by intro v hv; cases hv)⟩
    · refine ⟨?_,StackSmall.cons ?_ hk'⟩
      · exact ⟨hf'.p,((hf.b.mono (by omega : M≤M+3)).capLow hw).mono (by omega),Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
      · exact ⟨zeroBudget_small _ _,hf'.b,Nat.zero_le _,Array.Small.nil _ _,Array.Small.nil _ _,hc'.vs,zeroOrient_small _,(by intro v hv; cases hv)⟩
  | capHigh =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q.foldMin hf'.vs,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | capLow =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q.foldMax hf'.vs,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
  | includeInner =>
    refine ⟨?_,hk'⟩
    exact ⟨zeroBudget_small _ _,zeroBox_small _ _,Nat.zero_le _,hc'.q,Array.Small.nil _ _,(by intro v hv; cases hv),zeroOrient_small _,(by intro v hv; cases hv)⟩
 theorem JobLabel.mass (j : JobLabel) (x : Input) :
    stateMass (JobLabel.code j x)≤ stateMass (state x)+3 ∧ (JobLabel.code j x).2.length≤(stack x).length+2 := by
  cases j <;>
    simp only [JobLabel.code,solveCase,askCase,trialsCase,updateCase,centersCase,orientCase,orientTrialsCase,
      orientPlusCase,tightenCase,reweightCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [stateMass,ret,call,save,push,makeCell,pair_eval,comp_eval,pack_eval,const_eval,
      cons_eval,tail_eval,stackMass_cons,Pack.mass,p_eval,b_eval,t_eval,q_eval,o_eval,      List.length_nil,List.length_cons,RawOrientation.listMass_nil,      RawOrientation.base_length,List.length_tail] <;>
    dsimp only [state,stack,current,Code.comp_eval,Code.fst_eval,Code.snd_eval] <;> omega
 theorem FrameLabel.mass (f : FrameLabel) (x : Input) :
    stateMass (FrameLabel.code f x)≤(current x).mass+(caller x).mass+stackMass (rest x)+3 ∧
      (FrameLabel.code f x).2.length≤(rest x).length+2 := by
  cases f <;>
    simp only [FrameLabel.code,trialsHeadCase,vectorConsCase,medianCase,centerFirstCase,centerSecondCase,
      centersHeadCase,orientLoopCase,orientTailCase,orientHeadCase,orientConsCase,combineCase,
      tightenFirstCase,tightenSecondCase,boxPassCase,solveTightCase,solveOrientedCase,reweightHeadCase,
      solveReweightedCase,capHighCase,capLowCase,includeInnerCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [stateMass,ret,call,push,makeCell,pair_eval,comp_eval,pack_eval,const_eval,
      cons_eval,tail_eval,stackMass_cons,Pack.mass,p_eval,b_eval,t_eval,q_eval,r_eval,vs_eval,o_eval,os_eval,
      List.length_nil,List.length_cons,RawOrientation.listMass_nil,RawOrientation.listMass_cons,
      RawOrientation.extend_length,RawOrientation.combine_length,      RawOrientation.trueComplement,RawOrientation.falseComplement,RawOrientation.singleton,Pack.zero] <;>
    simp only [Code.comp_eval,Code.fst_eval,Code.snd_eval,      current,caller,stack,rest,state,Code.head_eval,Code.tail_eval] <;> omega
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Code
 theorem select_spec {α β : Type} [Encoding α] [Encoding β] (tag : Code α Count) (cases : List (Code α β))
    (fallback : Code α β) (x : α) (P : β→Prop) (hc : ∀ c∈cases, P (c x)) (hf : P (fallback x)) :
    P (select tag cases fallback x) := by
  induction cases generalizing tag with
  | nil => exact hf
  | cons c cs ih =>
    simp only [select,branch_eval]
    split
    · exact hc c (by simp)
    · exact ih _ (fun d hd => hc d (by simp [hd]))
end Code
namespace RawControl
 theorem jobs_spec (x : Input) (P : State→Prop) (h : ∀ j : JobLabel, P (j.code x)) :
    ∀ c ∈ [solveCase,askCase,trialsCase,updateCase,centersCase,orientCase,orientTrialsCase,orientPlusCase,tightenCase,reweightCase], P (c x) := by
  intro c hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h .solve
  · exact h .ask
  · exact h .trials
  · exact h .update
  · exact h .centers
  · exact h .orient
  · exact h .orientTrials
  · exact h .orientPlus
  · exact h .tighten
  · exact h .reweight
 theorem frames_spec (x : Input) (P : State→Prop) (h : ∀ j : FrameLabel, P (j.code x)) :
    ∀ c ∈ [trialsHeadCase,vectorConsCase,medianCase,centerFirstCase,centerSecondCase,centersHeadCase,orientLoopCase,orientTailCase,orientHeadCase,orientConsCase,combineCase,tightenFirstCase,tightenSecondCase,boxPassCase,boxPassCase,solveTightCase,solveOrientedCase,reweightHeadCase,solveReweightedCase,capHighCase,capLowCase,includeInnerCase], P (c x) := by
  intro c hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h .trialsHead
  · exact h .vectorCons
  · exact h .median
  · exact h .centerFirst
  · exact h .centerSecond
  · exact h .centersHead
  · exact h .orientLoop
  · exact h .orientTail
  · exact h .orientHead
  · exact h .orientCons
  · exact h .combine
  · exact h .tightenFirst
  · exact h .tightenSecond
  · exact h .floor
  · exact h .ceiling
  · exact h .solveTight
  · exact h .solveOriented
  · exact h .reweightHead
  · exact h .solveReweighted
  · exact h .capHigh
  · exact h .capLow
  · exact h .includeInner
 theorem caller_mass (x : Input) : (caller x).mass+stackMass (rest x)=stackMass (stack x) := by
  change ((stack x).headD ([],Pack.zero)).2.mass+stackMass (stack x).tail=stackMass (stack x)
  cases stack x <;> rfl
 theorem dispatch_small {n H M E D : ℕ} {x : Input}
    (hc : (current x).Small n H M) (hk : StackSmall n H M (stack x))
    (hs : x.1.2.2.1.length≤H) (hj : x.1.2.2.2.1.length≤H)
    (he : RawBasic.ArenaBounded x.1.1 E) (hd : x.1.2.2.2.2.length*(E+1)+20≤D) :
    StateSmall n H (M+D) (dispatch x) := by
  have hmd : M≤M+D := by omega
  have h0 : StateSmall n H (M+D) (state x) := ⟨hc.mono hmd,hk.mono hmd⟩
  apply Code.select_spec
  · exact jobs_spec x _ (fun j => j.small hc hk hs hj he hd)
  · simp only [resume,branch_eval]
    split
    · exact h0
    · apply Code.select_spec
      · exact frames_spec x _ (fun f => f.small hc hk.head hk.tail (by omega))
      · exact h0
 theorem dispatch_mass (x : Input) :
    stateMass (dispatch x)≤ stateMass (state x)+3 ∧ (dispatch x).2.length≤(stack x).length+2 := by
  have h0 : stateMass (state x)≤ stateMass (state x)+3 ∧ (state x).2.length≤(stack x).length+2 := by
    constructor <;> exact Nat.le_add_right _ _
  refine Code.select_spec _ _ _ x (fun z => stateMass z ≤ stateMass (state x)+3 ∧ z.2.length≤(stack x).length+2) ?_ ?_
  · exact jobs_spec x (fun z => stateMass z ≤ stateMass (state x)+3 ∧ z.2.length≤(stack x).length+2) (fun j => j.mass x)
  · simp only [resume,branch_eval]
    split
    · exact h0
    · refine Code.select_spec _ _ _ x (fun z => stateMass z ≤ stateMass (state x)+3 ∧ z.2.length≤(stack x).length+2) ?_ ?_
      · apply frames_spec x (fun z => stateMass z ≤ stateMass (state x)+3 ∧ z.2.length≤(stack x).length+2)
        intro f
        have h := f.mass x
        have hm := caller_mass x
        have ht : (rest x).length≤(stack x).length := by
          change (stack x).tail.length≤(stack x).length
          rw [List.length_tail]; omega
        change _≤(current x).mass+stackMass (stack x)+3 ∧ _≤_ at ⊢
        omega
      · exact h0
end RawControl
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_SizeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Size
variable {α β : Type} [Encoding α] [Encoding β]
 theorem randomBool (b : Bool) : treeSize (encode b)≤7 := by cases b <;> decide
 theorem mask (bs : List Bool) : treeSize (encode bs)≤8*bs.length+1 := by
  have h := list_bound (xs:=bs) (M:=7) (fun b _ => randomBool b)
  omega
 theorem digits {w : W} {N : ℕ} (h : treeSize (encode w)≤N) : w.digits.length≤N := (digits_le_wordSize w).trans h
end Size
namespace Array
 theorem randomSmallOfSize {xs : List W} {N : ℕ} (h : treeSize (encode xs)≤N) : Small N N xs :=
  ⟨(Size.length xs).trans h,(bounded_size xs).mono h⟩
 theorem Small.randomSize {xs : List W} {n M : ℕ} (h : Small n M xs) : treeSize (encode xs)≤n*(4*M+6)+1 :=
  (size_bound h.digits).trans (by gcongr; exact h.length)
end Array
namespace RawBudget
 theorem small_of_size {p : Data} {N : ℕ} (h : treeSize (encode p)≤N) : Small N N p := by
  have h1 := (Size.fst p).trans h
  have h2 := (Size.snd p).trans h
  have h21 := (Size.fst p.2).trans h2
  have h22 := (Size.snd p.2).trans h2
  exact ⟨Size.digits ((Size.fst p.1).trans h1),Size.digits ((Size.snd p.1).trans h1),
    Size.digits ((Size.fst p.2.1).trans h21),Size.digits ((Size.snd p.2.1).trans h21),
    Array.randomSmallOfSize ((Size.fst p.2.2).trans h22),Array.randomSmallOfSize ((Size.snd p.2.2).trans h22)⟩
end RawBudget
namespace RawBox
 theorem small_of_size {b : Data} {N : ℕ} (h : treeSize (encode b)≤N) : Small N N b := by
  have h2 := (Size.snd b).trans h
  exact ⟨Size.digits ((Size.fst b).trans h),Array.randomSmallOfSize ((Size.fst b.2).trans h2),
    Array.randomSmallOfSize ((Size.snd b.2).trans h2)⟩
end RawBox
namespace RawOrientation
 theorem small_of_size {o : Data} {N : ℕ} (h : treeSize (encode o)≤N) : Small N o := by
  intro bs hb
  exact (Size.length bs).trans ((Size.mem hb).trans ((Size.snd o).trans h))
 theorem listMass_size (os : List Data) : listMass os≤treeSize (encode os) := by
  induction os with
  | nil => exact Nat.zero_le _
  | cons o os ih =>
    rw [listMass_cons]
    have ho := (Size.length o.2).trans (Size.snd o)
    change _≤treeSize (listTree encode (o::os))
    rw [listTree,treeSize_pair]
    change _≤treeSize (listTree encode os) at ih
    omega
 theorem small_size {o : Data} {n : ℕ} (h : Small n o) :
    treeSize (encode o)≤o.2.length*(8*n+2)+9 := by
  have hl := Size.list_bound (xs:=o.2) (M:=8*n+1) (fun b hb => (Size.mask b).trans (by gcongr; exact h b hb))
  have hb := Size.randomBool o.1
  rw [←Prod.eta o,Size.pair]
  dsimp only
  nlinarith
 theorem many_size {os : List Data} {n : ℕ} (h : ∀ o∈os, Small n o) :
    treeSize (encode os)≤listMass os*(8*n+2)+10*os.length+1 := by
  induction os with
  | nil => change treeSize Data.nil≤_; simp only [treeSize_nil,List.length_nil,Nat.zero_mul,Nat.zero_add,RawOrientation.listMass_nil]; omega
  | cons o os ih =>
    have ho := small_size (h o (by simp))
    have ht := ih (fun q hq => h q (by simp [hq]))
    change treeSize (listTree encode (o::os))≤_
    rw [listTree,treeSize_pair,listMass_cons,List.length_cons]
    change treeSize (listTree encode os)≤_ at ht
    nlinarith
end RawOrientation
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
 theorem Pack.fields_size (z : Pack) :
    treeSize (encode z.p)≤treeSize (encode z) ∧
    treeSize (encode z.b)≤treeSize (encode z) ∧
    treeSize (encode z.t)≤treeSize (encode z) ∧
    treeSize (encode z.q)≤treeSize (encode z) ∧
    treeSize (encode z.r)≤treeSize (encode z) ∧
    treeSize (encode z.vs)≤treeSize (encode z) ∧
    treeSize (encode z.o)≤treeSize (encode z) ∧
    treeSize (encode z.os)≤treeSize (encode z) := by
  have h1 := Size.fst z.tuple
  have h2 := Size.snd z.tuple
  have h3 := (Size.snd z.tuple.2).trans h2
  have h4 := (Size.snd z.tuple.2.2).trans h3
  have h5 := (Size.snd z.tuple.2.2.2).trans h4
  have h6 := (Size.snd z.tuple.2.2.2.2).trans h5
  have h7 := (Size.snd z.tuple.2.2.2.2.2).trans h6
  exact ⟨h1,(Size.fst z.tuple.2).trans h2,(Size.fst z.tuple.2.2).trans h3,
    (Size.fst z.tuple.2.2.2).trans h4,(Size.fst z.tuple.2.2.2.2).trans h5,
    (Size.fst z.tuple.2.2.2.2.2).trans h6,(Size.fst z.tuple.2.2.2.2.2.2).trans h7,
    (Size.snd z.tuple.2.2.2.2.2.2).trans h7⟩
 theorem Pack.small_of_size {z : Pack} {N : ℕ} (h : treeSize (encode z)≤N) : z.Small N N N := by
  rcases z.fields_size with ⟨hp,hb,ht,hq,hr,hvs,ho,hos⟩
  exact ⟨RawBudget.small_of_size (hp.trans h),RawBox.small_of_size (hb.trans h),
    (Size.length z.t).trans (ht.trans h),Array.randomSmallOfSize (hq.trans h),Array.randomSmallOfSize (hr.trans h),
    fun xs hx => Array.randomSmallOfSize ((Size.mem hx).trans (hvs.trans h)),
    RawOrientation.small_of_size (ho.trans h),
    fun o ho' => RawOrientation.small_of_size ((Size.mem ho').trans (hos.trans h))⟩
 theorem Pack.mass_size (z : Pack) : z.mass≤4*treeSize (encode z) := by
  rcases z.fields_size with ⟨_,_,_,_,_,hvs,ho,hos⟩
  have h1 := (Size.length z.vs).trans hvs
  have h2 := (Size.length z.o.2).trans ((Size.snd z.o).trans ho)
  have h3 := (Size.length z.os).trans hos
  have h4 := (RawOrientation.listMass_size z.os).trans hos
  dsimp only [Pack.mass]; omega
 theorem Pack.small_size {z : Pack} {n H M U : ℕ} (h : z.Small n H M)
    (hu : 1≤U) (hn : n≤U) (hh : H≤U) (hm : M≤U) (hz : z.mass≤U) :
    treeSize (encode z)≤1024*U^3 := by
  have u2 : U≤U^2 := Nat.le_pow (by decide : 0<2)
  have u3 : U^2≤U^3 := Nat.pow_le_pow_right hu (by omega)
  have a (xs : List W) (ha : Array.Small n M xs) : treeSize (encode xs)≤12*U^2 := by
    have ht := ha.randomSize
    have hab : n*(4*M+6)≤U*(4*U+6) := Nat.mul_le_mul hn (by omega)
    nlinarith
  have w (v : W) (hv : v.digits.length≤M) : treeSize (encode v)≤10*U := by
    have hw := wordSize_bound v
    change treeSize (encode v)≤4*v.digits.length+5 at hw
    omega
  have hp : treeSize (encode z.p)≤72*U^2 := by
    have h1 := w _ h.p.kn
    have h2 := w _ h.p.kd
    have h3 := w _ h.p.mn
    have h4 := w _ h.p.md
    have h5 := a _ h.p.alpha
    have h6 := a _ h.p.beta
    rw [←Prod.eta z.p,Size.pair,←Prod.eta z.p.1,Size.pair,
      ←Prod.eta z.p.2,Size.pair,←Prod.eta z.p.2.1,Size.pair,←Prod.eta z.p.2.2,Size.pair]
    nlinarith
  have hb : treeSize (encode z.b)≤40*U^2 := by
    have h1 := w _ h.b.width
    have h2 := a _ h.b.lower
    have h3 := a _ h.b.upper
    rw [←Prod.eta z.b,Size.pair,←Prod.eta z.b.2,Size.pair]
    nlinarith
  have ht : treeSize (encode z.t)≤3*U := by rw [Size.count]; have := h.t; omega
  have hq := a _ h.q
  have hr := a _ h.r
  have hvlen : z.vs.length≤U := by dsimp only [Pack.mass] at hz; omega
  have hoLen : z.o.2.length≤U := by dsimp only [Pack.mass] at hz; omega
  have hosLen : z.os.length≤U := by dsimp only [Pack.mass] at hz; omega
  have hosMass : RawOrientation.listMass z.os≤U := by dsimp only [Pack.mass] at hz; omega
  have hv : treeSize (encode z.vs)≤14*U^3 := by
    have ht := Size.list_bound (fun xs hx => a xs (h.vs xs hx))
    have hb := Nat.mul_le_mul_right (12*U^2+1) hvlen
    nlinarith
  have ho : treeSize (encode z.o)≤20*U^2 := by
    have ht := RawOrientation.small_size h.o
    have hb := Nat.mul_le_mul hoLen (show 8*n+2≤8*U+2 by omega)
    nlinarith
  have hos : treeSize (encode z.os)≤22*U^2 := by
    have ht := RawOrientation.many_size h.os
    have hb := Nat.mul_le_mul hosMass (show 8*n+2≤8*U+2 by omega)
    nlinarith
  change treeSize (encode z.tuple)≤_
  simp only [Pack.tuple,Size.pair]
  nlinarith
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
 def StateTags (H : ℕ) (s : State) : Prop := s.1.1.length≤H ∧ StackTags H s.2
 @[simp] theorem stackTags_cons (H : ℕ) (c : Cell) (ks : List Cell) : StackTags H (c::ks) ↔ c.1.length≤H ∧ StackTags H ks := by simp [StackTags]
 theorem StackTags.tail {H : ℕ} {ks : List Cell} (h : StackTags H ks) : StackTags H ks.tail := fun c hc => h c (List.mem_of_mem_tail hc)
 theorem JobLabel.tags (j : JobLabel) {H : ℕ} {x : Input} (hH : 22≤H) (hk : StackTags H (stack x)) : StateTags H (j.code x) := by
  cases j <;>
    simp only [JobLabel.code,solveCase,askCase,trialsCase,updateCase,centersCase,orientCase,orientTrialsCase,
      orientPlusCase,tightenCase,reweightCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [StateTags,ret,call,save,push,makeCell,pair_eval,comp_eval,const_eval,
      cons_eval,List.length_replicate,stackTags_cons,hk,and_true] <;> omega
 theorem FrameLabel.tags (j : FrameLabel) {H : ℕ} {x : Input} (hH : 22≤H) (hk : StackTags H (rest x)) : StateTags H (j.code x) := by
  cases j <;>
    simp only [FrameLabel.code,trialsHeadCase,vectorConsCase,medianCase,centerFirstCase,centerSecondCase,
      centersHeadCase,orientLoopCase,orientTailCase,orientHeadCase,orientConsCase,combineCase,
      tightenFirstCase,tightenSecondCase,boxPassCase,solveTightCase,solveOrientedCase,reweightHeadCase,
      solveReweightedCase,capHighCase,capLowCase,includeInnerCase,branch_eval] <;>
    (try split_ifs) <;>
    simp only [StateTags,ret,call,push,makeCell,pair_eval,comp_eval,const_eval,
      cons_eval,List.length_replicate,stackTags_cons,hk,and_true] <;> omega
 theorem dispatch_tags {H : ℕ} {x : Input} (hH : 22≤H) (h : StateTags H (state x)) : StateTags H (dispatch x) := by
  apply Code.select_spec
  · exact jobs_spec x _ (fun j => j.tags hH h.2)
  · simp only [resume,branch_eval]
    split
    · exact h
    · apply Code.select_spec
      · exact frames_spec x _ (fun j => j.tags hH h.2.tail)
      · exact h
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
namespace Size
@[simp] theorem cons {α : Type} [Encoding α] (a : α) (as : List α) :
    treeSize (encode (a::as))=treeSize (encode a)+treeSize (encode as)+1 := treeSize_pair _ _
end Size
namespace RawControl
 theorem stackMass_mem {ks : List Cell} {c : Cell} (hc : c∈ks) : c.2.mass≤ stackMass ks := by
  induction ks with
  | nil => cases hc
  | cons d ds ih =>
    rw [stackMass_cons]
    rcases List.mem_cons.mp hc with rfl | hc
    · omega
    · have := ih hc; omega
 theorem stackMass_size (ks : List Cell) : stackMass ks≤4*treeSize (encode ks) := by
  induction ks with
  | nil => exact Nat.zero_le _
  | cons c cs ih =>
    rw [stackMass_cons,Size.cons]
    have hp := c.2.mass_size
    have hc := Size.snd c
    omega
 theorem stateMass_size (s : State) : stateMass s≤4*treeSize (encode s) := by
  have h1 := s.1.2.mass_size
  have h2 := stackMass_size s.2
  have h3 := Size.snd s.1
  rw [←Prod.eta s,Size.pair]
  dsimp only [stateMass]; omega
 theorem stateSmall_of_size {s : State} {N : ℕ} (h : treeSize (encode s)≤N) : StateSmall N N N s := by
  exact ⟨Pack.small_of_size ((Size.snd s.1).trans ((Size.fst s).trans h)),
    fun c hc => Pack.small_of_size ((Size.snd c).trans ((Size.mem hc).trans ((Size.snd s).trans h)))⟩
 theorem stateTags_of_size {s : State} {N : ℕ} (h : treeSize (encode s)≤N) : StateTags N s := by
  exact ⟨(Size.length s.1.1).trans ((Size.fst s.1).trans ((Size.fst s).trans h)),
    fun c hc => (Size.length c.1).trans ((Size.fst c).trans ((Size.mem hc).trans ((Size.snd s).trans h)))⟩
 theorem StateTags.mono {s : State} {H N : ℕ} (h : StateTags H s) (hm : H≤N) : StateTags N s :=
  ⟨h.1.trans hm,fun c hc => (h.2 c hc).trans hm⟩
 theorem state_small_size {s : State} {n H M U : ℕ} (h : StateSmall n H M s)
    (ht : StateTags U s) (hu : 1≤U) (hn : n≤U) (hh : H≤U) (hm : M≤U)
    (hs : stateMass s≤U) (hk : s.2.length≤U) : treeSize (encode s)≤4096*U^4 := by
  have u2 : U≤U^2 := Nat.le_pow (by decide)
  have u3 : U^2≤U^3 := Nat.pow_le_pow_right hu (by omega)
  have u4 : U^3≤U^4 := Nat.pow_le_pow_right hu (by omega)
  have cell (c : Cell) (hp : c.2.Small n H M) (htag : c.1.length≤U) (hmass : c.2.mass≤U) :
      treeSize (encode c)≤1028*U^3 := by
    have hpk := Pack.small_size hp hu hn hh hm hmass
    rw [←Prod.eta c,Size.pair,Size.count]
    nlinarith
  have hhead : treeSize (encode s.1)≤1028*U^3 := cell s.1 h.1 ht.1 (by dsimp only [stateMass] at hs; omega)
  have htail : treeSize (encode s.2)≤1030*U^4 := by
    have ht' := Size.list_bound (xs:=s.2) (M:=1028*U^3) (fun c hc => cell c (h.2 c hc) (ht.2 c hc) (by
      have := stackMass_mem hc; dsimp only [stateMass] at hs; omega))
    have hmul := Nat.mul_le_mul_right (1028*U^3+1) hk
    nlinarith
  rw [←Prod.eta s,Size.pair]
  nlinarith
end RawControl
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Loop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
noncomputable def advance : Code (Acc×Count) Acc :=
  (fst ≫ₚ fst) ⋏ₚ (((fst ≫ₚ fst) ⋏ₚ snd ⋏ₚ (fst ≫ₚ snd)) ≫ₚ dispatch)
@[simp] theorem advance_eval (e : Env) (s : State) (c : Count) : advance ((e,s),c)=(e,dispatch (e,c,s)) := rfl
 theorem fold_estimates (e : Env) (cs : List Count) {n H E D T : ℕ}
    (hs : e.2.2.1.length ≤ H) (hj : e.2.2.2.1.length ≤ H)
    (he : RawBasic.ArenaBounded e.1 E) (hd : e.2.2.2.2.length*(E+1)+20 ≤ D) (hT : 22 ≤ T)
    (s : State) (M : ℕ) (hc : StateSmall n H M s) (ht : StateTags T s) :
    (Fold.fold advance.eval (e,s) cs).1=e ∧
    StateSmall n H (M+cs.length*D) (Fold.fold advance.eval (e,s) cs).2 ∧
    stateMass (Fold.fold advance.eval (e,s) cs).2  ≤  stateMass s+3*cs.length ∧
    (Fold.fold advance.eval (e,s) cs).2.2.length ≤ s.2.length+2*cs.length ∧
    StateTags T (Fold.fold advance.eval (e,s) cs).2 := by
  induction cs generalizing s M with
  | nil => simpa [Fold.fold] using And.intro (rfl : e=e) (And.intro hc (And.intro (le_refl (stateMass s)) (And.intro (le_refl s.2.length) ht)))
  | cons c cs ih =>
    have hc' : StateSmall n H (M+D) (dispatch (e,c,s)) := dispatch_small hc.1 hc.2 hs hj he hd
    have ht' : StateTags T (dispatch (e,c,s)) := dispatch_tags hT ht
    have hm := dispatch_mass (e,c,s)
    have hh := ih (dispatch (e,c,s)) (M+D) hc' ht'
    rw [show Fold.fold advance.eval (e,s) (c::cs)=Fold.fold advance.eval (e,dispatch (e,c,s)) cs by rfl, List.length_cons]
    refine ⟨hh.1,?_,?_,?_,hh.2.2.2.2⟩
    · convert hh.2.1 using 1 ; ring
    · change stateMass (dispatch (e,c,s)) ≤  stateMass s+3 ∧ _ at hm
      omega
    · change _ ∧ (dispatch (e,c,s)).2.length ≤ s.2.length+2 at hm
      omega
 theorem prefix_size (s : Acc) (cs : List Count) (k : ℕ) (hk : k ≤ cs.length) :
    treeSize (encode (Fold.fold advance.eval s (cs.take k))) ≤
      1099511627776*(treeSize (encode (s,cs))+1)^12 := by
  let N := treeSize (encode (s,cs))+1
  have hs : treeSize (encode s) ≤ N := (Size.fst (s,cs)).trans (Nat.le_succ _)
  have he : treeSize (encode s.1) ≤ N := (Size.fst s).trans hs
  have hz : treeSize (encode s.2) ≤ N := (Size.snd s).trans hs
  have hg : treeSize (encode s.1.1) ≤ N := (Size.fst s.1).trans he
  have he2 := (Size.snd s.1).trans he
  have he22 := (Size.snd s.1.2).trans he2
  have he222 := (Size.snd s.1.2.2).trans he22
  have hsamp : s.1.2.2.1.length ≤ N := (Size.length _).trans ((Size.fst _).trans he22)
  have htrial : s.1.2.2.2.1.length ≤ N := (Size.length _).trans ((Size.fst _).trans he222)
  have hbasic : s.1.2.2.2.2.length ≤ N := (Size.length _).trans ((Size.snd _).trans he222)
  have hn : 1 ≤ N := Nat.le_add_left _ _
  have n2 : N ≤ N^2 := Nat.le_pow (by decide)
  have n3 : N^2 ≤ N^3 := Nat.pow_le_pow_right hn (by omega)
  have n12 : N^3 ≤ N^12 := Nat.pow_le_pow_right hn (by omega)
  have hl : (cs.take k).length ≤ N :=
    (List.length_take_le _ _).trans (hk.trans ((Size.length cs).trans ((Size.snd (s,cs)).trans (Nat.le_succ _))))
  let D := N*(N+1)+20
  have hh := fold_estimates s.1 (cs.take k) hsamp htrial
    (fun v hv e he => (RawBasic.arenaBounded_size _ v hv e he).trans hg)
    (show s.1.2.2.2.2.length*(N+1)+20 ≤ D by dsimp [D]; gcongr)
    (show 22 ≤ N+22 by omega) s.2 N (stateSmall_of_size hz) ((stateTags_of_size hz).mono (by omega))
  simp only [Prod.eta] at hh
  let U := 50*N^3
  have hu : 1 ≤ U := by dsimp [U]; omega
  have hnu : N ≤ U := by dsimp [U]; omega
  have hMu : N+(cs.take k).length*D ≤ U := by
    have hmul := Nat.mul_le_mul_right D hl
    dsimp [D] at hmul ⊢
    dsimp [U]
    nlinarith
  have hmass : stateMass (Fold.fold advance.eval s (cs.take k)).2 ≤ U := by
    have h0 := stateMass_size s.2
    dsimp [U]
    have h1 := hh.2.2.1
    omega
  have hdepth : (Fold.fold advance.eval s (cs.take k)).2.2.length ≤ U := by
    have h0 := (Size.length s.2.2).trans ((Size.snd s.2).trans hz)
    have h1 := hh.2.2.2.1
    dsimp [U]; omega
  have htag : StateTags U (Fold.fold advance.eval s (cs.take k)).2 := hh.2.2.2.2.mono (by dsimp [U]; omega)
  have hout := state_small_size hh.2.1 htag hu hnu hnu hMu hmass hdepth
  rw [←Prod.eta (Fold.fold advance.eval s (cs.take k)),Size.pair]
  rw [hh.1]
  change _ ≤ 1099511627776*N^12
  dsimp [U] at hout
  rw [mul_pow,←pow_mul] at hout
  norm_num at hout
  nlinarith
noncomputable def loop : Code (Acc×List Count) Acc := foldPrefix advance 1099511627776 12 prefix_size
end MeanPayoff.TreeDevice.Certified.RawControl

end

section
namespace MeanPayoff.RandomTree
@[simp] theorem all_const_iff {α : Type} (t : RandomTree α) (P : Prop) : t.All (fun _ => P) ↔ P := by
  induction t with
  | leaf a => rfl
  | coin l r hl hr => simp only [All,hl,hr,and_self]
end MeanPayoff.RandomTree

end

section
namespace MeanPayoff.SourceControl

def sampledRun {G : Game} {B : ℕ} {R : Result G B} : ℕ → State G B R → RandomTree (State G B R)
  | 0,s => .leaf s
  | n+1,s => (RandomTree.uniformBelow (sampleExponent B)).bind fun j => sampledRun n (sampledStep j s)

end MeanPayoff.SourceControl
namespace MeanPayoff.TreeDevice.Certified.RawControl
open BinaryData Code

def drawSamples (e n : ℕ) : RandomTree (List Count) :=
  match n with
  | 0 => .leaf []
  | n+1 => (RandomTree.uniformBelow e).bind fun j => (drawSamples e n).map (List.replicate j () :: ·)

end MeanPayoff.TreeDevice.Certified.RawControl

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Allocation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Counter
noncomputable def fixedPower : ℕ → Code Count Count
  | 0 => const [()]
  | k+1 => (Code.id ⋏ₚ fixedPower k) ≫ₚ mul
@[simp] theorem fixedPower_length (k : ℕ) (c : Count) : (fixedPower k c).length=c.length^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [fixedPower,ih,pow_succ,Nat.mul_comm]
end Counter
namespace RootCode
open InputCode

noncomputable def g : Code Parsed Count := width ≫ₚ NaturalLog.length ≫ₚ Counter.inc ≫ₚ Counter.inc
noncomputable def argument : Code Parsed Count := (const (List.replicate (2^17) ()) ⋏ₚ g) ≫ₚ Counter.mul
noncomputable def exponent : Code Parsed Count := argument ≫ₚ Counter.word ≫ₚ NaturalLog.ceil
noncomputable def cap : Code Parsed Count := (argument ⋏ₚ argument) ≫ₚ Counter.add
noncomputable def samples : Code Parsed Count := (exponent ⋏ₚ cap) ≫ₚ Counter.power
noncomputable def trialBase : Code Parsed Count := (samples ⋏ₚ (n ≫ₚ Counter.inc)) ≫ₚ Counter.mul ≫ₚ Counter.fixedPower 6
noncomputable def trials : Code Parsed Count := (trialBase ⋏ₚ trialBase) ≫ₚ Counter.add ≫ₚ Counter.inc
noncomputable def basic : Code Parsed Count := (n ⋏ₚ ((const (List.replicate 128 ()) ⋏ₚ samples) ≫ₚ Counter.mul)) ≫ₚ Counter.mul
noncomputable def env : Code Parsed RawControl.Env := rows ⋏ₚ exponent ⋏ₚ samples ⋏ₚ trials ⋏ₚ basic

end RootCode
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace RootCode
open InputCode
noncomputable def ones : Code Parsed (List W) := n ≫ₚ map (Word.constant 1)
noncomputable def budgets : Code Parsed RawBudget.Data :=
  ((n ≫ₚ Counter.word) ⋏ₚ Word.constant 1) ⋏ₚ
  ((n ≫ₚ Counter.word) ⋏ₚ Word.constant 1) ⋏ₚ ones ⋏ₚ ones
noncomputable def box : Code Parsed RawBox.Data :=
  width ⋏ₚ (n ≫ₚ map (Word.constant 0)) ⋏ₚ ((width ⋏ₚ n) ≫ₚ envMap (fst : Code (W×Unit) W))
noncomputable def state : Code Parsed RawControl.State :=
  RawControl.call 0 (RawControl.pack budgets box) (const [])
end RootCode
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Preparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Preparation
abbrev Seed := (Count×Count)×(W×RawControl.Acc)
abbrev Aux := (Count×Count)×Count×(W×RawControl.Acc)
noncomputable def inputLength : Code Digits Count := by
  let F := Map.device (TreeDevice.constant boolData Median.unitData ())
  refine ⟨fun d => d.bits.map (fun _ => ()),F.recode encode encode Digits.bits
    (fun d => d.bits.map (fun _ => ())) (fun _ => rfl) (fun _ => rfl),?_⟩
  obtain ⟨K,d,h⟩ := PolynomialCost.map (LinearCost.constant boolData Median.unitData ()).polynomial
  exact ⟨K,d,fun z => h z.bits⟩
noncomputable def logarithm : Code Digits Count :=
  inputLength ≫ₚ Counter.inc ≫ₚ Counter.inc ≫ₚ Counter.word ≫ₚ NaturalLog.ceil
noncomputable def exponent : Code Digits Count :=
  ((const (List.replicate 25000 ())) ⋏ₚ (logarithm ≫ₚ Counter.fixedPower 2)) ≫ₚ Counter.mul
noncomputable def root : Code Digits Seed := InputCode.parse ≫ₚ
  ((RootCode.exponent ⋏ₚ RootCode.samples) ⋏ₚ (InputCode.width ⋏ₚ (RootCode.env ⋏ₚ RootCode.state)))
noncomputable def seed : Code Digits (Count×Seed) := exponent ⋏ₚ root
noncomputable def inflate : Device encode encode
    (fun z : Count×Seed => (Fold.fold Allocation.double.eval [()] z.1,z.2)) :=
  pairMap Allocation.device (TreeDevice.identity encode)
noncomputable def assemble : Code (Count×Seed) (Count×Aux) :=
  (((snd ≫ₚ fst ≫ₚ fst) ⋏ₚ fst) ≫ₚ Counter.mul) ⋏ₚ ((snd ≫ₚ fst) ⋏ₚ fst ⋏ₚ (snd ≫ₚ snd))
noncomputable def value (d : Digits) : Count×Aux :=
  assemble (Fold.fold Allocation.double.eval [()] (exponent d),root d)
noncomputable def device : Device encode encode value :=
  @compose Digits (Count×Seed) (Count×Aux) encode encode encode seed.eval
    (fun z => assemble (Fold.fold Allocation.double.eval [()] z.1,z.2)) seed.device
    (@compose (Count×Seed) (Count×Seed) (Count×Aux) encode encode encode
      (fun z => (Fold.fold Allocation.double.eval [()] z.1,z.2)) assemble.eval inflate assemble.device)
end Preparation
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.TreeDevice.Certified.Preparation
open BinaryData
noncomputable def resource (d : Digits) : ℕ := treeSize (encode d)+2^(exponent d).length
end MeanPayoff.TreeDevice.Certified.Preparation

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Traces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace Counter
 theorem bounded_length (w : W) (cap : Count) : (bounded (w,cap)).length ≤ cap.length := by
  have hf : ∀ (xs : List Bool) (s : Address.State),
      (Fold.fold Address.step s xs).2.length ≤ s.2.length+xs.length := by
    intro xs
    induction xs with
    | nil => intro s; simp [Fold.fold]
    | cons b bs ih =>
      intro s
      have h := ih (Address.step (s,b))
      change (Fold.fold Address.step (Address.step (s,b)) bs).2.length≤_
      have hg : (Address.step (s,b)).2.length ≤ s.2.length+1 := by
        simp only [Address.step]
        split <;> simp
      simp only [List.length_cons]
      omega
  have h := hf (cap.map (fun _ => false)) (w,[])
  change (Fold.fold Address.step (w,[]) (cap.map (fun _ => false))).2.length≤_
  simpa using h
end Counter
namespace Chunks
noncomputable def split : Code (Digits×Count) (Digits×Digits) := by
  refine ⟨fun z => (⟨(Split.split (z.1.bits,z.2)).1⟩,⟨(Split.split (z.1.bits,z.2)).2⟩),
    Split.device.recode encode encode (fun z : Digits×Count => (z.1.bits,z.2))
      (fun z : Digits×Count => ((⟨(Split.split (z.1.bits,z.2)).1⟩ : Digits),(⟨(Split.split (z.1.bits,z.2)).2⟩ : Digits)))
      (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := Split.polynomial
  exact ⟨K,d,fun z => h (z.1.bits,z.2)⟩
noncomputable def positive : Code Digits W := by
  refine ⟨fun d => IntegerRead.positive d.bits, IntegerRead.positiveDevice.recode encode encode Digits.bits
    (fun d => IntegerRead.positive d.bits) (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := IntegerRead.positive_linear.polynomial
  exact ⟨K,d,fun z => h z.bits⟩
noncomputable def reverseDigits : Code Digits Digits := by
  refine ⟨fun d => ⟨d.bits.reverse⟩, (Lists.reverseDevice boolData).recode encode encode Digits.bits
    (fun d => (⟨d.bits.reverse⟩ : Digits)) (fun _ => rfl) (fun _ => rfl), ?_⟩
  obtain ⟨K,d,h⟩ := PolynomialCost.reverse boolData
  exact ⟨K,d,fun z => h z.bits⟩
abbrev State := (Count×Count)×(List Count×Digits)
noncomputable def params : Code State (Count×Count) := fst
noncomputable def acc : Code State (List Count) := snd ≫ₚ fst
noncomputable def bits : Code State Digits := snd ≫ₚ snd
noncomputable def pieces : Code State (Digits×Digits) := (bits ⋏ₚ (params ≫ₚ fst)) ≫ₚ split
noncomputable def sample : Code State Count := (((pieces ≫ₚ fst) ≫ₚ reverseDigits ≫ₚ positive) ⋏ₚ (params ≫ₚ snd)) ≫ₚ Counter.bounded
noncomputable def next : Code State State := params ⋏ₚ ((sample ⋏ₚ acc) ≫ₚ cons) ⋏ₚ (pieces ≫ₚ snd)
noncomputable def step : Code (State×Unit) State := fst ≫ₚ next
 theorem next_params (s : State) : (next s).1=s.1 := rfl
 theorem next_acc (s : State) : (next s).2.1=sample s::s.2.1 := rfl
 theorem next_bits (s : State) : (next s).2.2.bits=s.2.2.bits.drop s.1.1.length := by
  change (Split.split (s.2.2.bits,s.1.1)).2=_
  exact Split.rest _ _
 theorem sample_length (s : State) : (sample s).length ≤ s.1.2.length := Counter.bounded_length _ _
 theorem next_size (s : State) : treeSize (encode (next s))≤treeSize (encode s)+(2*s.1.2.length+2) := by
  have h := sample_length s
  have hr : treeSize (encode (next s).2.2)≤treeSize (encode s.2.2) := by
    change treeSize (listTree boolData (next s).2.2.bits) ≤ treeSize (listTree boolData s.2.2.bits)
    rw [next_bits]
    exact listTree_drop_le _ _ _
  have hshape (t : State) : treeSize (encode t)=
      treeSize (encode t.1)+(treeSize (encode t.2.1)+treeSize (encode t.2.2)+1)+1 := by
    rcases t with ⟨p,a,d⟩
    simp only [Size.pair]
  rw [hshape (next s),next_params,next_acc]
  have hc : treeSize (encode (sample s::s.2.1))=treeSize (encode (sample s))+treeSize (encode s.2.1)+1 :=
    treeSize_pair _ _
  rw [hc,Size.count,hshape s]
  omega
 theorem fold_size (s : State) (cs : Count) : treeSize (encode (Fold.fold step.eval s cs))≤
    treeSize (encode s)+cs.length*(2*s.1.2.length+2) := by
  induction cs generalizing s with
  | nil => simp [Fold.fold]
  | cons u cs ih =>
    have h := ih (next s)
    rw [next_params] at h
    have hn := next_size s
    change treeSize (encode (Fold.fold step.eval (next s) cs))≤_
    rw [List.length_cons]
    nlinarith
 theorem prefix_size (s : State) (cs : Count) (k : ℕ) (hk : k ≤ cs.length) :
    treeSize (encode (Fold.fold step.eval s (cs.take k)))≤5*(treeSize (encode (s,cs))+1)^2 := by
  let N := treeSize (encode (s,cs))+1
  have hs : treeSize (encode s)≤N := (Size.fst (s,cs)).trans (Nat.le_succ _)
  have hc : cs.length≤N := (Size.length _).trans ((Size.snd (s,cs)).trans (Nat.le_succ _))
  have hp : s.1.2.length≤N := (Size.length _).trans ((Size.snd _).trans ((Size.fst _).trans hs))
  have h := fold_size s (cs.take k)
  have hl : (cs.take k).length≤N := (List.length_take_le _ _).trans (hk.trans hc)
  have hm := Nat.mul_le_mul hl (show 2*s.1.2.length+2≤2*N+2 by omega)
  have hn : 1≤N := Nat.le_add_left _ _
  change _≤5*N^2
  nlinarith
noncomputable def fold : Code (State×Count) State := foldPrefix step 5 2 prefix_size
noncomputable def run : Code ((Count×Count)×Digits×Count) (List Count) :=
  ((fst ⋏ₚ ((const [] : Code ((Count×Count)×Digits×Count) (List Count)) ⋏ₚ (snd ≫ₚ fst))) ⋏ₚ (snd ≫ₚ snd)) ≫ₚ fold ≫ₚ snd ≫ₚ fst ≫ₚ reverse
end Chunks
end MeanPayoff.TreeDevice.Certified

end

section
namespace MeanPayoff.RandomTree
 theorem all_of_read {α : Type} (t : RandomTree α) (Q : α→Prop)
    (h : ∀ bits : ℕ→Bool, Q (t.read bits)) : t.All Q := by
  induction t with
  | leaf a => exact h (fun _ => false)
  | coin l r il ir =>
    constructor
    · apply il
      intro bits
      simpa only [read, Bool.false_eq_true, ↓reduceIte] using
        h (fun | 0 => false | j+1 => bits j)
    · apply ir
      intro bits
      simpa only [read, ↓reduceIte] using
        h (fun | 0 => true | j+1 => bits j)
end MeanPayoff.RandomTree
namespace MeanPayoff.RegisterBits
open RandomTree BinaryData.Take

def Traces {K : ℕ} (P : Program K) (c : Config P) (t : RandomTree (Config P)) : Prop :=
  ∀ (bits : ℕ→Bool) (pos : ℕ), advance P (fun j => bits (pos+j)) c
    ((t.consume bits pos).2-pos) = (t.consume bits pos).1
end MeanPayoff.RegisterBits

end

section
namespace MeanPayoff.RandomTree
@[simp] theorem map_leaf' {α β : Type} (f : α→β) (a : α) : (leaf a).map f=leaf (f a) := rfl
@[simp] theorem map_coin' {α β : Type} (f : α→β) (l r : RandomTree α) :
    (coin l r).map f=coin (l.map f) (r.map f) := rfl
end MeanPayoff.RandomTree
namespace MeanPayoff.FairBits
open RandomTree

def draw : ℕ→RandomTree (List Bool)
  | 0 => .leaf []
  | n+1 => .coin ((draw n).map (false::·)) ((draw n).map (true::·))
def acc : ℕ→List Bool→RandomTree (List Bool)
  | 0,bs => .leaf bs
  | n+1,bs => .coin (acc n (false::bs)) (acc n (true::bs))
end MeanPayoff.FairBits

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Chunks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.TreeDevice.Certified.Chunks
open BinaryData
open BinaryStack.Addition (value)
def decode (e : ℕ) : ℕ→List Bool→List Count
  | 0,_ => []
  | n+1,bs => List.replicate (value (bs.take e).reverse) () :: decode e n (bs.drop e)
end MeanPayoff.TreeDevice.Certified.Chunks

end

section
namespace MeanPayoff.TreeDevice.Certified
open BinaryData Code
local infixl:80 " ≫ₚ " => Code.comp
local infixr:70 " ⋏ₚ " => Code.pair
namespace PostCode
abbrev Input := Digits×Preparation.Aux
noncomputable def samples : Code Input (List Count) :=
  ((snd ≫ₚ fst) ⋏ₚ (fst ≫ₚ Chunks.reverseDigits) ⋏ₚ (snd ≫ₚ snd ≫ₚ fst)) ≫ₚ Chunks.run
noncomputable def start : Code Input (W×RawControl.Acc) := snd ≫ₚ snd ≫ₚ snd
noncomputable def execute : Code Input (W×RawControl.Acc) :=
  (start ≫ₚ fst) ⋏ₚ (((start ≫ₚ snd) ⋏ₚ samples) ≫ₚ RawControl.loop)
noncomputable def returned : Code (W×RawControl.Acc) (W×List W) :=
  fst ⋏ₚ (snd ≫ₚ snd ≫ₚ fst ≫ₚ snd ≫ₚ RawControl.q)
noncomputable def classify : Code (W×List W) (List Bool) :=
  ((fst ≫ₚ Word.half) ⋏ₚ snd) ≫ₚ envMap Word.lt
noncomputable def boolean : Device Compare.bitTree boolData (fun b : Bool => b) :=
  (TreeDevice.branch (TreeDevice.identity Compare.bitTree)
    (TreeDevice.constant Compare.bitTree boolData true)
    (TreeDevice.constant Compare.bitTree boolData false)).extFun (by intro b; cases b <;> rfl)
 theorem boolean_poly : PolynomialCost boolean :=
  PolynomialCost.branch (LinearCost.identity _).polynomial (LinearCost.constant _ _ _).polynomial
    (LinearCost.constant _ _ _).polynomial
noncomputable def digits : Code (List Bool) Digits := by
  let D := Map.device boolean
  refine ⟨Digits.mk,D.recode encode encode _root_.id Digits.mk (fun _ => rfl) (fun _ => ?_),?_⟩
  · simp [encode]
  · obtain ⟨K,d,h⟩ := PolynomialCost.map boolean_poly
    exact ⟨K,d,fun z => h z⟩
noncomputable def run : Code Input Digits := execute ≫ₚ returned ≫ₚ classify ≫ₚ digits
end PostCode
end MeanPayoff.TreeDevice.Certified

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_RandomTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.RandomTable
open RegisterBits BinaryData TreeDevice
open BinaryData.Take (advance_add config_ext)
variable (pre post : RegisterBits.Program 5)
noncomputable def flow : Flow.Program 5 where
  nodes := 12
  start := 0
  block p := if p=0 then pre else if p=9 then moveCode 1 0 else if p=11 then post else skip
  read p := if p=2 ∨ p=5 ∨ p=6 ∨ p=7 ∨ p=8 then 1 else 0
  next p top bit := match p.val with
    | 0 => some ⟨1,.keep,none⟩
    | 1 => some ⟨2,.pop,none⟩
    | 2 => some ⟨3,.push false,none⟩
    | 3 => some ⟨if top=some true then 4 else 9,.pop,none⟩
    | 4 => some ⟨5,.pop,none⟩
    | 5 => some ⟨if bit then 6 else 8,.push false,none⟩
    | 6 => some ⟨7,.push false,none⟩
    | 7 => some ⟨8,.push true,none⟩
    | 8 => some ⟨3,.push true,none⟩
    | 9 => some ⟨10,.keep,none⟩
    | 10 => some ⟨11,.push true,none⟩
    | _ => none
noncomputable def program := Flow.compile (flow pre post)
noncomputable def cfg (p : Fin 12) (xs ys : List Bool) (out : List Bool) : Config (program pre post) :=
  Flow.state (flow pre post) p (core xs ys []) out
noncomputable def edge (p : Fin 12) (xs ys : List Bool) (out : List Bool) : Config (program pre post) :=
  Flow.edge (flow pre post) p (core xs ys []) out
end MeanPayoff.RandomTable

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Realizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
noncomputable def preTail : Program 5 := Sequence5.program (moveCode 1 0) Preparation.device.program
noncomputable def pre : Program 5 := Sequence5.program Box5.program preTail
noncomputable def preCost (d : Digits) : ℕ :=
  (2*d.bits.length+2+feedCost d.bits+1)+(6*treeSize (encode d)+3+Preparation.device.limit d+2)+2
noncomputable def post : Program 5 := Sequence5.program PostCode.run.device.program Emit.program
noncomputable def postCost (z : PostCode.Input) : ℕ := PostCode.run.device.limit z+Emit.cost (PostCode.run z).bits+2
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
noncomputable def program : Program 5 := RandomTable.program pre post
noncomputable def aux (d : Digits) : Preparation.Aux := (Preparation.value d).2
noncomputable def amount (d : Digits) : ℕ := (Preparation.value d).1.length
noncomputable def answer (d : Digits) (bs : List Bool) : List Bool := (PostCode.run (⟨bs⟩,aux d)).bits
 noncomputable def postBudget (K e : ℕ) (d : Digits) : ℕ :=
   K*(4*amount d+treeSize (encode (aux d))+3)^e
 noncomputable def limit (K e : ℕ) (d : Digits) : ℕ := preCost d+36*amount d+postBudget K e d+20
end MeanPayoff.Realizer

end

end OAI
end

section
-- module Solutions.OAIQ117_RM.RandomMean_Complexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MeanPayoff.Realizer
open TreeDevice TreeDevice.Certified BinaryData RandomTree
noncomputable def iterations (d : Digits) : ℕ := 2^(Preparation.exponent d).length
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
noncomputable def total (K e : ℕ) (d : Digits) : ℕ :=
  2*Compile.bound program d.bits (limit K e d)
end MeanPayoff.Realizer

end

end OAI
end


