-- Prove2me | Definitions.Def_OAIB3Sq000
-- name    : OAIB3Sq000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T12:07:57.804122+00:00
-- url     : https://prove2.me/theorems/3c3330a0-a2a0-4d6c-bd83-eea30e91bf36
-- title:
--   Definitions bundle OAIB3Sq000 of the split of OpenAI, A power saving for square-difference-free sets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SquareDifference.power_saving`, carved from OpenAI's openai/math development (OpenAI, *A power saving for square-difference-free sets*, OpenAI Math Release, September 24, 2026, result family 182, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 351 declarations of OpenAI's Lean: 293 definitions, 1 inductive type or structure, 12 instances and 45 theorems. The definitions and types are `OAI.LiftAnalysis.SquareDifference.ExactSupport`, `OAI.LiftAnalysis.SquareDifference.ResidueSpace`, `OAI.LiftAnalysis.SquareDifference.boolChar`, `OAI.LiftAnalysis.SquareDifference.boolMul`, `OAI.LiftAnalysis.SquareDifference.boolMulEquiv`, `OAI.LiftAnalysis.SquareDifference.boolSign`, `OAI.LiftAnalysis.SquareDifference.circleDistance`, `OAI.LiftAnalysis.SquareDifference.coordinateFreeze`, `OAI.LiftAnalysis.SquareDifference.copyDifference`, `OAI.LiftAnalysis.SquareDifference.copySwapEquiv`, `OAI.LiftAnalysis.SquareDifference.exactGate`, `OAI.LiftAnalysis.SquareDifference.expPhase`, `OAI.LiftAnalysis.SquareDifference.fourierPolynomial`, `OAI.LiftAnalysis.SquareDifference.frequencyAngle`, `OAI.LiftAnalysis.SquareDifference.gateCoefficient`, `OAI.LiftAnalysis.SquareDifference.hybrid`, `OAI.LiftAnalysis.SquareDifference.liftPiece`, `OAI.LiftAnalysis.SquareDifference.patch`, `OAI.LiftAnalysis.SquareDifference.primeSupport`, `OAI.LiftAnalysis.SquareDifference.prodChar`, `OAI.LiftAnalysis.SquareDifference.remainingFamily`, `OAI.LiftAnalysis.SquareDifference.residueGate`, `OAI.LiftAnalysis.SquareDifference.supportDenominator`, `OAI.LiftAnalysis.SquareDifference.supportFamily`, `OAI.LiftAnalysis.SquareDifference.supportNumerator`, `OAI.LiftAnalysis.SquareDifference.truncatedLift`, `OAI.LiftAnalysis.SquareDifference.walsh`, `OAI.LiftAnalysis.SquareDifference.walshEnergy`, `OAI.LiftTheory.SquareDifference.HasFourierBound`, `OAI.LiftTheory.SquareDifference.OutsideModulus`, `OAI.LiftTheory.SquareDifference.ResidueSpace`, `OAI.LiftTheory.SquareDifference.coordinateFreeze`, `OAI.LiftTheory.SquareDifference.exactGate`, `OAI.LiftTheory.SquareDifference.expPhase`, `OAI.LiftTheory.SquareDifference.fourierPolynomial`, `OAI.LiftTheory.SquareDifference.frequencyAngle`, `OAI.LiftTheory.SquareDifference.gateCoefficient`, `OAI.LiftTheory.SquareDifference.liftPiece`, `OAI.LiftTheory.SquareDifference.outsideCoordinate`, `OAI.LiftTheory.SquareDifference.primeSieveWeight` and 254 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `SquareDifference_AffineTuples`, `SquareDifference_BlockParameters`, `SquareDifference_CRTTransfer`, `SquareDifference_CircleDistance`, `SquareDifference_CompleteWeights`, `SquareDifference_ConductorBounds`, `SquareDifference_CrossProducts`, `SquareDifference_CyclicIndicator`, `SquareDifference_DualCoordinates`, `SquareDifference_Endpoint`, `SquareDifference_ExceptionalBasics`, `SquareDifference_FiniteKernel`, `SquareDifference_FourierLift`, `SquareDifference_GateExpansion`, `SquareDifference_GaussSum`, `SquareDifference_IntervalLift`, `SquareDifference_IntervalTruncation`, `SquareDifference_Main`, `SquareDifference_MarkedTuples`, `SquareDifference_MatrixBounds`, `SquareDifference_MixedEnergy`, `SquareDifference_OrderedBlock`, `SquareDifference_OrderedRates`, `SquareDifference_OutsideFourier`, `SquareDifference_PairBridge`, `SquareDifference_PhaseBounds`, `SquareDifference_PowerParameters`, `SquareDifference_PrimaryKernel`, `SquareDifference_PrimeExtension`, `SquareDifference_PrimeGauss`, `SquareDifference_PrimeSetup`, `SquareDifference_ProductBounds`, `SquareDifference_RationalApproximation`, `SquareDifference_RationalLift`, `SquareDifference_ReflectionLaw`, `SquareDifference_ResidueFourier`, `SquareDifference_ResidueLift`, `SquareDifference_ResidueReindex`, `SquareDifference_RootModels`, `SquareDifference_ScaleTransfer`, `SquareDifference_SelectedRoots`, `SquareDifference_SievedFourier`, `SquareDifference_SmallGood`, `SquareDifference_SmallRoots`, `SquareDifference_TensorLaw`, `SquareDifference_TensorPair`, `SquareDifference_TransferRates`, `SquareDifference_TupleEnergy`, `SquareDifference_TupleReflection`, `SquareDifference_TupleWeights`, `SquareDifference_UniformRates`, `SquareDifference_UniformTransfer`, `SquareDifference_WalshMoments`, `SquareDifference_WordReflection`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.SquareDifference.interval_low_pair` and `OAI.SquareDifference.source_ordered_contraction`; the proofs of `OAI.SquareDifference.interval_low_pair`, `OAI.SquareDifference.power_saving` and `OAI.SquareDifference.source_ordered_contraction`.
-- source:
--   OpenAI, A power saving for square-difference-free sets, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 182; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-square-difference-free-sets-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib

section
-- module Solutions.OAIB3_Sqd.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_GaussSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

noncomputable def squareIndicator {F : Type*} [Field F] (x : F) : ℝ :=
  by
  classical
  exact if x ≠ 0 ∧ IsSquare x then 1 else 0

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_MixedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

def directedCrossEdge {I J A B : Type*} (dir : I → J → Bool)
    (e : (I × J) × (A × B)) : ((I × A) ⊕ (J × B)) × ((I × A) ⊕ (J × B)) :=
  if dir e.1.1 e.1.2 then
    (Sum.inl (e.1.1, e.2.1), Sum.inr (e.1.2, e.2.2))
  else (Sum.inr (e.1.2, e.2.2), Sum.inl (e.1.1, e.2.1))

noncomputable def listKernel {I J : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × J)) (dir : I → J → Bool) (x : I → ZMod p) (y : J → ZMod p) : ℝ :=
  ∏ e ∈ E, if dir e.1 e.2 then squareIndicator (y e.2 - x e.1)
    else squareIndicator (x e.1 - y e.2)

def fourListsEquiv (I J X : Type*) :
    ((I × Bool) ⊕ (J × Bool) → X) ≃ ((I → X) × (I → X)) × ((J → X) × (J → X)) where
  toFun z := ((fun i => z (.inl (i, false)), fun i => z (.inl (i, true))),
    (fun j => z (.inr (j, false)), fun j => z (.inr (j, true))))
  invFun z := fun w => match w with
    | .inl (i, false) => z.1.1 i
    | .inl (i, true) => z.1.2 i
    | .inr (j, false) => z.2.1 j
    | .inr (j, true) => z.2.2 j
  left_inv z := by funext w; rcases w with ⟨i, b⟩ | ⟨j, b⟩ <;> cases b <;> rfl
  right_inv z := rfl

noncomputable def indexCross {I J : Type*} [Fintype I] [DecidableEq J]
    (A : Matrix I I ℝ) (j k : I → J) : ℝ :=
  ∑ x : I, ∑ y : I, A x y * (if j x = k y then 1 else 0)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_MatrixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

abbrev WordVertex (B : Type*) (h : ℕ) := B → Equiv.Perm (Fin h)

abbrev PositionPair (h : ℕ) := {p : Fin h × Fin h // p.1 < p.2}

def vertexSwap {B : Type*} [DecidableEq B] {h : ℕ}
    (v : WordVertex B h) (b : B) (p : PositionPair h) : WordVertex B h :=
  Function.update v b (v b * Equiv.swap p.1.1 p.1.2)

def reflect {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : WordVertex B h) : WordVertex B h :=
  Function.update v b (Equiv.swap α β * v b)

def cutPlus {B : Type*} {h : ℕ} (b : B) (α β : Fin h) (v : WordVertex B h) : Prop :=
  (v b).symm α < (v b).symm β

instance cutPlusDecidable {B : Type*} {h : ℕ} (b : B) (α β : Fin h) :
    DecidablePred (cutPlus b α β) :=
  fun v => inferInstanceAs (Decidable ((v b).symm α < (v b).symm β))

lemma reflect_involutive {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) : Function.Involutive (reflect b α β) := by
  intro v
  ext a
  by_cases hab : a = b
  · subst a
    simp [reflect, ← mul_assoc]
  · simp [reflect, hab]

lemma reflect_cutPlus {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (v : WordVertex B h) :
    cutPlus b α β (reflect b α β v) ↔ (v b).symm β < (v b).symm α := by
  simp [cutPlus, reflect, Equiv.Perm.mul_def]

noncomputable def interaction {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (v w : WordVertex B h) : ℝ :=
  ∑ b ∈ S, ∑ p : PositionPair h,
    if w = vertexSwap v b p then δ ^ (p.1.2.val - p.1.1.val) else 0

abbrev CutHalf {B : Type*} {h : ℕ} (b : B) (α β : Fin h) :=
  {v : WordVertex B h // cutPlus b α β v}

noncomputable def crossInteraction {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (S : Finset B) (δ : ℝ) (b : B) (α β : Fin h) :
    Matrix (CutHalf b α β) (CutHalf b α β) ℝ :=
  Matrix.of fun x y => interaction S δ x.1 (reflect b α β y.1)

def tupleH : ℕ := 24

def tupleT : ℕ := 80

def tupleBlocks : ℕ := 2 * tupleT + 1

noncomputable def tupleDelta : ℝ := 1 / (10 * (tupleH : ℝ) ^ 2)

noncomputable def tupleKappa : ℝ := (9 / 10) * tupleDelta ^ (tupleH - 1)

lemma cutPlus_reflect_iff_not {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) (v : WordVertex B h) :
    cutPlus b α β (reflect b α β v) ↔ ¬ cutPlus b α β v := by
  rw [reflect_cutPlus]
  have hne : (v b).symm α ≠ (v b).symm β := (v b).symm.injective.ne hαβ
  exact lt_iff_not_ge.trans (not_congr (le_iff_lt_or_eq.trans (or_iff_left hne)))

noncomputable def halfSumEquiv {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) :
    CutHalf b α β ⊕ CutHalf b α β ≃ WordVertex B h where
  toFun := Sum.elim Subtype.val (fun v => reflect b α β v.1)
  invFun := fun v => if hp : cutPlus b α β v then Sum.inl ⟨v, hp⟩ else
    Sum.inr ⟨reflect b α β v, (cutPlus_reflect_iff_not b hαβ v).mpr hp⟩
  left_inv := by
    rintro (x | x)
    · simp [x.2]
    · have hn : ¬ cutPlus b α β (reflect b α β x.1) := by
        rw [cutPlus_reflect_iff_not b hαβ]
        exact not_not.mpr x.2
      simp [hn]
      exact Subtype.ext (reflect_involutive b α β x.1)
  right_inv := by
    intro v
    by_cases hv : cutPlus b α β v
    · simp [hv]
    · simp only [dite_eq_right hv, Sum.elim_inr]
      exact reflect_involutive b α β v

lemma card_cutHalf {B : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) {α β : Fin h} (hαβ : α ≠ β) :
    2 * Fintype.card (CutHalf b α β) = (Nat.factorial h) ^ Fintype.card B := by
  classical
  have hh := Fintype.card_congr (halfSumEquiv b hαβ)
  simpa [Fintype.card_sum, Fintype.card_fun, Fintype.card_perm, two_mul] using hh

def addressEdge {B G : Type*} [Fintype B] [DecidableEq G] [Group G]
    (c : G) (T : ℕ) (u v : B → G) : Prop :=
  T ≤ (univ.filter fun b => v b = u b * c).card

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TupleEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

noncomputable def indexEnergy {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (j : I → J) : ℝ := (1 / 2) * indexCross H j j

noncomputable def indexWeight {I J : Type*} [Fintype I] [DecidableEq J]
    (H : Matrix I I ℝ) (j : I → J) : ℝ := Real.exp (indexEnergy H j)

abbrev TupleVertex := WordVertex (Fin tupleBlocks) tupleH

abbrev TupleAddress (S : Finset (Fin tupleBlocks)) :=
  {b : Fin tupleBlocks // b ∉ S} → Equiv.Perm (Fin tupleH)

def tupleR : ℕ := Nat.factorial tupleH / 2

abbrev TupleListIndex (S : Finset (Fin tupleBlocks)) := Fin (tupleR ^ S.card)

abbrev TupleListEntry (S : Finset (Fin tupleBlocks)) := TupleAddress S × TupleListIndex S

def tupleProjection (S : Finset (Fin tupleBlocks)) (v : TupleVertex) : TupleAddress S :=
  fun b => v b.1

def tupleCycle : Equiv.Perm (Fin tupleH) := finRotate tupleH

def cycleVertex (j : ℕ) : TupleVertex := fun _ => tupleCycle ^ j

noncomputable def tupleListEdges (S : Finset (Fin tupleBlocks)) :
    Finset (TupleListEntry S × TupleListEntry S) := by
  classical
  exact if S.card ≤ tupleT then
    univ.filter fun e => addressEdge tupleCycle (tupleT + 1) e.1.1 e.2.1 else ∅

noncomputable def tupleWeight (S : Finset (Fin tupleBlocks))
    (j : TupleVertex → TupleListIndex S) : ℝ := indexWeight (interaction S tupleDelta) j

noncomputable def tupleValidity {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) : ℝ :=
  ∏ e ∈ tupleListEdges S, squareIndicator (Y e.2 - Y e.1)

def tupleOutput {p : ℕ} (S : Finset (Fin tupleBlocks))
    (Y : TupleListEntry S → ZMod p) (j : TupleVertex → TupleListIndex S) :
    TupleVertex → ZMod p := fun v => Y (tupleProjection S v, j v)

noncomputable def tupleComponent {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (G : (TupleVertex → ZMod p) → ℝ) : ℝ :=
  𝔼 Y : TupleListEntry S → ZMod p, 𝔼 j : TupleVertex → TupleListIndex S,
    tupleValidity S Y * tupleWeight S j * G (tupleOutput S Y j)

noncomputable def tupleCutForm {p : ℕ} [Fact p.Prime] (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (F : (CutHalf b α β → ZMod p) → ℝ) : ℝ :=
  tupleComponent S (fun z => F (fun x => z x.1) * F (fun x => z (reflect b α β x.1)))

noncomputable def tupleWeightBound : ℝ :=
  Real.exp ((Fintype.card TupleVertex : ℝ) * (tupleT + 1) *
    (tupleH.choose 2 : ℝ) * tupleDelta / 2)

noncomputable def reflectEquiv {B : Type*} [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) : Equiv.Perm (WordVertex B h) :=
  Function.Involutive.toPerm (reflect b α β) (reflect_involutive b α β)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TupleReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference

noncomputable def tupleAddressReflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) : Equiv.Perm (TupleAddress S) :=
  Function.Involutive.toPerm
    (fun u a => (if a.1 = b then Equiv.swap α β else 1) * u a)
    (by
      intro u
      funext a
      by_cases ha : a.1 = b <;> simp [ha, ← mul_assoc])

noncomputable def tupleEntryReflect (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) : Equiv.Perm (TupleListEntry S) :=
  Equiv.prodCongr (tupleAddressReflect S b α β) (Equiv.refl _)

def symbolPotential {h : ℕ} (w : Equiv.Perm (Fin h)) : ℤ :=
  ∑ i : Fin h, (i.val : ℤ) * ((w.symm i).val : ℤ)

def wordPotential {B : Type*} [Fintype B] {h : ℕ} (v : WordVertex B h) : ℤ :=
  ∑ b : B, symbolPotential (v b)

def foldWord {B : Type*} [DecidableEq B] {h : ℕ} (b : B) (α β : Fin h)
    (v : WordVertex B h) : WordVertex B h :=
  if cutPlus b α β v then v else reflect b α β v

abbrev WordCut (B : Type*) (h : ℕ) := B × PositionPair h

def foldMap {B : Type*} [DecidableEq B] {h : ℕ} (cs : List (WordCut B h)) :
    WordVertex B h → WordVertex B h :=
  cs.foldr (fun c f => foldWord c.1 c.2.1.1 c.2.1.2 ∘ f) id

noncomputable def graphValidity {I : Type*} {p : ℕ} [Fact p.Prime]
    (E : Finset (I × I)) (z : I → ZMod p) : ℝ :=
  ∏ e ∈ E, squareIndicator (z e.2 - z e.1)

noncomputable def cutInternalEdges {I : Type*} [Fintype I]
    (E : Finset ((I ⊕ I) × (I ⊕ I))) : Finset (I × I) := by
  classical
  exact univ.filter fun e => (Sum.inl e.1, Sum.inl e.2) ∈ E

noncomputable def cutCrossEdges {I : Type*} [Fintype I]
    (E : Finset ((I ⊕ I) × (I ⊕ I))) : Finset (I × I) := by
  classical
  exact univ.filter fun e => (Sum.inl e.1, Sum.inr e.2) ∈ E ∨
    (Sum.inr e.2, Sum.inl e.1) ∈ E

noncomputable def cutCrossDirection {I : Type*}
    (E : Finset ((I ⊕ I) × (I ⊕ I))) (i j : I) : Bool := by
  classical
  exact decide ((Sum.inl i, Sum.inr j) ∈ E)

open scoped Classical

noncomputable def graphPullback {I K : Type*} [Fintype I]
    (e : I ≃ K) (E : Finset (K × K)) : Finset (I × I) := by
  classical
  exact univ.filter fun ij => (e ij.1, e ij.2) ∈ E

abbrev TupleHalfAddress (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    (α β : Fin tupleH) := CutHalf (⟨b, hb⟩ : {c : Fin tupleBlocks // c ∉ S}) α β

abbrev TupleHalfEntry (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    (α β : Fin tupleH) := TupleHalfAddress S b hb α β × TupleListIndex S

noncomputable instance tupleHalfEntryFintype (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) (α β : Fin tupleH) :
    Fintype (TupleHalfEntry S b hb α β) := by
  classical
  unfold TupleHalfEntry
  infer_instance

noncomputable def tupleEntryHalfEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    TupleHalfEntry S b hb α β ⊕ TupleHalfEntry S b hb α β ≃ TupleListEntry S :=
  (Equiv.sumProdDistrib _ _ _).symm.trans
    (Equiv.prodCongr (halfSumEquiv (⟨b, hb⟩ : {c : Fin tupleBlocks // c ∉ S}) hne) (Equiv.refl _))

def tupleHalfProjection (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (hb : b ∉ S) (α β : Fin tupleH) (x : CutHalf b α β) : TupleHalfAddress S b hb α β :=
  ⟨tupleProjection S x.1, x.2⟩

noncomputable def tupleHalfWeight (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (α β : Fin tupleH) (j : CutHalf b α β → TupleListIndex S) : ℝ :=
  indexWeight (Matrix.submatrix (interaction S tupleDelta) Subtype.val Subtype.val) j

noncomputable def tupleUnmarkedGraph (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :=
  graphPullback (tupleEntryHalfEquiv S b hb hne) (tupleListEdges S)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ReflectionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

noncomputable def tupleUnmarkedMoment {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks) (hb : b ∉ S)
    {α β : Fin tupleH} (hne : α ≠ β) (F : (CutHalf b α β → ZMod p) → ℝ) : ℝ :=
  𝔼 x : TupleHalfEntry S b hb α β → ZMod p,
  𝔼 j : CutHalf b α β → TupleListIndex S,
    graphValidity (cutInternalEdges (tupleUnmarkedGraph S b hb hne)) x *
      (F (fun v => x (tupleHalfProjection S b hb α β v, j v))) ^ 2

noncomputable def tupleUnmarkedConstant : ℝ :=
  (32 * (Fintype.card TupleVertex : ℝ)^2) ^ ((1 : ℝ) / 4) * tupleWeightBound^2

abbrev TupleCutWord (α β : Fin tupleH) :=
  {w : Equiv.Perm (Fin tupleH) // w.symm α < w.symm β}

noncomputable def orderedPermEquiv {h : ℕ} (α β : Fin h) :
    {w : Equiv.Perm (Fin h) // w.symm α < w.symm β} ≃ (CutHalf () α β : Type) where
  toFun w := ⟨fun _ => w.1, w.2⟩
  invFun w := ⟨w.1 (), w.2⟩
  left_inv _ := rfl
  right_inv w := by ext u; cases u; rfl

lemma card_orderedPerm {h : ℕ} {α β : Fin h} (hne : α ≠ β) :
    Fintype.card {w : Equiv.Perm (Fin h) // w.symm α < w.symm β} = Nat.factorial h / 2 := by
  have hh := card_cutHalf () hne
  rw [← Fintype.card_congr (orderedPermEquiv α β), Fintype.card_unit, pow_one] at hh
  omega

lemma card_tupleCutWord {α β : Fin tupleH} (hne : α ≠ β) :
    Fintype.card (TupleCutWord α β) = tupleR :=
  card_orderedPerm hne

def tupleMarkAddress (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (a : TupleAddress S) : TupleAddress (insert b S) :=
  fun c => a ⟨c.1, fun hc => c.2 (mem_insert_of_mem hc)⟩

def tupleUnmarkAddress (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (u : TupleAddress (insert b S)) (w : Equiv.Perm (Fin tupleH)) : TupleAddress S :=
  fun c => if hc : c.1 = b then w else u ⟨c.1, by simp [hc, c.2]⟩

lemma tupleUnmarkAddress_at (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S)
    (u : TupleAddress (insert b S)) (w : Equiv.Perm (Fin tupleH)) :
    tupleUnmarkAddress S b u w ⟨b, hb⟩ = w := by
  simp [tupleUnmarkAddress]

lemma tupleMark_unmark (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (u : TupleAddress (insert b S)) (w : Equiv.Perm (Fin tupleH)) :
    tupleMarkAddress S b (tupleUnmarkAddress S b u w) = u := by
  funext c
  have hb : c.1 ≠ b := by intro h; exact c.2 (by simp [h])
  simp [tupleMarkAddress, tupleUnmarkAddress, hb]

lemma tupleUnmark_mark (S : Finset (Fin tupleBlocks)) (b : Fin tupleBlocks)
    (hb : b ∉ S) (a : TupleAddress S) :
    tupleUnmarkAddress S b (tupleMarkAddress S b a) (a ⟨b,hb⟩) = a := by
  funext c
  by_cases hc : c.1 = b
  · have he : c = ⟨b,hb⟩ := Subtype.ext hc
    subst c
    simp [tupleUnmarkAddress]
  · simp [tupleUnmarkAddress, tupleMarkAddress, hc]

noncomputable def tupleHalfAddressEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) (α β : Fin tupleH) :
    TupleHalfAddress S b hb α β ≃ TupleAddress (insert b S) × TupleCutWord α β where
  toFun a := (tupleMarkAddress S b a.1, ⟨a.1 ⟨b,hb⟩, a.2⟩)
  invFun a := ⟨tupleUnmarkAddress S b a.1 a.2.1, by
    change (tupleUnmarkAddress S b a.1 a.2.1 ⟨b,hb⟩).symm α <
      (tupleUnmarkAddress S b a.1 a.2.1 ⟨b,hb⟩).symm β
    rw [tupleUnmarkAddress_at]
    exact a.2.2⟩
  left_inv a := Subtype.ext (tupleUnmark_mark S b hb a.1)
  right_inv a := by
    apply Prod.ext
    · exact tupleMark_unmark S b a.1 a.2.1
    · apply Subtype.ext
      exact tupleUnmarkAddress_at S b hb a.1 a.2.1

noncomputable def tupleMarkIndexEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    TupleListIndex (insert b S) ≃ TupleCutWord α β × TupleListIndex S :=
  Fintype.equivOfCardEq (by
    simp only [TupleListIndex, Fintype.card_fin, Fintype.card_prod,
      card_tupleCutWord hne, card_insert_of_notMem hb, pow_succ, mul_comm])

noncomputable def tupleRegroupEquiv (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    TupleHalfEntry S b hb α β ≃ TupleListEntry (insert b S) :=
  ((Equiv.prodCongr (tupleHalfAddressEquiv S b hb α β) (Equiv.refl _)).trans
    (Equiv.prodAssoc _ _ _)).trans
      (Equiv.prodCongr (Equiv.refl _) (tupleMarkIndexEquiv S b hb hne).symm)

def tupleWordOfHalf (b : Fin tupleBlocks) (α β : Fin tupleH) (v : CutHalf b α β) :
    TupleCutWord α β := ⟨v.1 b, v.2⟩

def tupleHalfCount : ℕ := (Nat.factorial tupleH)^tupleBlocks / 2

noncomputable def tupleMarkedConstant : ℝ :=
  (Real.exp tupleKappa - 1)^tupleHalfCount /
    ((tupleR : ℝ)^(tupleT + 1))^tupleHalfCount

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_MarkedTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

noncomputable def tupleReflectionThreshold : ℝ :=
  max 3 ((tupleUnmarkedConstant * (tupleR : ℝ)^tupleHalfCount /
    tupleMarkedConstant)^16)

noncomputable def tupleMixtureWeight (p : ℕ) (S : Finset (Fin tupleBlocks)) : ℝ :=
  (p : ℝ)^(-(S.card : ℝ)/16)

noncomputable def tupleMixture {p : ℕ} [Fact p.Prime]
    (G : (TupleVertex → ZMod p) → ℝ) : ℝ :=
  ∑ S ∈ (univ : Finset (Fin tupleBlocks)).powerset,
    if S.card ≤ tupleT + 1 then tupleMixtureWeight p S * tupleComponent S G else 0

noncomputable def tupleComponentMap {p : ℕ} [Fact p.Prime]
    (S : Finset (Fin tupleBlocks)) : ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ where
  toFun := tupleComponent S
  map_add' F G := by simp [tupleComponent, mul_add, expect_add_distrib]
  map_smul' c F := by
    simp only [tupleComponent, Pi.smul_apply, smul_eq_mul]
    simp_rw [show ∀ a b d : ℝ, a * b * (c * d) = c * (a * b * d) by intros; ring]
    simp_rw [← mul_expect]
    rfl

noncomputable def tupleMixtureMap {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ where
  toFun := tupleMixture
  map_add' F G := by
    unfold tupleMixture
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro S _
    split_ifs with hs
    · change _ * tupleComponentMap S (F+G) = _
      rw [map_add, mul_add]
      rfl
    · simp
  map_smul' c F := by
    change tupleMixture (c • F) = c * tupleMixture F
    unfold tupleMixture
    rw [mul_sum]
    apply sum_congr rfl
    intro S _
    split_ifs with hs
    · change _ * tupleComponentMap S (c • F) = _
      rw [map_smul, smul_eq_mul]
      change tupleMixtureWeight p S * (c * tupleComponent S F) =
        c * (tupleMixtureWeight p S * tupleComponent S F)
      ring
    · simp

noncomputable def tupleLeadingEdges : ℕ := (tupleListEdges ∅).card

noncomputable def tupleLeadingMassLower : ℝ := (1/2 : ℝ)^(tupleLeadingEdges+1)

noncomputable def tupleMassThreshold : ℝ :=
  max 3 (((2 : ℝ)^(tupleLeadingEdges+1) * tupleLeadingEdges)^2)

noncomputable def tupleLaw {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ :=
  (tupleMixture (p := p) (fun _ => 1))⁻¹ • tupleMixtureMap

noncomputable def multilinearIntegral {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (a : V → X → ℝ) : ℝ :=
  L (fun z => ∏ v, a v (z v))

noncomputable def diagonalIntegral {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) : ℝ :=
  multilinearIntegral L (fun _ => g)

noncomputable def halfProduct {B X : Type*} [Fintype B] [DecidableEq B] {h : ℕ}
    (b : B) (α β : Fin h) (a : WordVertex B h → X → ℝ)
    (x : CutHalf b α β → X) : ℝ := ∏ v, a v.1 (x v)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_WordReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

noncomputable def diagonalRoot {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) : ℝ :=
  (diagonalIntegral L g)^((1 : ℝ)/(Fintype.card V : ℝ))

noncomputable def cutKernel {Ω I : Type*} [DecidableEq I]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (left right : Ω → I) : Matrix I I ℝ :=
  fun x y => L (fun z => if left z = x ∧ right z = y then 1 else 0)

noncomputable def lawDensity {Ω : Type*} [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (x : Ω) : ℝ :=
  L (fun y => if y=x then 1 else 0)

noncomputable def tensorLaw {J V : Type*} [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] {X : J → Type*} [∀ j, Fintype (X j)]
    [∀ j, DecidableEq (X j)]
    (L : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) : ((V → ∀ j, X j) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := ∑ z : ∀ j, V → X j, (∏ j, lawDensity (L j) (z j)) * F (fun v j => z j v)
  map_add' F G := by simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' c F := by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← mul_sum, RingHom.id_apply]

noncomputable def productTupleLaw {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀ j, Fact (p j).Prime] :
    ((TupleVertex → ∀ j, ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw (fun j => tupleLaw (p := p j))

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_AffineTuples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

noncomputable def affineEquiv {F : Type*} [Field F] (q a : F) (hq : q ≠ 0) : F ≃ F where
  toFun x := q^2*x+a
  invFun y := (y-a)/q^2
  left_inv x := by field_simp; ring
  right_inv y := by field_simp; ring

noncomputable def conditionalEnergy {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) (f : X → ℝ) : ℝ :=
  𝔼 y, (𝔼 x, f x*W x y)^2/(𝔼 x, W x y)

noncomputable def jointDensity {Ω X Y : Type*} [Fintype Ω] [DecidableEq Ω]
    (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω ≃ X×Y) (x : X) (y : Y) : ℝ :=
  Fintype.card Ω * lawDensity L (e.symm (x,y))

noncomputable def splitIndex {V : Type*} [DecidableEq V] (v : V) :
    Unit ⊕ {w : V // w≠v} ≃ V where
  toFun := Sum.elim (fun _ => v) Subtype.val
  invFun w := if h : w=v then Sum.inl () else Sum.inr ⟨w,h⟩
  left_inv i := by cases i with
    | inl i => cases i; simp
    | inr i => simp [i.property]
  right_inv w := by by_cases h : w=v <;> simp [h]

noncomputable def crossEdges {I J : Type*} [Fintype I] [Fintype J]
    (E : Finset ((I⊕J)×(I⊕J))) : Finset (I×J) :=
  univ.filter fun e => (Sum.inl e.1,Sum.inr e.2)∈E ∨ (Sum.inr e.2,Sum.inl e.1)∈E

noncomputable def crossDir {I J : Type*} (E : Finset ((I⊕J)×(I⊕J)))
    (i : I) (j : J) : Bool := decide ((Sum.inl i,Sum.inr j)∈E)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CrossProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

noncomputable def tupleZeroIndex : TupleListIndex ∅ :=
  ⟨0, by simp only [card_empty, pow_zero]; decide⟩

instance tupleEmptyIndexSubsingleton : Subsingleton (TupleListIndex ∅) where
  allEq i j := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    simp only [card_empty, pow_zero] at hi hj
    omega

noncomputable def tupleLeadingEntry : TupleVertex ≃ TupleListEntry ∅ where
  toFun v := (tupleProjection ∅ v, tupleZeroIndex)
  invFun u b := u.1 ⟨b, by simp⟩
  left_inv v := rfl
  right_inv u := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _

noncomputable def tupleLeadingGraph : Finset (TupleVertex×TupleVertex) :=
  graphPullback tupleLeadingEntry (tupleListEdges ∅)

noncomputable def graphCondConstant {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V×V)) (v : V) : ℝ :=
  let m := (crossEdges (graphPullback (splitIndex v) E)).card
  (2/(1/2 : ℝ)^m+4/((1/2 : ℝ)^m)^2)*((32*m : ℝ)^((1:ℝ)/4))^2

noncomputable def graphRest {J : Type*} [Fintype J] {p : ℕ} [Fact p.Prime]
    (E : Finset ((Unit⊕J)×(Unit⊕J))) (y : J → ZMod p) : ℝ :=
  ∏i, ∏j, if (Sum.inr i,Sum.inr j)∈E then squareIndicator (y j-y i) else 1

noncomputable def tupleSubmixture {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) : ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ :=
  ∑S∈D, tupleMixtureWeight p S • tupleComponentMap S

noncomputable def tupleSubLaw {p : ℕ} [Fact p.Prime]
    (D : Finset (Finset (Fin tupleBlocks))) : ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ :=
  (tupleSubmixture (p := p) D (fun _ => 1))⁻¹ • tupleSubmixture D

noncomputable def tupleConditionalNumerator : ℝ :=
  (∑v : TupleVertex, graphCondConstant tupleLeadingGraph v)+
    ((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound

noncomputable def tupleConditionalConstant : ℝ := tupleConditionalNumerator/tupleLeadingMassLower

noncomputable def tupleConditionalThreshold : ℝ :=
  max tupleMassThreshold (max 3 (tupleConditionalConstant^32))

noncomputable def squarePairAverage {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F → F → ℝ) : ℝ := 𝔼 q : Fˣ, 𝔼 x, g x (x+(q : F)^2)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TupleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open scoped Classical

noncomputable def tupleFamily (n : ℕ) : Finset (Finset (Fin tupleBlocks)) :=
  univ.filter (fun S => S.card≤n)

noncomputable def tupleGoodLaw {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ := tupleSubLaw (tupleFamily tupleT)

noncomputable def tupleTerminalFamily : Finset (Finset (Fin tupleBlocks)) :=
  univ.filter (fun S => S.card=tupleT+1)

noncomputable def tupleExceptionalLaw {p : ℕ} [Fact p.Prime] :
    ((TupleVertex → ZMod p) → ℝ) →ₗ[ℝ] ℝ :=
  (tupleMixture (p := p) (fun _ => 1))⁻¹ • tupleSubmixture tupleTerminalFamily

noncomputable def tupleEta (p : ℕ) [Fact p.Prime] : ℝ := tupleExceptionalLaw (p := p) (fun _ => 1)

noncomputable def tupleExceptionalConstant : ℝ :=
  ((univ : Finset (Finset (Fin tupleBlocks))).card : ℝ)*tupleWeightBound/tupleLeadingMassLower

end SquareDifference

namespace SquareDifference

open Finset

noncomputable def kernelForm {X : Type*} [Fintype X]
    (K : Matrix X X ℝ) (f g : X → ℝ) : ℝ :=
  𝔼 x, 𝔼 y, f x*K x y*g y

noncomputable def conditionalGram {X Y : Type*} [Fintype X] [Fintype Y]
    (W : X → Y → ℝ) : Matrix X X ℝ :=
  fun x x' => 𝔼 y, W x y*W x' y/(𝔼 z, W z y)

noncomputable def noiseKernel {X : Type*} [Fintype X] [DecidableEq X]
    (δ : ℝ) : Matrix X X ℝ :=
  fun x y => 1-δ^2+δ^2*(Fintype.card X : ℝ)*(if x=y then 1 else 0)

noncomputable def coordOp {J : Type*} [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (j : J)
    (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ :=
  𝔼 t : X j, K j (x j) t*f (Function.update x j t)

def patch {J : Type*} [DecidableEq J] {X : J → Type*}
    (s : Finset J) (x y : ∀ j, X j) (j : J) : X j := if j∈s then y j else x j

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace SquareDifference
open Finset

noncomputable def partialOp {J : Type*} [Fintype J] [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)]
    (K : ∀ j, Matrix (X j) (X j) ℝ) (s : Finset J)
    (f : (∀ j, X j) → ℝ) (x : ∀ j, X j) : ℝ :=
  𝔼 y : ∀ j, X j, (∏ j ∈ s, K j (x j) (y j))*f (patch s x y)

def ExactSupport {J : Type*} [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (U : Finset J)
    (f : (∀ j, X j) → ℝ) : Prop :=
  (∀ j∈U, ∀ x, (𝔼 t : X j, f (Function.update x j t))=0) ∧
  (∀ j∉U, ∀ x t, f (Function.update x j t)=f x)

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_WalshMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators

namespace LiftAnalysis

open Finset

open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

def boolSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def walsh {J : Type*} [DecidableEq J] (s : Finset J)
    (c : Finset J → ℝ) (x : J → Bool) : ℝ :=
  ∑ U∈s.powerset, c U*∏ j∈U, boolSign (x j)

noncomputable def walshEnergy {J : Type*} [DecidableEq J] (s : Finset J)
    (C : ℝ) (c : Finset J → ℝ) : ℝ := ∑ U∈s.powerset, C^U.card*(c U)^2

def patch {J : Type*} [DecidableEq J] {X : J → Type*}
    (s : Finset J) (x y : ∀ j, X j) (j : J) : X j := if j∈s then y j else x j

def ExactSupport {J : Type*} [DecidableEq J]
    {X : J → Type*} [∀ j, Fintype (X j)] (U : Finset J)
    (f : (∀ j, X j) → ℝ) : Prop :=
  (∀ j∈U, ∀ x, (𝔼 t : X j, f (Function.update x j t))=0) ∧
  (∀ j∉U, ∀ x t, f (Function.update x j t)=f x)

def hybrid {J : Type*} {X : J → Type*} (b : J → Bool) (x y : ∀j, X j) (j : J) : X j :=
  if b j then x j else y j

def boolMul (a b : Bool) : Bool := if a then b else !b

lemma boolMul_self (a b : Bool) : boolMul a (boolMul a b)=b := by cases a <;> cases b <;> rfl

def copySwapEquiv {J : Type*} {X : J → Type*} (e : J → Bool) :
    ((∀j, X j) × (∀j, X j)) ≃ ((∀j, X j) × (∀j, X j)) where
  toFun a := (hybrid e a.1 a.2, hybrid e a.2 a.1)
  invFun a := (hybrid e a.1 a.2, hybrid e a.2 a.1)
  left_inv a := by
    apply Prod.ext <;> funext j <;> cases he : e j <;> simp [hybrid, he]
  right_inv a := by
    apply Prod.ext <;> funext j <;> cases he : e j <;> simp [hybrid, he]

def boolMulEquiv {J : Type*} (e : J → Bool) : (J → Bool) ≃ (J → Bool) where
  toFun b j := boolMul (e j) (b j)
  invFun b j := boolMul (e j) (b j)
  left_inv b := by funext j; exact boolMul_self _ _
  right_inv b := by funext j; exact boolMul_self _ _

noncomputable def boolChar {J : Type*} (U : Finset J) (b : J → Bool) : ℝ :=
  ∏ j∈U, boolSign (b j)

noncomputable def copyDifference {J : Type*} [Fintype J] [DecidableEq J] (U : Finset J)
    {X : J → Type*} (f : (∀j, X j) → ℝ) (x y : ∀j, X j) : ℝ :=
  (2:ℝ)^U.card*(𝔼 b : J → Bool, f (hybrid b x y)*boolChar U b)

end SquareDifference
end LiftAnalysis
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_FourierLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators
namespace LiftAnalysis
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

noncomputable def expPhase (t : ℝ) : ℂ := Real.fourierChar t

noncomputable def circleDistance (t : ℝ) : ℝ := |t - round t|

@[simp] lemma expPhase_zero : expPhase 0 = 1 := by simp [expPhase]
@[simp] lemma norm_expPhase (t : ℝ) : ‖expPhase t‖ = 1 := Circle.norm_coe _

variable {J : Type*} [Fintype J]

variable (p : J → ℕ) [∀ j, NeZero (p j)]

abbrev ResidueSpace := ∀ j, ZMod (p j)

noncomputable def prodChar (a z : ResidueSpace p) : ℂ :=
  ∏ j, ZMod.stdAddChar (a j*z j)

noncomputable def frequencyAngle (a : ResidueSpace p) : ℝ :=
  ∑ j, (a j).val/(p j : ℝ)

noncomputable def primeSupport (a : ResidueSpace p) : Finset J :=
  univ.filter fun j => a j ≠ 0

noncomputable def supportDenominator (a : ResidueSpace p) : ℕ :=
  ∏ j∈primeSupport p a, p j

@[simp] lemma prodChar_zero (z : ResidueSpace p) : prodChar p 0 z=1 := by
  simp [prodChar, AddChar.map_zero_eq_one]
@[simp] lemma prodChar_zero_right (a : ResidueSpace p) : prodChar p a 0=1 := by
  simp [prodChar, AddChar.map_zero_eq_one]

noncomputable def supportNumerator (a : ResidueSpace p) : ℕ := by
  classical
  exact ∑ j∈primeSupport p a, (a j).val * ∏ i∈(primeSupport p a).erase j, p i

noncomputable def residueGate (q : ℕ) (x : ZMod q) : ℝ :=
  (if x=0 then (q : ℝ) else 0)-1

noncomputable def exactGate [DecidableEq J] (U : Finset J) (z : ResidueSpace p) : ℝ :=
  ∏j∈U, residueGate (p j) (z j)

noncomputable def fourierPolynomial [DecidableEq J] (c : ResidueSpace p → ℂ) (z : ResidueSpace p) : ℂ :=
  ∑a, c a*prodChar p a z

noncomputable def gateCoefficient [DecidableEq J] (L : ℕ) (f : ℕ → ℂ)
    (B : Finset J) (z a : ResidueSpace p) : ℂ :=
  (L : ℂ)⁻¹*∑n∈range L, f n*expPhase (-(n : ℝ)*frequencyAngle p a)*
    (exactGate p B (z-fun j => (n : ZMod (p j))) : ℂ)

noncomputable def coordinateFreeze [DecidableEq J] (W : Finset J)
    (z x : ResidueSpace p) : ResidueSpace p := fun j => if j∈W then z j else x j

noncomputable def liftPiece [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U : Finset J) (z : ResidueSpace p) : ℝ :=
  (L : ℝ)⁻¹*∑n∈range L, f n*exactGate p U (z-fun j => (n : ZMod (p j)))

end SquareDifference

end LiftAnalysis
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ResidueLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators

namespace SquareDifference

open Finset

section FrozenAnalysis

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  {X : J → Type*} [instFintypeXj : ∀j,Fintype (X j)] [instNonemptyXj : ∀j,Nonempty (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]

noncomputable def freezeCoordinates (B : Finset J) (z x : ∀j,X j) : ∀j,X j :=
  fun j => if j∈B then z j else x j

end FrozenAnalysis

end SquareDifference

namespace LiftAnalysis

namespace SquareDifference

open Finset

section ActualLift

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

noncomputable def supportFamily (Q : ℕ) : Finset (Finset J) :=
  univ.filter (fun U => ∏j∈U,p j≤Q)

noncomputable def truncatedLift (L Q : ℕ) (f : ℕ → ℝ) (x : ResidueSpace p) : ℝ :=
  ∑U∈supportFamily p Q,liftPiece p L f U x

noncomputable def remainingFamily (B : Finset J) (H : ℕ) : Finset (Finset J) :=
  univ.filter (fun U => Disjoint U B ∧ ∏j∈U,p j≤H)

end ActualLift

end SquareDifference

end LiftAnalysis

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ScaleTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped BigOperators

namespace SquareDifference

open Finset

section GroupProjection

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,AddCommGroup (X j)] [instDecidableEqXj : ∀j,DecidableEq (X j)]

noncomputable def coordinateProjection (B : Finset J) (f : (∀j,X j) → ℝ) (x : ∀j,X j) : ℝ :=
  𝔼 z,f (freezeCoordinates B z x)

def maskedCoordinate (B : Finset J) (z : ∀j,X j) : ∀j,X j := fun j => if j∈B then z j else 0

end GroupProjection

end SquareDifference

namespace SquareDifference

open Finset

section FrozenFamily

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J]
  (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]

noncomputable def frozenFamily (B : Finset J) (z : ∀j,ZMod (p j))
    (s : Finset (Finset J)) (f : Finset J → (∀j,ZMod (p j)) → ℝ) (x : ∀j,ZMod (p j)) : ℝ :=
  ∑U∈s,f U (freezeCoordinates B z x)

end FrozenFamily

end SquareDifference

namespace SquareDifference

open Finset

noncomputable abbrev liftSupportFamily {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.supportFamily p

noncomputable abbrev actualLiftPiece {J : Type*} [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.liftPiece p

noncomputable abbrev actualTruncatedLift {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.truncatedLift p

noncomputable abbrev actualRemainingFamily {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) := LiftAnalysis.SquareDifference.remainingFamily p

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PrimeGauss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped ComplexConjugate BigOperators

namespace SquareDifference

noncomputable def primeSieveWeight (p : ℕ) (x : ZMod p) : ℝ :=
  ((p : ℝ)*(if x=0 then 1 else 0)-1)/(p-1)

noncomputable def zmodScaleHom (p k : ℕ) : ZMod p →+ ZMod (p*k) :=
  ZMod.lift p ⟨{ toFun := fun z : ℤ => (k : ZMod (p*k))*(z : ZMod (p*k))
                 map_zero' := by simp
                 map_add' := by intros; simp only [Int.cast_add, mul_add] }, by
    change (k : ZMod (p*k))*((p : ℤ) : ZMod (p*k))=0
    rw [Int.cast_natCast]
    rw [← Nat.cast_mul, mul_comm k p, ZMod.natCast_self]⟩

def HasFourierBound {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (w : R → ℂ) (C : ℝ) : Prop :=
  ∃ c : R → ℂ, (∀x, w x=∑a, c a*ψ (a*x)) ∧ (∑a, ‖c a‖)≤C

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_SievedFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

noncomputable def coordinateChar {I : Type*} [DecidableEq I] {R : I → Type*}
    [∀i, CommRing (R i)] (ψ : AddChar (∀i, R i) ℂ) (i : I) : AddChar (R i) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.single R i)

lemma addChar_finset_sum {I A : Type*} [AddCommMonoid A] (ψ : AddChar A ℂ)
    (S : Finset I) (f : I → A) : ψ (∑i∈S, f i)=∏i∈S, ψ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

lemma additive_character_product {I : Type*} [Fintype I] [DecidableEq I]
    {R : I → Type*} [∀i, CommRing (R i)] (ψ : AddChar (∀i, R i) ℂ) (x : ∀i, R i) :
    ψ x=∏i, coordinateChar ψ i (x i) := by
  have h : x=∑i, Pi.single i (x i) := by
    ext j
    simp only [Finset.sum_apply]
    rw [sum_eq_single j]
    · simp
    · intro i _ hij; exact Pi.single_eq_of_ne (Ne.symm hij) _
    · simp
  conv_lhs => rw [h]
  rw [addChar_finset_sum]
  rfl

noncomputable def residueDensity {m q : ℕ} (hmq : m∣q) (c : ZMod m) (x : ZMod q) : ℝ :=
  if ZMod.castHom hmq (ZMod m) x=c then m else 0

noncomputable def localSieveTerm {I : Type*} [DecidableEq I]
    (S : Finset I) (a b : I → ℂ) (T : Finset I) : ℂ :=
  (-1)^T.card*(∏i∈S\T, a i)*∏i∈T, b i

noncomputable def truncatedSieveMean {I : Type*} [DecidableEq I]
    (S : Finset I) (p : I → ℕ) (H : ℝ) (a b : I → ℂ) : ℂ :=
  ∑T∈S.powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then localSieveTerm S a b T else 0

noncomputable def unitQuadraticMean {R : Type*} [CommRing R] [Fintype R]
    [DecidableEq R] (ψ : AddChar R ℂ) : ℂ := 𝔼 x : Rˣ, ψ ((x : R)^2)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PrimaryKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

section RootSieve

variable {I : Type*} [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : ∀i, AddChar (ZMod (m i)) ℂ)

noncomputable def rootSieveA (i : I) : ℂ :=
  if i∈R then 𝔼 x : ZMod (m i), (residueDensity (hm i) (c i) x : ℂ)*ψ i (x^2)
  else 𝔼 x : ZMod (m i), ψ i (x^2)

noncomputable def rootSieveB (i : I) : ℂ :=
  if i∈R then 0 else 𝔼 x : ZMod (m i),
    (primeSieveWeight (p i) (ZMod.castHom (hm i) (ZMod (p i)) x) : ℂ)*ψ i (x^2)

end RootSieve

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CompleteWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

noncomputable def primaryModulus (q p : ℕ) : ℕ := p^(max 1 (q.factorization p))

lemma primaryModulus_pos {q p : ℕ} (hp : p.Prime) : 0<primaryModulus q p := pow_pos hp.pos _

lemma prime_dvd_primaryModulus (q p : ℕ) : p∣primaryModulus q p := by
  exact dvd_pow_self p (by have := le_max_left 1 (q.factorization p); omega)

instance primaryModulus_neZero (q p : ℕ) [Fact p.Prime] : NeZero (primaryModulus q p) :=
  ⟨(primaryModulus_pos (Fact.out : p.Prime)).ne'⟩

noncomputable def expPhase (t : ℝ) : ℂ := Real.fourierChar t

noncomputable def periodicMean (a : ℕ → ℂ) (T : ℕ) : ℂ := (T : ℂ)⁻¹*∑m∈range T, a m

noncomputable def rationalChar (b : ℚ) : AddChar (ZMod b.den) ℂ :=
  (@ZMod.stdAddChar b.den ⟨b.pos.ne'⟩).mulShift b.num

section CRTRootSieve

variable {I : Type*} [Fintype I] [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))

noncomputable def localRootWeight (i : I) (x : ZMod (m i)) : ℂ :=
  if i∈R then (residueDensity (hm i) (c i) x : ℂ) else 1

noncomputable def localSieveWeight (i : I) (x : ZMod (m i)) : ℂ :=
  if i∈R then 0 else (primeSieveWeight (p i) (ZMod.castHom (hm i) (ZMod (p i)) x) : ℂ)

end CRTRootSieve

lemma primaryModuli_pairwise {I : Type*} (p : I → ℕ) [∀i, Fact (p i).Prime]
    (hinj : Function.Injective p) (q : ℕ) :
    Pairwise (fun i j => (primaryModulus q (p i)).Coprime (primaryModulus q (p j))) := by
  intro i j hij
  apply Nat.Coprime.pow
  exact (Nat.coprime_primes (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mpr
    (fun h => hij (hinj h))

section PrimaryCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
  (q : ℕ) [NeZero q]
  (hq : q∣∏i, primaryModulus q (p i))

noncomputable def primaryCoordinateChar (ψ : AddChar (ZMod q) ℂ)
    (i : I) : AddChar (ZMod (primaryModulus q (p i))) ℂ :=
  coordinateChar ((ψ.compAddMonoidHom (ZMod.castHom hq (ZMod q)).toAddMonoidHom).compAddMonoidHom
    (ZMod.prodEquivPi (fun i => primaryModulus q (p i)) (primaryModuli_pairwise p hinj q)).symm.toAddMonoidHom) i

noncomputable def primaryActive : Finset I := univ.filter (fun i => p i∣q)

omit [DecidableEq I] [∀i, Fact (p i).Prime] [NeZero q] in
@[simp] lemma mem_primaryActive (i : I) : i∈primaryActive p q ↔ p i∣q := by
  simp only [primaryActive,mem_filter,mem_univ,true_and]

end PrimaryCoefficient

section KernelCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (hinj : Function.Injective p)
  (b : ℚ) (hb : b.den ∣ ∏ i, primaryModulus b.den (p i))
  (R : Finset I) (c : ∀ i, ZMod (p i))

noncomputable def primarySieveCoefficient (H : ℝ) : ℂ :=
  truncatedSieveMean univ p H
    (rootSieveA p (fun i => primaryModulus b.den (p i))
      (fun i => prime_dvd_primaryModulus b.den (p i)) R c
      (primaryCoordinateChar p hinj b.den hb (rationalChar b)))
    (rootSieveB p (fun i => primaryModulus b.den (p i))
      (fun i => prime_dvd_primaryModulus b.den (p i)) R
      (primaryCoordinateChar p hinj b.den hb (rationalChar b)))

noncomputable def primaryModelCoefficient (H : ℝ) : ℂ :=
  if ((∏ i ∈ primaryActive p b.den \ R, p i : ℕ) : ℝ) ≤ H ∧
       (∀ i ∈ primaryActive p b.den \ R, primaryModulus b.den (p i) = p i) then
    (∏ i ∈ primaryActive p b.den ∩ R,
      rootSieveA p (fun i => primaryModulus b.den (p i))
        (fun i => prime_dvd_primaryModulus b.den (p i)) R c
        (primaryCoordinateChar p hinj b.den hb (rationalChar b)) i) *
    ∏ i ∈ primaryActive p b.den \ R,
      unitQuadraticMean (primaryCoordinateChar p hinj b.den hb (rationalChar b) i)
  else 0

noncomputable def actualRootWeight (n : ℕ) : ℂ :=
  ∏ i ∈ R, if (n : ZMod (p i)) = c i then (p i : ℂ) else 0

noncomputable def actualSieveWeight (T : Finset I) (n : ℕ) : ℂ :=
  ∏ i ∈ T, if i ∈ R then 0 else (primeSieveWeight (p i) (n : ZMod (p i)) : ℂ)

noncomputable def actualDivisorWeight (H : ℝ) (n : ℕ) : ℂ :=
  actualRootWeight p R c n *
    ∑ T ∈ (univ : Finset I).powerset,
      if ((∏ i ∈ T, p i : ℕ) : ℝ) ≤ H then
        (-1)^T.card * actualSieveWeight p R T n else 0

noncomputable def rootSquareModulus : ℕ := ∏ i ∈ R, if p i = 2 then 8 else p i

end KernelCoefficient

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CircleDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

section ActualWeight

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime]
  (R : Finset I) (c : ∀i, ZMod (p i))

variable (q : ℕ) [NeZero q] (hpq : ∀i,p i∣q)

noncomputable def ringRootWeight (x : ZMod q) : ℂ :=
  ∏i∈R,(residueDensity (hpq i) (c i) x : ℂ)

noncomputable def ringSieveWeight (T : Finset I) (x : ZMod q) : ℂ :=
  ∏i∈T, if i∈R then 0 else (primeSieveWeight (p i) (ZMod.castHom (hpq i) (ZMod (p i)) x) : ℂ)

noncomputable def ringDivisorWeight (H : ℝ) (x : ZMod q) : ℂ :=
  ringRootWeight p R c q hpq x * ∑T∈(univ:Finset I).powerset,
    if ((∏i∈T,p i : ℕ):ℝ)≤H then (-1)^T.card * ringSieveWeight p R q hpq T x else 0

end ActualWeight

section CompleteWeight

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))

noncomputable def actualCompleteWeight (n : ℕ) : ℂ :=
  actualRootWeight p R c n * ∏i, (1 - if i∈R then 0 else
    (primeSieveWeight (p i) (n : ZMod (p i)) : ℂ))

end CompleteWeight

noncomputable def smallQuadraticModulus (p : ℕ) : ℕ := if p=2 then 8 else p

lemma smallQuadraticModulus_pos {p : ℕ} (hp : p.Prime) : 0<smallQuadraticModulus p := by
  unfold smallQuadraticModulus
  split_ifs
  · norm_num
  · exact hp.pos

instance instNeZeroNatSmallQuadraticModulusOfFactPrime {p : ℕ} [Fact p.Prime] : NeZero (smallQuadraticModulus p) :=
  ⟨(smallQuadraticModulus_pos (Fact.out : p.Prime)).ne'⟩

lemma prime_dvd_smallQuadraticModulus (p : ℕ) : p∣smallQuadraticModulus p := by
  unfold smallQuadraticModulus
  split_ifs with h
  · subst p; norm_num
  · exact dvd_rfl

lemma smallQuadraticModuli_pairwise {I : Type*} (p : I → ℕ)
    (hp : ∀i,(p i).Prime) (hinj : Function.Injective p) :
    Pairwise (fun i j => (smallQuadraticModulus (p i)).Coprime (smallQuadraticModulus (p j))) := by
  intro i j hij
  have hc : (p i).Coprime (p j) := (Nat.coprime_primes (hp i) (hp j)).mpr (hinj.ne hij)
  unfold smallQuadraticModulus
  split_ifs with hi hj hj
  · exact False.elim (hij (hinj (hi.trans hj.symm)))
  · simpa only [hi,show 2^3=8 by norm_num] using hc.pow_left 3
  · simpa only [hj,show 2^3=8 by norm_num] using hc.pow_right 3
  · exact hc

noncomputable def smallRootSquare (p : ℕ) (c : ZMod p) : ZMod (smallQuadraticModulus p) :=
  if p=2 then 1 else (c.val : ZMod (smallQuadraticModulus p))^2

noncomputable def circleDistance (t : ℝ) : ℝ := |t - round t|

@[simp] lemma expPhase_zero : expPhase 0 = 1 := by simp [expPhase]
@[simp] lemma norm_expPhase (t : ℝ) : ‖expPhase t‖ = 1 := Circle.norm_coe _

noncomputable def phaseBound (M t : ℝ) : ℝ :=
  if circleDistance t = 0 then M else min M (circleDistance t)⁻¹

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PhaseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

noncomputable def distanceBucket (q : ℕ) (t : ℝ) : ℕ :=
  ⌊2*(q : ℝ)*circleDistance t⌋₊

noncomputable def bucketWeight (q : ℕ) (M : ℝ) (k : ℕ) : ℝ :=
  if k=0 then M else 2*q/(k : ℝ)

noncomputable def squareWeight (N : ℕ) (y : ℝ) (m : ℕ) : ℂ :=
  (2*((m : ℝ)+1)/(N : ℝ)) • expPhase (y*(m+1)^2)

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_RationalApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

noncomputable def normalizedLinearSum (N : ℕ) (y : ℝ) : ℂ :=
  (N : ℝ)⁻¹ • ∑ n ∈ range N, expPhase (y*(n+1))

noncomputable def modelCenterCoefficient {I : Type*} [Fintype I]
    (c : I → ℚ) (z : I → ℂ) (b : ℚ) : ℂ := by
  classical
  exact ∑i, if ∃k : ℤ, b-c i=(k : ℚ) then z i else 0

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_FiniteKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

noncomputable def finiteSquareKernel {K : Type*} [Fintype K]
    (ε : K → ℂ) (v : K → ℕ → ℂ) (M N : ℕ) (α : ℝ) : ℂ :=
  ∑k, ε k*∑m∈range M, squareWeight N α m*v k (m+1)

noncomputable def finiteRationalCoefficient {K : Type*} [Fintype K]
    (ε : K → ℂ) (v : K → ℕ → ℂ) (t : K → ℕ) (b : ℚ) : ℂ :=
  ∑k, ε k*periodicMean (fun m => v k (m+1)*expPhase ((b : ℝ)*(m+1)^2)) (b.den*t k)

noncomputable def boundedRationals (L : ℕ) : Finset ℚ :=
  ((univ : Finset (Fin L × Fin L)).image
    (fun v => ((v.1.val : ℚ)/(v.2.val+1)))).filter (fun b => 0≤b ∧ b<1 ∧ b.den≤L)

attribute [local instance] Classical.propDecidable

section ActualKernelCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))

noncomputable def completeRationalCoefficient (b : ℚ) : ℂ :=
  periodicMean (fun n => actualCompleteWeight p R c (n+1)*expPhase ((b:ℝ)*(n+1)^2))
    (b.den*∏i,p i)

noncomputable def kernelModelCoefficient (H : ℝ) (b : ℚ) : ℂ :=
  if ((∏i∈primaryActive p b.den\R,p i : ℕ):ℝ)≤H then completeRationalCoefficient p R c b else 0

end ActualKernelCoefficient

section ActualKernelTerms

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (R : Finset I) (c : ∀i, ZMod (p i))

noncomputable def boundedSieveSets (H : ℝ) : Finset (Finset I) :=
  (univ : Finset I).powerset.filter (fun T => ((∏i∈T,p i : ℕ):ℝ)≤H)

noncomputable def sieveTermSign (T : Finset I) : ℂ := (-1)^T.card

noncomputable def sieveTermWeight (T : Finset I) (n : ℕ) : ℂ :=
  actualRootWeight p R c n*actualSieveWeight p R T n

noncomputable def sieveTermPeriod (T : Finset I) : ℕ := (∏i∈R,p i)*(∏i∈T,p i)

noncomputable def actualSquareTransform (H : ℝ) (M N : ℕ) (α : ℝ) : ℂ :=
  ∑m∈range M,squareWeight N α m*actualDivisorWeight p R c H (m+1)

noncomputable def actualModelTransform (H : ℝ) (L N : ℕ) (α : ℝ) : ℂ :=
  ∑b : boundedRationals L,kernelModelCoefficient p R c H b.val*
    normalizedLinearSum N (α-b.val)

end ActualKernelTerms

end SquareDifference

namespace SquareDifference

open Finset

noncomputable def rationalGridPoint (q : ℕ) (a : ZMod q) : ℚ := (a.val : ℚ)/q

lemma rationalGridPoint_den_dvd (q : ℕ) (a : ZMod q) : (rationalGridPoint q a).den∣q := by
  have h := Rat.den_dvd (a.val : ℤ) (q : ℤ)
  rw [Rat.divInt_eq_div] at h
  simp only [Int.cast_natCast] at h
  exact Int.natCast_dvd_natCast.mp h

end SquareDifference
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_UniformRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference
open Finset

noncomputable def rationalGrid (q : ℕ) [NeZero q] : Finset ℚ :=
  univ.image (rationalGridPoint q)

end SquareDifference

namespace SquareDifference

open Finset

section GridModel

variable {I : Type*} [Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)

include hinj

variable (R : Finset I) (c : ∀i,ZMod (p i))

omit hinj in
instance smallProductNeZero : NeZero (∏i,smallQuadraticModulus (p i)) :=
  ⟨(prod_pos (fun i _ => smallQuadraticModulus_pos (Fact.out : (p i).Prime))).ne'⟩

end GridModel

end SquareDifference

namespace SquareDifference

open Finset

section SmallCoordinates

variable {I : Type*} [instFintypeI : Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)

noncomputable def smallTupleEquiv :
    ZMod (∏i,smallQuadraticModulus (p i)) ≃+* ∀i,ZMod (smallQuadraticModulus (p i)) :=
  ZMod.prodEquivPi _ (smallQuadraticModuli_pairwise p (fun _ => Fact.out) hinj)

noncomputable def smallCoordinateChar (b : ℚ)
    (hb : b.den∣∏i,smallQuadraticModulus (p i)) (i : I) :
    AddChar (ZMod (smallQuadraticModulus (p i))) ℂ :=
  coordinateChar (((rationalChar b).compAddMonoidHom
    (ZMod.castHom hb (ZMod b.den)).toAddMonoidHom).compAddMonoidHom
      (smallTupleEquiv p hinj).symm.toAddMonoidHom) i

end SmallCoordinates

end SquareDifference

open Filter

open scoped Topology

namespace SquareDifference

open Finset

section UniformFinal

variable {I : Type*} [instFintypeI : Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [instFactNatPrimepi : ∀i, Fact (p i).Prime]
  (R : Finset I) (c : ∀i,ZMod (p i))

noncomputable def kernelAbsoluteConstant : ℝ := 2^64+3*(4+8*Real.pi)+156+16

end UniformFinal

end SquareDifference

open Finset Complex

open scoped BigOperators ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_DualCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate

namespace SquareDifference

section CyclicFourier

variable {q : ℕ} [NeZero q]

noncomputable def cyclicChar (a x : ZMod q) : ℂ := ZMod.stdAddChar (a*x)

noncomputable def cyclicPolynomial (c : ZMod q → ℂ) (x : ZMod q) : ℂ :=
  ∑a, c a*cyclicChar a x

noncomputable def cyclicFourier (f : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  𝔼 x, f x*conj (cyclicChar a x)

end CyclicFourier

end SquareDifference

namespace SquareDifference

open Finset

section SequenceKernel

variable {q : ℕ} [instNeZeroq : NeZero q]

noncomputable def cyclicPush {T : Type*} (s : Finset T) (shift : T → ZMod q)
    (w : T → ℂ) (z : ZMod q) : ℂ := ∑t∈s, if shift t=z then w t else 0

end SequenceKernel

end SquareDifference

namespace SquareDifference

open Finset

section OrderedModel

variable {q : ℕ} [NeZero q]

noncomputable def intervalFourier (N : ℕ) (F : ZMod q → ℂ) (α : ℝ) : ℂ :=
  (N:ℂ)⁻¹*∑x, F x*expPhase (-(x.val:ℝ)*α)

noncomputable def intervalModelWeight {B : Type*} [Fintype B]
    (N : ℕ) (β : B → ℝ) (c : B → ℂ) (n : ℕ) : ℂ :=
  (N:ℂ)⁻¹*∑b, c b*expPhase (-β b*((n:ℝ)+1))

end OrderedModel

end SquareDifference

namespace SquareDifference

open Finset

section DualCoordinates

variable {q : ℕ} [NeZero q]

noncomputable def standardCharEquiv : ZMod q ≃ AddChar (ZMod q) ℂ :=
  Equiv.ofBijective (fun a => (ZMod.stdAddChar (N:=q)).mulShift a) (by
    rw [Fintype.bijective_iff_injective_and_card,AddChar.card_eq]
    refine ⟨?_,rfl⟩
    intro a b h
    have h1 := congrArg (fun ψ : AddChar (ZMod q) ℂ => ψ 1) h
    simp only [AddChar.mulShift_apply,mul_one] at h1
    exact ZMod.injective_stdAddChar h1)

lemma standardCharEquiv_apply (a x : ZMod q) :
    standardCharEquiv a x=ZMod.stdAddChar (a*x) := rfl

lemma standardCharEquiv_symm_apply (ψ : AddChar (ZMod q) ℂ) (x : ZMod q) :
    ZMod.stdAddChar ((standardCharEquiv (q:=q)).symm ψ*x)=ψ x := by
  rw [← standardCharEquiv_apply,(standardCharEquiv (q:=q)).apply_symm_apply]

end DualCoordinates

section ProductDual

variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)] (hcop : Pairwise fun i j => (m i).Coprime (m j))

local instance productModulusNeZero : NeZero (∏i,m i) :=
  ⟨prod_ne_zero_iff.mpr (fun _ _ => NeZero.ne _)⟩

noncomputable def dualCRTCoordinates (a : ZMod (∏i,m i)) (i : I) : ZMod (m i) :=
  standardCharEquiv.symm
    (coordinateChar ((standardCharEquiv a).compAddMonoidHom
      (ZMod.prodEquivPi m hcop).symm.toAddMonoidHom) i)

lemma dualCRTCoordinates_char (a : ZMod (∏i,m i)) (i : I) (x : ZMod (m i)) :
    ZMod.stdAddChar (dualCRTCoordinates m hcop a i*x)=
      coordinateChar ((standardCharEquiv a).compAddMonoidHom
        (ZMod.prodEquivPi m hcop).symm.toAddMonoidHom) i x := by
  exact standardCharEquiv_symm_apply _ x

lemma dualCRTCoordinates_product (a : ZMod (∏i,m i)) (x : ∀i,ZMod (m i)) :
    ZMod.stdAddChar (a*(ZMod.prodEquivPi m hcop).symm x)=
      ∏i,ZMod.stdAddChar (dualCRTCoordinates m hcop a i*x i) := by
  simp_rw [dualCRTCoordinates_char]
  exact additive_character_product
    ((standardCharEquiv a).compAddMonoidHom (ZMod.prodEquivPi m hcop).symm.toAddMonoidHom) x

lemma dualCRTCoordinates_injective : Function.Injective (dualCRTCoordinates m hcop) := by
  intro a b hab
  apply standardCharEquiv.injective
  ext x
  obtain ⟨y,rfl⟩ := (ZMod.prodEquivPi m hcop).symm.surjective x
  change ZMod.stdAddChar (a*(ZMod.prodEquivPi m hcop).symm y)=
    ZMod.stdAddChar (b*(ZMod.prodEquivPi m hcop).symm y)
  rw [dualCRTCoordinates_product,dualCRTCoordinates_product,hab]

noncomputable def dualCRTEquiv : ZMod (∏i,m i) ≃ ∀i,ZMod (m i) :=
  Equiv.ofBijective (dualCRTCoordinates m hcop) (by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨dualCRTCoordinates_injective m hcop,by simp [Fintype.card_pi]⟩)

end ProductDual

end SquareDifference

namespace SquareDifference

open Finset

section SmallDual

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i,Fact (p i).Prime] (hinj : Function.Injective p)

local instance smallFactorNeZero (i : I) : NeZero (smallQuadraticModulus (p i)) :=
  ⟨(smallQuadraticModulus_pos (Fact.out : (p i).Prime)).ne'⟩

noncomputable def smallDualEquiv :
    ZMod (∏i,smallQuadraticModulus (p i)) ≃ ∀i,ZMod (smallQuadraticModulus (p i)) :=
  dualCRTEquiv _ (smallQuadraticModuli_pairwise p (fun _ => Fact.out) hinj)

end SmallDual

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_RationalLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

noncomputable def expPhase (t : ℝ) : ℂ := Real.fourierChar t

@[simp] lemma expPhase_zero : expPhase 0 = 1 := by simp [expPhase]
@[simp] lemma norm_expPhase (t : ℝ) : ‖expPhase t‖ = 1 := Circle.norm_coe _

variable {J : Type*} [Fintype J]

variable (p : J → ℕ) [∀ j, NeZero (p j)]

abbrev ResidueSpace := ∀ j, ZMod (p j)

noncomputable def prodChar (a z : ResidueSpace p) : ℂ :=
  ∏ j, ZMod.stdAddChar (a j*z j)

noncomputable def frequencyAngle (a : ResidueSpace p) : ℝ :=
  ∑ j, (a j).val/(p j : ℝ)

noncomputable def primeSupport (a : ResidueSpace p) : Finset J :=
  univ.filter fun j => a j ≠ 0

noncomputable def supportDenominator (a : ResidueSpace p) : ℕ :=
  ∏ j∈primeSupport p a, p j

@[simp] lemma prodChar_zero (z : ResidueSpace p) : prodChar p 0 z=1 := by
  simp [prodChar, AddChar.map_zero_eq_one]
@[simp] lemma prodChar_zero_right (a : ResidueSpace p) : prodChar p a 0=1 := by
  simp [prodChar, AddChar.map_zero_eq_one]

noncomputable def supportNumerator (a : ResidueSpace p) : ℕ := by
  classical
  exact ∑ j∈primeSupport p a, (a j).val * ∏ i∈(primeSupport p a).erase j, p i

noncomputable def residueGate (q : ℕ) (x : ZMod q) : ℝ :=
  (if x=0 then (q : ℝ) else 0)-1

noncomputable def exactGate [DecidableEq J] (U : Finset J) (z : ResidueSpace p) : ℝ :=
  ∏j∈U, residueGate (p j) (z j)

noncomputable def fourierPolynomial [DecidableEq J] (c : ResidueSpace p → ℂ) (z : ResidueSpace p) : ℂ :=
  ∑a, c a*prodChar p a z

noncomputable def gateCoefficient [DecidableEq J] (L : ℕ) (f : ℕ → ℂ)
    (B : Finset J) (z a : ResidueSpace p) : ℂ :=
  (L : ℂ)⁻¹*∑n∈range L, f n*expPhase (-(n : ℝ)*frequencyAngle p a)*
    (exactGate p B (z-fun j => (n : ZMod (p j))) : ℂ)

noncomputable def coordinateFreeze [DecidableEq J] (W : Finset J)
    (z x : ResidueSpace p) : ResidueSpace p := fun j => if j∈W then z j else x j

noncomputable def liftPiece [DecidableEq J] (L : ℕ) (f : ℕ → ℝ)
    (U : Finset J) (z : ResidueSpace p) : ℝ :=
  (L : ℝ)⁻¹*∑n∈range L, f n*exactGate p U (z-fun j => (n : ZMod (p j)))

end SquareDifference

end LiftTheory
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ResidueFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SquareDifference

open Finset

section PairFourier

variable {J : Type*} [Fintype J] [DecidableEq J]
  (p : J → ℕ) [∀j,NeZero (p j)]

noncomputable def residueFourier (F : ResidueSpace p → ℂ) (a : ResidueSpace p) : ℂ :=
  𝔼 x,F x*conj (prodChar p a x)

noncomputable def squareMultiplier (a : ResidueSpace p) : ℂ :=
  𝔼 u : ∀j,(ZMod (p j))ˣ,prodChar p a (fun j => (u j : ZMod (p j))^2)

noncomputable def squarePairForm (F G : ResidueSpace p → ℂ) : ℂ :=
  𝔼 u : ∀j,(ZMod (p j))ˣ,𝔼 x,F x*G (x+(fun j => (u j : ZMod (p j))^2))

end PairFourier

end SquareDifference

namespace SquareDifference

noncomputable def primeSieveWeight (p : ℕ) (x : ZMod p) : ℝ :=
  ((p : ℝ)*(if x=0 then 1 else 0)-1)/(p-1)

noncomputable def zmodScaleHom (p k : ℕ) : ZMod p →+ ZMod (p*k) :=
  ZMod.lift p ⟨{ toFun := fun z : ℤ => (k : ZMod (p*k))*(z : ZMod (p*k))
                 map_zero' := by simp
                 map_add' := by intros; simp only [Int.cast_add, mul_add] }, by
    change (k : ZMod (p*k))*((p : ℤ) : ZMod (p*k))=0
    rw [Int.cast_natCast]
    rw [← Nat.cast_mul, mul_comm k p, ZMod.natCast_self]⟩

end SquareDifference
end LiftTheory
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ConductorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

def HasFourierBound {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (w : R → ℂ) (C : ℝ) : Prop :=
  ∃ c : R → ℂ, (∀x, w x=∑a, c a*ψ (a*x)) ∧ (∑a, ‖c a‖)≤C

end SquareDifference
end LiftTheory
end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_RootModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
open Filter
open scoped Topology
open Finset Complex
open scoped BigOperators ComplexConjugate
namespace LiftTheory
open Finset
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SquareDifference

noncomputable def unitQuadraticMean {R : Type*} [CommRing R] [Fintype R]
    [DecidableEq R] (ψ : AddChar R ℂ) : ℂ := 𝔼 x : Rˣ, ψ ((x : R)^2)

end SquareDifference

namespace SquareDifference

open Finset

section RootModel

variable {I : Type*} [instFintypeI : Fintype I] [instDecidableEqI : DecidableEq I]
  (m : I → ℕ) [∀i,NeZero (m i)] (R : Finset I)

abbrev OutsideModulus : {i : I // i∉R} → ℕ := fun i => m i.val

noncomputable def rootCharacter (a s : ResidueSpace m) : ℂ :=
  ∏i∈R,ZMod.stdAddChar (a i*s i)

def outsideCoordinate (a : ResidueSpace m) : ResidueSpace (OutsideModulus m R) := fun i => a i.val

noncomputable def sequenceResidueFourier {Ω : Type*} [Fintype Ω]
    (L : ℕ) (F : Ω → ℂ) (n : Ω → ℕ) (a : ResidueSpace m) : ℂ :=
  (L : ℂ)⁻¹*∑z,F z*conj (prodChar m a (fun i => (n z : ZMod (m i))))

end RootModel

end SquareDifference

end LiftTheory

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PairBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

namespace PairBridge

open LiftTheory.SquareDifference

section Fourier

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ)
  [instNeZeropj : ∀j,NeZero (p j)]

noncomputable def sequenceCoeff (L : ℕ) (f : ℕ → ℝ) (a : ResidueSpace p) : ℂ :=
  (L : ℂ)⁻¹*∑n∈range L,(f n:ℂ)*conj (prodChar p a (fun j => (n:ZMod (p j))))

noncomputable def gatedSequence (B : Finset J) (z : ResidueSpace p) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∏j∈B,p j:ℝ)*(if ∀j∈B,(n:ZMod (p j))=z j then f n else 0)

end Fourier

end PairBridge

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_Endpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

def NatSquareFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ m : ℕ, 1 ≤ m → b ≠ a + m^2

noncomputable def natIndicator (A : Finset ℕ) (n : ℕ) : ℝ := if n∈A then 1 else 0

noncomputable def squareChild (A : Finset ℕ) (c D L : ℕ) : Finset ℕ :=
  (range L).filter (fun t => c+D^2*t∈A)

section Functional

variable {J : Type} [Fintype J] [DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

noncomputable def setFunctional (N Q : ℕ) (A : Finset ℕ) : ℝ :=
  diagonalIntegral (productTupleLaw p) (actualTruncatedLift p N Q (natIndicator A))

end Functional

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CRTTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

noncomputable def smallResidueInput (M : ℕ) (A : Finset ℕ) (s : ZMod M) (n : ℕ) : ℝ :=
  (M:ℝ)*(if (n:ZMod M)=s then natIndicator A n else 0)

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_UniformTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

def LiftSizeConditions (L Q : ℕ) : Prop :=
  0<L ∧ 0<Q ∧ 2*(Q:ℝ)≤L ∧ (Q:ℝ)^5≤L

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

noncomputable def intervalInput (a L : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n∈Ico a (a+L) then f n else 0

section Interval

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

noncomputable def intervalPiece (a L : ℕ) (f : ℕ → ℝ) (U : Finset J) (x : ResidueSpace p) : ℝ :=
  (L:ℝ)⁻¹*∑t∈range L,f (a+t)*exactGate p U (x-fun j => ((a+t:ℕ):ZMod (p j)))

noncomputable def intervalLift (a L Q : ℕ) (f : ℕ → ℝ) (x : ResidueSpace p) : ℝ :=
  ∑U∈liftSupportFamily p Q,intervalPiece p a L f U x

end Interval

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_OutsideFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference.PairBridge

open LiftTheory.SquareDifference

section Outside

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)] (B : Finset J)

def outsideExtend (a : ResidueSpace (OutsideModulus p B)) : ResidueSpace p :=
  fun j => if hj : j∈B then 0 else a ⟨j,hj⟩

noncomputable def assembleOutside (z : ResidueSpace p) (x : ResidueSpace (OutsideModulus p B)) : ResidueSpace p :=
  fun j => if hj : j∈B then z j else x ⟨j,hj⟩

end Outside

end SquareDifference.PairBridge

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TensorLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open Finset

section TensorExpansion

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (L E : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)

noncomputable def mixedTensorLaw (B : Finset J) : ((V → ∀j,X j) → ℝ) →ₗ[ℝ] ℝ :=
  tensorLaw (fun j => if j∈B then E j else L j)

end TensorExpansion

end SquareDifference

namespace SquareDifference

open Finset

section TensorFreeze

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀j,Fintype (X j)] [∀j,DecidableEq (X j)]
  (M L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ)

noncomputable def frozenTensorLaw (B : Finset J) : ((V → ∀j,X j) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := tensorLaw M (fun z => tensorLaw L (fun x => F (fun v j => if j∈B then z v j else x v j)))
  map_add' F G := by
    simp only [Pi.add_apply]
    simp only [←Pi.add_def,map_add]
  map_smul' c F := by
    simp only [Pi.smul_apply,←Pi.smul_def,map_smul,RingHom.id_apply]

end TensorFreeze

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TensorPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

section TensorPair

variable {J V : Type*} [Fintype J] [instDecidableEqJ : DecidableEq J] [Fintype V] [DecidableEq V]
  {X Ω : J → Type*} [instFintypeXj : ∀j,Fintype (X j)] [∀j,DecidableEq (X j)] [∀j,Fintype (Ω j)]
  (L : ∀j,((V → X j) → ℝ) →ₗ[ℝ] ℝ) (u v : V)
  (a b : ∀j,Ω j → X j)

noncomputable def pairPush : (((∀j,X j) × (∀j,X j)) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := tensorLaw L (fun z => F (z u,z v))
  map_add' F G := by simp only [Pi.add_apply,←Pi.add_def,map_add]
  map_smul' c F := by simp only [Pi.smul_apply,←Pi.smul_def,map_smul,RingHom.id_apply]

noncomputable def pairSample : (((∀j,X j) × (∀j,X j)) → ℝ) →ₗ[ℝ] ℝ where
  toFun F := 𝔼 w : ∀j,Ω j,F (fun j => a j (w j),fun j => b j (w j))
  map_add' F G := by simp only [Pi.add_apply,expect_add_distrib]
  map_smul' c F := by simp only [Pi.smul_apply,smul_eq_mul,mul_expect,RingHom.id_apply]

end TensorPair

section PiProduct

variable {J : Type*} [Fintype J] [DecidableEq J] {X Y : J → Type*}
  [∀j,Fintype (X j)] [∀j,Fintype (Y j)]

def piProductEquiv : (∀j,X j × Y j) ≃ (∀j,X j) × (∀j,Y j) where
  toFun z := (fun j => (z j).1,fun j => (z j).2)
  invFun z j := (z.1 j,z.2 j)
  left_inv _ := rfl
  right_inv _ := rfl

end PiProduct

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_GateExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

def OtherVertices {V : Type*} (u v : V) := {w : V // w≠u ∧ w≠v}

instance instFintypeOtherVerticesOfDecidableEq {V : Type*} [Fintype V] [DecidableEq V] (u v : V) : Fintype (OtherVertices u v) := inferInstanceAs (Fintype {w : V // w≠u ∧ w≠v})

instance instDecidableEqOtherVertices {V : Type*} [DecidableEq V] (u v : V) : DecidableEq (OtherVertices u v) := inferInstanceAs (DecidableEq {w : V // w≠u ∧ w≠v})

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_IntervalTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section Truncate

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instFactNatPrimepj : ∀j,Fact (p j).Prime]

noncomputable def retainedFamily (Q T : ℕ) (keep : Finset TupleVertex) (v : TupleVertex) : Finset (Finset J) :=
  if v∈keep then liftSupportFamily p Q else (liftSupportFamily p Q).filter (fun U => ∏j∈U,p j≤T)

noncomputable def retainedIntervalLift (a : TupleVertex → ℕ) (L Q T : ℕ) (keep : Finset TupleVertex)
    (f : TupleVertex → ℕ → ℝ) (v : TupleVertex) (x : ResidueSpace p) : ℝ :=
  ∑U∈retainedFamily p Q T keep v,intervalPiece p (a v) L (f v) U x

end Truncate

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ResidueReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

section Reindex

variable {J K : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] [instFintypeK : Fintype K] [instDecidableEqK : DecidableEq K]
  (p : J → ℕ) (m : K → ℕ) [instNeZeropj : ∀j,NeZero (p j)] [∀k,NeZero (m k)]
  (e : K ≃ J) (hm : m=fun k => p (e k))

noncomputable def residueReindex : ResidueSpace p ≃ ResidueSpace m := by
  subst m
  exact (Equiv.piCongrLeft (fun j => ZMod (p j)) e).symm

end Reindex

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PrimeExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section Indexed

variable {S J : Type*} [instFintypeS : Fintype S] [instDecidableEqS : DecidableEq S] [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ)

abbrev extendedPrime : S ⊕ J → ℕ := Sum.elim ps p

noncomputable def extendedRoots (B : Finset J) : Finset (S ⊕ J) := univ.disjSum B

@[simp] lemma inl_mem_extendedRoots {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J] (B : Finset J) (s : S) : Sum.inl s∈extendedRoots (S:=S) B := by simp [extendedRoots]
@[simp] lemma inr_mem_extendedRoots {S : Type*}
    {J : Type*}
    [Fintype S]
    [DecidableEq S]
    [Fintype J]
    [DecidableEq J] (B : Finset J) (j : J) : Sum.inr j∈extendedRoots (S:=S) B ↔ j∈B := by simp [extendedRoots]
noncomputable def outsideSumEquiv (B : Finset J) :
    {i : S ⊕ J // i∉extendedRoots (S:=S) B} ≃ {j : J // j∉B} where
  toFun i := match i with
    | ⟨Sum.inl s,hi⟩ => False.elim (hi (inl_mem_extendedRoots B s))
    | ⟨Sum.inr j,hi⟩ => ⟨j,fun hj => hi ((inr_mem_extendedRoots B j).mpr hj)⟩
  invFun j := ⟨Sum.inr j.val,by simpa using j.property⟩
  left_inv i := by
    rcases i with ⟨s|j,hi⟩
    · exact False.elim (hi (inl_mem_extendedRoots B s))
    · rfl
  right_inv _ := rfl

instance extendedPrime_prime [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime] :
    ∀i,Fact (extendedPrime ps p i).Prime := fun i => by cases i <;> dsimp [extendedPrime] <;> infer_instance

end Indexed

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_CyclicIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

section Selected

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

noncomputable def selectedIndicator (M a L : ℕ) (A : Finset ℕ) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (n : ℕ) : ℝ :=
  if n∈A ∧ n∈Ico a (a+L) ∧ (n:ZMod M)=s ∧ ∀j∈B,(n:ZMod (p j))=z j then 1 else 0

end Selected

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_SmallRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

noncomputable def smallStrict (p : ℕ) (x : ZMod (smallQuadraticModulus p)) : Prop :=
  if p=2 then x=1 else x≠0 ∧ IsSquare x

section Small

variable {S : Type*} [Fintype S] [instDecidableEqS : DecidableEq S] (ps : S → ℕ)

noncomputable def smallModulus : ℕ := ∏s,smallQuadraticModulus (ps s)

lemma smallModulus_dvd {S : Type*}
    [Fintype S]
    [DecidableEq S]
    (ps : S → ℕ) (s : S) : smallQuadraticModulus (ps s)∣smallModulus ps := dvd_prod_of_mem _ (mem_univ s)

noncomputable def smallProjection (s : S) : ZMod (smallModulus ps) →+* ZMod (smallQuadraticModulus (ps s)) :=
  ZMod.castHom (smallModulus_dvd ps s) _

@[simp] lemma smallProjection_nat (s : S) (n : ℕ) : smallProjection ps s (n:ZMod (smallModulus ps))=(n:ZMod (smallQuadraticModulus (ps s))) := map_natCast _ _

noncomputable def smallStrictPair (s t : ZMod (smallModulus ps)) : Prop :=
  ∀i,smallStrict (ps i) (smallProjection ps i (t-s))

end Small

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_SelectedRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

section Roots

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (ps : S → ℕ) (p : J → ℕ) [instFactNatPrimepsi : ∀i,Fact (ps i).Prime] [∀j,Fact (p j).Prime]

noncomputable def selectedRootLabels (s : ZMod (smallModulus ps)) (z : ResidueSpace p) :
    ∀i,ZMod (smallQuadraticModulus (extendedPrime ps p i)) := fun i => match i with
  | Sum.inl j => smallProjection ps j s
  | Sum.inr j => ((z j).val:ZMod (smallQuadraticModulus (p j)))

end Roots

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PowerParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

noncomputable def sourceBeta : ℝ := 1/100000

noncomputable def sourceGamma : ℝ := 1/64

noncomputable def sourceTau (d : ℕ) : ℝ := sourceBeta*sourceGamma/(1000*((d:ℝ)+1))

noncomputable def sourceSigma (d : ℕ) : ℝ := sourceGamma*sourceTau d/4

noncomputable def sourceLoss (d : ℕ) : ℝ := sourceGamma*sourceTau d/(100*((d:ℝ)+1))

noncomputable def powerCutoff (N : ℕ) (a : ℝ) : ℕ := ⌊(N:ℝ)^a⌋₊

noncomputable def childLength (N D : ℕ) : ℕ := ⌈(N:ℝ)/(D:ℝ)^2⌉₊

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_TransferRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

noncomputable def transferFactor (d M N : ℕ) : ℝ :=
  (1+(M:ℝ)^2*(N:ℝ)^(2*sourceTau d-1))^d

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_BlockParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

noncomputable def blockLength (N K : ℕ) : ℕ := ⌈(N:ℝ)/K⌉₊

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_OrderedBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

noncomputable def orderedLowError (d M K H : ℕ) (R : ℝ) : ℝ :=
  (M:ℝ)^d*(K:ℝ)^(3*d)*(H:ℝ)^(-(1:ℝ)/3)*((K:ℝ)^2*M*kernelAbsoluteConstant+R^2)

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_OrderedRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

noncomputable def orderedError (d M N K H : ℕ) (C : ℝ) : ℝ :=
  (K:ℝ)⁻¹*(2*(C*(N:ℝ)^(sourceLoss d))^(2*d))+
    (d:ℝ)*(K:ℝ)^(-sourceGamma)*(C*(N:ℝ)^(sourceLoss d))^d+
    orderedLowError d M K H (C*(N:ℝ)^(sourceLoss d))

noncomputable def orderedErrorConstant (d M : ℕ) (C : ℝ) : ℝ :=
  2*C^(2*d)+(d:ℝ)*C^d+(M:ℝ)^(d+1)*kernelAbsoluteConstant+(M:ℝ)^d*C^2

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_ExceptionalBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

section Mixed

variable {J : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [∀j,Fact (p j).Prime]

noncomputable def exceptionalProduct (B : Finset J) : ℝ := ∏j∈B,tupleEta (p j)

noncomputable def actualMixedLaw (B : Finset J) : ((TupleVertex → ∀j,ZMod (p j)) → ℝ) →ₗ[ℝ] ℝ :=
  mixedTensorLaw (fun j => tupleLaw (p:=p j)) (fun j => tupleExceptionalLaw (p:=p j)) B

end Mixed

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_SmallGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

section Small

variable {S : Type*} [Fintype S] [instDecidableEqS : DecidableEq S] (ps : S → ℕ) [∀s,Fact (ps s).Prime]

lemma smallModulus_pos {S : Type*}
    [Fintype S]
    [DecidableEq S]
    (ps : S → ℕ)
    [∀ (s : S), Fact (Nat.Prime (ps s))] : 0<smallModulus ps := prod_pos (fun s _ => smallQuadraticModulus_pos (Fact.out : (ps s).Prime))

noncomputable def smallResidueEquiv (hinj : Function.Injective ps) :
    ZMod (smallModulus ps) ≃+* (∀s,ZMod (smallQuadraticModulus (ps s))) :=
  ZMod.prodEquivPi _ (smallQuadraticModuli_pairwise ps (fun _ => Fact.out) hinj)

noncomputable def goodSmallAssignment (s : TupleVertex → ZMod (smallModulus ps)) : Prop :=
  ∀k<24,smallStrictPair ps (s (cycleVertex k)) (s (cycleVertex (k+1)))

noncomputable def goodSmallProbability : ℝ := by
  classical
  letI : NeZero (smallModulus ps) := ⟨(smallModulus_pos ps).ne'⟩
  exact 𝔼 s : TupleVertex → ZMod (smallModulus ps),if goodSmallAssignment ps s then (1:ℝ) else 0

end Small

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_PrimeSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SquareDifference

structure SourcePrimeHyp {S J : Type} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
    (ps : S → ℕ) (p : J → ℕ) [∀s,Fact (ps s).Prime] [∀j,Fact (p j).Prime] (N : ℕ) : Prop where
  injective : Function.Injective (extendedPrime ps p)
  lower : ∀j,64≤p j
  mass : ∀j,max tupleMassThreshold tupleConditionalThreshold≤(p j:ℝ)
  reflection : ∀j,tupleReflectionThreshold≤(p j:ℝ)
  coprime : ∀j,(smallModulus ps).Coprime (p j)
  exceptional : ∀j,tupleEta (p j)≤1/(p j:ℝ)^4
  cover : ∀r : ℕ,r.Prime → r≤N → ∃i,extendedPrime ps p i=r

def smallPrimeSet (P : ℕ) : Finset ℕ := (range P).filter Nat.Prime

def largePrimeSet (P N : ℕ) : Finset ℕ := (Icc P N).filter Nat.Prime

abbrev SmallPrime (P : ℕ) := ↥(smallPrimeSet P)

abbrev LargePrime (P N : ℕ) := ↥(largePrimeSet P N)

def smallPrimes (P : ℕ) : SmallPrime P → ℕ := Subtype.val

def largePrimes (P N : ℕ) : LargePrime P N → ℕ := Subtype.val

instance smallPrimes_fact (P : ℕ) (s : SmallPrime P) : Fact (smallPrimes P s).Prime :=
  ⟨(mem_filter.mp s.property).2⟩

instance largePrimes_fact (P N : ℕ) (s : LargePrime P N) : Fact (largePrimes P N s).Prime :=
  ⟨(mem_filter.mp s.property).2⟩

end SquareDifference

end

end OAI
end

section
-- module Solutions.OAIB3_Sqd.SquareDifference_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Finset

namespace SquareDifference

def natTranslate (A : Finset ℤ) : Finset ℕ := A.image (fun z => (z-1).toNat)

end SquareDifference

end

end OAI
end


