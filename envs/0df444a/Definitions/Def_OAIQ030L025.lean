-- Prove2me | Definitions.Def_OAIQ030L025
-- name    : OAIQ030L025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:33:51.341332+00:00
-- url     : https://prove2.me/theorems/686ffc94-9cf1-4054-bcbc-3184ad8df221
-- title:
--   Definitions bundle OAIQ030L025 of the split of OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 40 definitions, 4 instances and 10 theorems. The definitions and types are `OAI.LaughlinGap.RealOccupation.SumTable9.s_1_4`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_1_5`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_1_6`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_1_7`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_2_1`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_2_2`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_2_3`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_2_4`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_2_5`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_2_6`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_2_7`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_3_0`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_3_1`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_3_2`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_3_3`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_3_4`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_3_5`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_3_6`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_3_7`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_4_0`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_4_1`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_4_2`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_4_3`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_4_4`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_4_5`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_4_6`, `OAI.LaughlinGap.RealOccupation.SumTable9.s_4_7`, `OAI.LaughlinGap.RealOccupation.lift`, `OAI.LaughlinGap.RealOccupation.rowAlphaInteger`, `OAI.LaughlinGap.RealOccupation.rowLambdaInteger`, `OAI.LaughlinGap.Spin.LowNestedIndex`, `OAI.LaughlinGap.Spin.binomialPairTensor`, `OAI.LaughlinGap.Spin.integerCoupling`, `OAI.LaughlinGap.Spin.limitingHighestCoefficient`, `OAI.LaughlinGap.Spin.onFirstMap`, `OAI.LaughlinGap.Spin.onSecondMap`, `OAI.LaughlinGap.Spin.swap23Linear`, `OAI.LaughlinGap.Spin.transposeMap`, `OAI.LaughlinGap.threeBodyDimensionRatio`, `OAI.LaughlinGap.threeBodyTailStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`LaughlinGap_CovariantLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/CovariantLift.lean), [`LaughlinGap_ExactRows`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/ExactRows.lean), [`LaughlinGap_IntertwiningSpin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/IntertwiningSpin.lean), [`LaughlinGap_LowNested`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/LowNested.lean), [`LaughlinGap_NestedSpin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/NestedSpin.lean), [`LaughlinGap_PairSpin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/PairSpin.lean), [`LaughlinGap_RationalCoupling`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/RationalCoupling.lean), [`LaughlinGap_SpectralBound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/SpectralBound.lean), [`LaughlinGap_SpinWork`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/SpinWork.lean), [`LaughlinGap_SumTable9`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/SumTable9.lean), [`LaughlinGap_TensorSpin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/TensorSpin.lean), [`LaughlinGap_ThreeSpin`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LaughlinGap/ThreeSpin.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ030L028`.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ030_LG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpectralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral Bound. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators Topology
open Filter

noncomputable def threeBodyDimensionRatio (Q z : ℕ) : ℝ :=
  (3 * (Q : ℝ) - 1 - 2 * (z : ℝ)) / (2 * (Q : ℝ) - 1)

noncomputable def threeBodyTailStar (z : ℕ) : ℝ :=
  if 17 ≤ z ∧ Odd z then
    (3 / 2 : ℝ) * (3 * (z : ℝ) - 1) * ((z : ℝ) + 1) * (1 / 2 : ℝ) ^ z
  else 0

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CovariantLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariant Lift. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def lift (B : ι → Matrix κ κ ℝ) :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ where
  toFun A := ∑ i, ∑ j, A i j • ((B i).transpose * B j)
  map_add' A C := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r A := by simp [Finset.smul_sum, smul_smul]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpinWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Work. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Topology
open Filter

noncomputable def limitingHighestCoefficient (u v : ℝ) (z p : ℕ) : ℝ :=
  (-1 : ℝ)^(z-p) * Real.sqrt (z.choose p : ℝ) * u^p * v^(z-p)

open Polynomial

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_TensorSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma dot_eq_zero_of_distinct_eigenvalues {ι : Type*} [Fintype ι]
    (A : Module.End ℝ (ι → ℝ)) (hA : ∀ x y, dotProduct (A x) y = dotProduct x (A y))
    {x y : ι → ℝ} {μ ν : ℝ} (hx : A x = μ • x) (hy : A y = ν • y) (hμν : μ ≠ ν) :
    dotProduct x y = 0 := by
  have h := hA x y
  rw [hx, hy, smul_dotProduct, dotProduct_smul] at h
  exact (mul_eq_zero.mp (show (μ-ν)*dotProduct x y = 0 by
    simp only [smul_eq_mul] at h; nlinarith)).resolve_left (sub_ne_zero.mpr hμν)

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntertwiningSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intertwining Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def transposeMap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) := by
  classical
  exact {
    toFun := fun x i => ∑ k, A (fun j => if i=j then 1 else 0) k * x k
    map_add' := by intro x y; funext i; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by intro r x; funext i; simp [Finset.mul_sum, mul_left_comm] }

lemma transposeMap_adjoint {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (x : ι → ℝ) (y : κ → ℝ) :
    dotProduct (A x) y = dotProduct x (transposeMap A y) := by
  classical
  rw [A.pi_apply_eq_sum_univ x]
  simp only [dotProduct, transposeMap, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma eq_of_dotProduct_eq {ι : Type*} [Fintype ι] {x y : ι → ℝ}
    (h : ∀ a, dotProduct a x = dotProduct a y) : x = y := by
  classical
  funext i
  simpa [dotProduct] using h (fun j => if j=i then 1 else 0)

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def binomialPairTensor (Q p : ℕ) : (Fin (Q+1) × Fin (Q+1)) → ℝ :=
  fun ij => if ij.1.val + ij.2.val = p+1 then
    ((ij.1.val : ℝ)-ij.2.val)*Real.sqrt (Q.choose ij.1.val : ℝ)*
      Real.sqrt (Q.choose ij.2.val : ℝ) else 0

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def onFirstMap {ι κ σ : Type*} (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ((ι × σ) → ℝ) →ₗ[ℝ] ((κ × σ) → ℝ) where
  toFun x pq := A (fun i => x (i,pq.2)) pq.1
  map_add' x y := by
    funext ⟨p,q⟩
    exact congrFun (A.map_add (fun i => x (i,q)) (fun i => y (i,q))) p
  map_smul' r x := by
    funext ⟨p,q⟩
    exact congrFun (A.map_smul r (fun i => x (i,q))) p

@[simp] lemma onFirstMap_apply {ι κ σ : Type*} (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (x : (ι × σ) → ℝ) (p : κ) (q : σ) :
    onFirstMap A x (p,q) = A (fun i => x (i,q)) p := rfl

def swap23Linear (Q : ℕ) : Module.End ℝ (((Fin (Q+1) × Fin (Q+1)) × Fin (Q+1)) → ℝ) where
  toFun x ijk := x ((ijk.1.1,ijk.2),ijk.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NestedSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct

noncomputable def onSecondMap {ι κ σ : Type*} (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :
    ((σ × ι) → ℝ) →ₗ[ℝ] ((σ × κ) → ℝ) where
  toFun x pq := A (fun i => x (pq.1,i)) pq.2
  map_add' x y := by
    funext ⟨p,q⟩
    exact congrFun (A.map_add (fun i => x (p,i)) (fun i => y (p,i))) q
  map_smul' r x := by
    funext ⟨p,q⟩
    exact congrFun (A.map_smul r (fun i => x (p,i))) q

@[simp] lemma onSecondMap_apply {ι κ σ : Type*} (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (x : (σ × ι) → ℝ) (p : σ) (q : κ) :
    onSecondMap A x (p,q) = A (fun i => x (p,i)) q := rfl

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_LowNested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low Nested. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

abbrev LowNestedIndex (T : ℕ) := (D : Fin (T+1)) × Fin (D.val+1)

lemma lowNested_valid {Q T D r : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (hD : D ≤ T) (hr : r ≤ D) :
    r ≤ Q ∧ D-r ≤ min (2*Q-2) (Q+Q-2*r) ∧
      T-D ≤ (2*Q-2)+(Q+Q-2*r)-2*(D-r) := by omega

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Coupling. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Polynomial
open Polynomial

noncomputable def integerCoupling (c z l : ℕ) : ℚ[X] := (X-1)^z * (C (c:ℚ)*X+1)^l

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ExactRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def rowLambdaInteger : Fin 8 → ℤ := ![6971289, 4543418, 2122516, 3473755, 1187195, 1558861, -522862, 1523334]

def rowAlphaInteger : Fin 8 → Fin 8 → Fin 9 → ℤ := ![
  ![![0, 0, 2967, -8940, 597844, -3700599, -1482135, -1339330, -1774974], ![0, -1484, 0, -400546, -727512, 452505, 336757, -687973, 0], ![742, 2235, 200273, -333763, -26754, 152623, 53954, 0, 0], ![-2235, -74731, 515641, -77419, 104592, -28049, 0, 0, 0], ![11959, 64406, 79631, -160154, 59858, 0, 0, 0, 0], ![-689922, -67178, 66061, -77891, 0, 0, 0, 0, 0], ![59862, -44385, 84784, 0, 0, 0, 0, 0, 0], ![153877, -34627, 0, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, -25023, -53790, 766486, 9140658, 6404627, 13809118, 23999206], ![0, 12512, 0, -81797, -655373, -2080938, -2714428, 2099732, -5178959], ![-6256, 13448, 40899, 710335, 786050, -693550, 623937, -1143911, 0], ![-13448, -95811, -546491, -138110, 34419, -267131, -144692, 0, 0], ![123267, -216124, -122255, 80152, -24553, 132133, 0, 0, 0], ![937778, 118499, 304496, 31238, 59346, 0, 0, 0, 0], ![1417, -356711, 56605, -65505, 0, 0, 0, 0, 0], ![-131919, -496957, 74692, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, 40292, 23298, -1528688, 1746358, -12625070, -2802951, -6221618], ![0, -20146, 0, 520862, 3752616, 3182905, 4997631, 2764684, 861720], ![10073, -5824, -260431, -498930, 791582, 797383, 224990, -770365, 257970], ![5824, 191086, -439224, -64123, 275842, 867800, 34013, 364701, 0], ![-156414, -358613, -895366, -226478, -106557, 44603, 621822, 0, 0], ![1390987, 809119, -671849, -312442, 38220, 292352, 0, 0, 0], ![-51065, 534431, -193959, -39966, 151939, 0, 0, 0, 0], ![996138, 485619, -35844, 2051, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, 260793, 1619513, -9479213, -9905866, -2635931, -19784496], ![0, 0, 0, -921422, -5959267, -3855561, -5424538, -3111939, 8971929], ![0, -65198, 460711, 981829, 1266048, 467412, 2221895, 5826028, -4062050], ![65198, -202439, 507988, -1218507, -969129, -1457246, 510645, -2757862, -105174], ![73303, 1083365, 1360170, 496901, 546989, 591478, -1611153, 541242, 0], ![-3047173, -422296, 565219, 51950, -138923, -157439, 384768, 0, 0], ![-1096705, -516126, -272886, -590124, 310843, 424224, 0, 0, 0], ![-907772, 513824, -898660, 386231, 250109, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, 105594, -4061461, 6356394, 10585121, -6662244], ![0, 0, 0, 110095, -1847081, -3073897, -2667170, -8745701, 5964734], ![0, 0, -55047, -433408, -2935870, -4255122, -2157050, -4954706, -4844675], ![0, -13199, 895178, 1245604, -560549, -1093209, -872791, 718839, 1986698], ![47323, 37137, 717733, 1000936, -51292, -45155, -380146, 602091, 78888], ![-1084895, -476551, 1133209, 876644, -325993, -113185, 946782, -228390, 0], ![-1146443, -1427889, 250513, 803576, -775332, 795845, 94822, 0, 0], ![-1103184, -439205, 578684, -576406, 521912, 2369, 0, 0, 0]],
  ![![0, 0, 0, 0, 0, 1307234, 1613443, -12951363, 31680953], ![0, 0, 0, 0, 281037, 661119, -2279616, 5048517, -23313511], ![0, 0, 0, 58302, -216885, -757322, -7019672, -5556231, -4399124], ![0, 0, -128561, -217031, 206708, -4699975, -3183010, -1044281, 2334083], ![0, -52551, 405571, 290575, 700566, -1549534, 387879, 5277042, -3807459], ![251228, -457263, -370075, 2178628, 928006, -250704, 3565738, -1838288, -1006797], ![447635, 843581, 712865, 1465846, 157586, 2126100, -1099955, 74867, 0], ![-1885572, -2909636, 386414, 199797, 509416, -417784, -153850, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 962082, -4231547, 6336802], ![0, 0, 0, 0, 0, 554480, 519996, -3314368, -8609585], ![0, 0, 0, 0, 8439, 936902, -1855598, -3611338, -2870966], ![0, 0, 0, -22438, 326366, -903827, -684137, -5872845, 530800], ![0, 0, -41983, -291963, 67578, 107968, -4215760, 473171, -2108792], ![0, -52838, -406574, 473590, 277799, -2954710, 85152, -1038229, 12413], ![245134, 588941, 460312, 152807, -910473, 428359, -647302, 35163, -1436712], ![-2025, -885233, -317059, -405381, -399637, -622199, -249650, -812670, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 4582620, -21402093], ![0, 0, 0, 0, 0, 0, 2744534, -4053241, 2091862], ![0, 0, 0, 0, 0, 1254615, 119326, -1351192, 846998], ![0, 0, 0, 0, 251416, 819674, -831726, 1116146, -3026818], ![0, 0, 0, -366503, -138643, -262993, -69789, -2014575, 2467955], ![0, 0, -442958, -386858, 237177, 21361, -945799, 490916, 623063], ![0, 312317, 378534, 414641, -381651, -1214503, 525474, 331451, -671780], ![1126574, 51881, -475448, -1232794, -905053, 27808, -429230, -574069, -776706]]
 ]

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table9. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable9

def s_1_4 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, -114237024, -32139152, 14773616, 26501616], ![0, 0, 0, 0, -2730868296, 888948528, 1186545064, -414269760, -2489687292], ![0, 0, 0, 3428658560, -4397040736, -730798000, 5014531536, 7460175264, 5261441232], ![0, 0, -1287030432, 9046283200, -4395083224, -8198499888, 2119638192, 14512066560, 12798803532], ![0, 1445319888, -2727103824, 2051893200, -2699674656, -12541931280, -10799609264, 9009726384, 24239259912], ![-504121152, -459236976, -1580875968, 1648119056, 8852519264, -10258990384, -50644820096, -46936312016, 67395213856], ![-124084752, -2069880384, 4210909440, -2097837776, -19311560080, -373233120, 58677388448, 54372480304, -134659606176], ![99780992, 336249600, -3201374208, 9230594240, 11732196480, -54292939392, -100862798848, 195959627712, 1032784015104], ![339305984, 780455936, 600565760, 3505246720, 14544808960, 30409156096, 41779782144, 65051670528, 197372583936]]

def s_1_5 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 399935088, -244781328, -218021840, 192438096, 698823144], ![0, 0, 0, 1661387024, -170651704, -1577391016, -2246028464, -1997818736, -788074388], ![0, 0, 813274272, -1608294752, -3714900088, 1599716784, 11840566768, 19026236288, 13803707868], ![0, 337141452, -8670367476, 22585357452, 5823519300, -28238114268, -26404240332, 26510282964, 88203373752], ![-2325184, 3796679336, -4349627488, 2289182648, 3658927952, -44329174024, -100069123456, -33928707928, 219356691728], ![-978735200, -703209856, -1247939328, -1866830528, -8158159360, -36660037632, -83429403008, -98627686336, -25763165280], ![-119043968, -4998679296, 3221129472, 32459701920, -46137335040, -281287060032, -204851711104, 998150939424, 3011654462976], ![621161600, 3621979520, -6524928640, -26778353600, 71825199040, 372578811712, 392750639424, -977249168640, -3753388311552], ![954602496, 2695069440, 0, 128411520, 62381095680, 249758416512, 415134383616, 79356524544, -902860434432]]

def s_1_6 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 60625040, 383174672, -238278256, -742629376, -523532224, 570600392], ![0, 0, 1014848544, -2794418080, 780563656, 2894788848, 1806222192, -168332928, 302635452], ![0, 257917176, -2209377480, 5367374168, 690922920, -8358578232, -7556951256, 5330820456, 12117435648], ![-86195120, 660710872, 469309792, 1256769544, -8825195504, -22558055480, -17288668928, 20754175384, 66872022496], ![-570696256, -84703616, -4451409408, -10176627872, 23325512480, 67265942592, -48829854144, -426558617760, -643453212960], ![1065806976, -21137664, 4922021376, 10742699520, 3165816960, 12332578560, 117274946304, 345151517184, 531525802752], ![281461504, 2048244736, 2193909760, -16391288320, 13888167680, 208448969216, 347194801152, -419652937728, -2734089836544], ![-1023629312, -1505908480, 0, -19130216320, -71876437760, -92532498048, -26402692608, -204984907776, -1718837480448], ![-482887680, 22067896320, 22067896320, -142342809600, -163662336000, 1183379963904, 4300284764160, 4223795355648, -10710080409600]]

def s_1_7 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 786416400, -2628613280, 2994846944, 2513439264, -4390809120, -9564223872, -2735219280], ![0, -590906460, 940165284, -1003653884, 2129329260, 7179081420, 9659425020, 5134698012, -14158414680], ![-220867936, 1011450608, -1706332096, 1894918224, -2545706208, -16467354672, -25188040832, -11962241552, 25502130112], ![-152352544, -4165691648, 2340481536, -1228044640, -20245672160, 17784926784, 144686081984, 220942285216, 24001915392], ![1027543680, -51028992, 7756677120, -1702055360, 5238291840, 114040854912, 207967404032, -154051966656, -1179550220544], ![-248547456, -291356544, 7001769600, 9677231040, -45331185600, -148004884800, -50282356032, 612425293056, 1470762399744], ![-2545447936, -6287248640, 0, -27567693440, -178334337280, -410769560448, -479734110720, -474436233216, -2158546553856], ![-1219476480, 10318540800, 10318540800, -98354856960, -174900510720, 481781145600, 2168133783552, 1974968709120, -7565586462720], ![0, 23860408320, 47720816640, -89476531200, -214743674880, 1102350864384, 5669233016832, 10236115169280, 0]]

def s_2_1 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1201120, -1201112], ![0, 0, 0, 0, 0, 0, 6024640, 3442688, 860752], ![0, 0, 0, 0, 0, 6278304, -61245728, -99831008, -109477440], ![0, 0, 0, 0, -1080997856, -299669920, -566718560, -1432839776, -2448729232], ![0, 0, 0, 1915122656, 1117019824, 616368624, 161538368, -391261664, -1077980440], ![0, 0, -863961920, -502634624, 2024134880, 3518928576, 3267120320, 1972813056, 694787088], ![0, -540443888, -543765360, -1724249072, -2562260432, 4230269104, 14499167344, 15539105008, -2790928992], ![165776640, 80385712, -1405196128, -1213740464, 1402303744, 181320336, -8378206688, -15156843152, 3238226240]]

def s_2_2 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 1934016, 1934016], ![0, 0, 0, 0, 0, 0, -2609216, -1490944, -372656], ![0, 0, 0, 0, 0, 147739712, 202279424, 233445248, 241236928], ![0, 0, 0, 0, -228921056, 1523300096, 1622275488, 776540480, -305371184], ![0, 0, 0, 279749440, -2569073920, -2505066208, -1259566560, 178090688, 1560573344], ![0, 0, 239519136, 1243122240, -2473311536, -3674597824, -2015625568, -1088474304, -5469524200], ![0, 1230881936, 266701648, 2614273360, 882558000, -1438524176, -1568344400, -1399581520, -6317725056], ![-206058304, 146496896, -286324480, 418102656, 782345984, 1239594368, 2182644352, 2536417664, 1096237760], ![-100745728, 270080832, -1226312000, 519482624, 6413178112, -3594504384, -26824944704, -5952065920, 117587352960]]

def s_2_3 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, -29208736, -16690688, -4172632], ![0, 0, 0, 0, 0, -322104432, -297091280, -282798032, -279224680], ![0, 0, 0, 0, -53979824, -3042286048, -2739029168, -554878400, 2099496360], ![0, 0, 0, 637936192, 3168764288, 2922715616, 2990397280, 5137870400, 9806650144], ![0, 0, 1356270432, -846205696, 1878929296, 2838426592, 1821136672, 2319980160, 8753904312], ![0, -3362156608, -1194269376, -684249216, -1973557472, -9880320640, -21564973376, -28715104512, -25631999696], ![489377984, 575164976, -821711200, 12208437712, -10774654976, -22285151984, 21627928224, 62718818800, -44641296640], ![-34599168, -454836160, 4685780032, -10732206336, 3745236736, 50939081920, 37533449536, -119929833600, -315079102080], ![-76002048, 79277696, -2531506176, -8105704960, 16081330176, 16547688576, -101225720320, -227826996480, 51208646400]]

def s_2_4 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 55235424, 18748320, -2102048, -7315040], ![0, 0, 0, 0, 1390717072, -259422752, -433020976, 237119360, 1118194536], ![0, 0, 0, -2353352384, 1364669376, -313598176, -3204668960, -4917976128, -4855875840], ![0, 0, 501595744, -4381636608, 2403505744, 5384244064, 1945137824, -3182195584, -3429370344], ![0, -910310112, 1066176096, -2386376544, 3703110272, 2177979360, -8616975584, -9381060512, 23733444400], ![-1115391872, 1603574304, 5721655104, -4971072928, 14362567680, 32553268960, 15459748288, -2636801504, 66290856960], ![-101047104, 1083995808, -6416181664, 3670999168, -14507064960, -20274733024, 42321673184, 85291035200, -84105037440], ![354247296, 295234944, -3479514112, -12108099072, 30430220800, 8958428288, -251710653440, -499367128320, 82275338880], ![159573504, 522000384, 1478985728, 170973184, -1778917376, -52679680, -3526548480, -47431019520, -184563371520]]

def s_2_5 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, -191413408, 91410464, 75800864, -110342432, -339119248], ![0, 0, 0, -929580000, 270972688, 1179991728, 1658450848, 1626906912, 1065499352], ![0, 0, 84596704, 1226559744, 1236917264, -2696137696, -9117198304, -14132446208, -13238457480], ![0, -825043016, 4231199320, -11686112744, -2922481080, 13553110152, 15056607336, -1402448856, -18575612016], ![1041778560, -2753507024, 2516118304, -15400181296, 14981986048, 24089616656, -59780141792, -161731052304, -66900952640], ![-628337664, -374016512, 227579008, -3237555712, 10249063936, 31096519040, 23637892992, -8111676160, 42578922240], ![-815030784, 5460591040, -20565325824, -11662835968, 130136204800, 24439935424, -656851831040, -874469001600, 1823800907520], ![85107072, -3833995008, 23120911616, 20903051008, -114707184384, -25860055680, 874718156160, 1775470723200, -850575813120], ![-153327616, -37413376, 12637068288, 21822819840, -12180060160, 28875214080, 461434682880, 1205003162880, 775662243840]]

def s_2_6 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, -120294016, -216603360, 90381408, 329055040, 229931456, -274359376], ![0, 0, -409606944, 1509634816, -404804464, -1979864160, -2199356128, -1851020032, -2173578056], ![0, -374877840, 314636592, -3804281168, -11472304, 4273845392, 4470422992, 5679407824, 19262304512], ![46595520, 121955920, -1432120224, 1214510256, 6684772864, 5571405168, -9705619616, -28735238256, -12247854720], ![-73019904, -2424261312, 6818911680, -5464989440, -51037945600, 41904564800, 248020716224, 59812073600, -1034340416640], ![251040896, 2654301952, -2330860544, 4123488256, 5100176896, -28290357248, -67608133120, -21951313920, 142850586240], ![-318129408, -2357471232, 14373818368, 30630230016, -52574229504, -20604789760, 629461647360, 1570154849280, 491898274560], ![-72013824, -2942737920, -4424956928, 5912957440, -15283251200, -79783476480, 4287951360, 495159540480, 1083634421760], ![6271082496, -11843592192, 31519580160, 102983516160, -431990046720, -1694858342400, -1283584389120, 2912962314240, 0]]

def s_2_7 : Fin 9 → Fin 9 → ℤ := ![![0, 0, -345393728, 1249700352, -1321530240, -1284543296, 1546147968, 3590851200, 328576896], ![0, 511747816, -556655928, 250466696, 371289368, -3019051304, -5649780360, 1973197240, 29136109616], ![-214049280, -114799072, 2137040960, 2880475360, 4763577856, 7386865248, 5085125056, -8047666272, -31341412480], ![229341952, 449612096, -12060232384, 4235793152, -28986150144, -71890217024, -20640992704, 53240677760, -170337790080], ![-654576256, 2095790976, 8676076544, 23773982208, -33925509632, 16954558848, 440534225920, 824943064320, -113216123520], ![330103936, 1333122816, -10454695168, -2373459712, 44758344448, -38816880000, -445119753600, -740689027200, 498161664000], ![-678811648, -4873779712, -17960375296, -616532480, 18734458880, -71933679360, -181112486400, 317590606080, 2412568350720], ![3727192064, -8717643776, 9968275456, 48153190400, -273536040960, -1078666352640, -993680455680, 1362047385600, 0], ![6362775552, -4772081664, 31813877760, 143162449920, -286324899840, -1968483686400, -3149573898240, 0, 0]]

def s_3_0 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 142592, 142512], ![0, 0, 0, 0, 0, 0, 1001280, 572160, 143040], ![0, 0, 0, 0, 0, 223639360, 246402688, 259411072, 262663680], ![0, 0, 0, 0, 81305056, -761065984, -713518624, -157446848, 525755952], ![0, 0, 0, 465373440, 187883360, -48154848, -275498048, -512867520, -764945584], ![0, 0, -268043200, -503256192, -1032903744, -1381419072, -1723082240, -2603509632, -4661148640], ![0, -146355104, -32816160, -848723104, -1409555872, -1799429600, -2649245664, -5118321760, -10791331168]]

def s_3_1 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1201280, -1201200], ![0, 0, 0, 0, 0, 0, 6024704, 3442432, 860320], ![0, 0, 0, 0, 0, 190014720, 122491712, 83906880, 74260608], ![0, 0, 0, 0, -456356992, 1126114752, 1660213184, 1595239616, 1380496992], ![0, 0, 0, -3625272448, -2985629472, -2185995168, -1477999488, -1005433152, -804244784], ![0, 0, 3267563392, 991949184, -1850355008, -6312887936, -10966371456, -12962800896, -9099507808], ![0, -1393163168, -662665184, 4443855136, 2237270496, -8569826848, -24196400672, -32901902112, -15748203136], ![258243072, -1138251232, 1881711872, -2188673696, -5007815488, 2021266272, 14055069312, 7188494368, -55347136064]]

def s_3_2 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 1934016, 1934016], ![0, 0, 0, 0, 0, 0, -2609152, -1491200, -373088], ![0, 0, 0, 0, 0, -459099200, -404559232, -373393408, -365601984], ![0, 0, 0, 0, -1508787392, -53496576, -251450304, -1394113152, -2772952032], ![0, 0, 0, 1078739200, 3966686080, 6222988352, 6116300736, 2657288832, -4401377280], ![0, 0, -3764972352, -880094720, -331249248, 4081411200, 11667682368, 17800168832, 16867164208], ![0, 1458572576, 1124658592, -140254048, -3114132128, -1770390048, 7613548896, 22492242272, 32751031424], ![-104453440, -188420608, 1028639488, 247419648, -1048788864, 146628864, 1500224512, -4968396032, -25412924608], ![30171648, -949204224, 4526010624, -11312078208, 10677489024, 33978049024, -33960930304, -149245466496, -60468949632]]

def s_3_3 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, -29208704, -16690816, -4172848], ![0, 0, 0, 0, 0, 569169440, 594182624, 608475744, 612048880], ![0, 0, 0, 0, 4322640672, 424561088, -181953632, 1092426112, 2837029456], ![0, 0, 0, -6290530176, -4967288704, -7362117952, -10384407488, -12268094848, -12571664640], ![0, 0, 5151188608, 4423099904, 5542884640, 2450707776, -4431157312, -10976358400, -12132514320], ![0, -607633856, -6060894592, -8383092736, -1295457216, 15374866048, 39411583872, 64024422656, 78380158560], ![-201337664, 3215165472, -2786066944, -2438090656, -10261671616, -3527798176, 15826641536, 31124018464, 97310336256], ![-93035136, 287474176, -259227904, 5272318336, -11948347008, -8264916480, 88591254528, 201553712000, -3010797312], ![138557952, -2344978944, 13691630592, -40974732032, -4711910400, 134777466880, 14791211008, -538926803712, -682636316160]]

def s_3_4 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, -1008896, -37495360, -58345792, -63558976], ![0, 0, 0, 0, -61066656, -1190412608, -843217760, 347716352, 1749586576], ![0, 0, 0, 3822137088, 2779367808, -21285824, -396340672, 4044771456, 13899696576], ![0, 0, -1974204160, 53565696, 327036320, -8780247488, -22037426752, -26866583040, -8853017296], ![0, -1859011264, 913282752, -712978624, 9072160896, 18225086400, 14166401856, -10764612928, -55407461728], ![-698844160, -166228928, 4830865664, 13176835392, 22388270208, -2731963328, -56756797696, -91994762304, -98224268672], ![402070592, -2419370368, -2191235456, 29876805696, -46107642560, -98227458816, 98174917120, 343019849024, -120065063808], ![154135296, -1775105024, 26402267136, -91790119680, -14328631296, 257883437056, -68060561408, -1317134113536, -1503763841280], ![-96740352, 824520704, 2941575168, 1248759808, -11779661824, -42211807232, -94392496128, -178384373760, -323137182720]]

def s_3_5 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, -162223936, 167428800, 198649024, 59335232, -122612960], ![0, 0, 0, 1078185024, -1037528800, -2153103008, -2407557824, -1880333760, -591290960], ![0, 0, -633079296, -3262386816, 2489761824, 9445329856, 14693497536, 17761858048, 18787608944], ![0, 2548967344, -6115641296, -701223632, 11182212112, -6962623088, -70248292656, -146993951920, -151543604896], ![1136465920, -3011777504, -2640714240, -13593112992, 14572658880, 65239820384, 117502893696, 151066520864, 86110922688], ![147875968, -3510518528, 2522540032, 5320568576, 17651528192, 52051712000, 103990949888, 132438465280, 22662205056], ![1350922752, -17897515264, 82445540864, -198423102080, 55397874176, 852935114752, -15264134144, -3619487526528, -4850661864960], ![-1915912960, 14305371392, -58183904000, 185251367424, 84998197760, -952528299520, -923427681792, 3225393841920, 7984975933440], ![-954296320, 3403045376, -9005746176, 79383929856, 113896466432, -286821964800, -737211310080, 236444398080, 2468650060800]]

def s_3_6 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 477910720, -67621568, -4928448, 194380032, 260818944, 127021472], ![0, 0, 251641856, -1164293504, -530831584, 3276529344, 8225413312, 10479515136, 5751548144], ![0, -948353568, 385773536, 509778272, 3065488032, -2292419808, -22785529184, -55667257952, -85778442240], ![319887808, -2151300640, 4278446080, -4697679200, -3182154816, 33089707680, 81589227904, 70084507616, -75892223360], ![-567982336, 5717223680, -33748288256, 101066408064, -106895201920, -298908761600, 347958768640, 1364412001920, 376610604672], ![121131776, -352551424, 8647808000, 1641013248, -16213281792, -49205065728, -162747475968, -425552676864, -758765656320], ![-1071424000, 8319485952, -50753523712, 147752685568, 135854917632, -540965777408, -452852047872, 2620281231360, 6199317020160], ![48717824, 2899080704, -27555903488, -978740224, 59398535168, -8698045440, 71168778240, 1357128199680, 4516316851200], ![-6077927424, 69368217600, -106518282240, 120045453312, 249034014720, -3451477524480, -11190791208960, -8496140083200, 24990187622400]]

def s_3_7 : Fin 9 → Fin 9 → ℤ := ![![0, 0, -186324544, 584366720, -1475528320, -147926912, 4196210816, 7420743680, 4448225600], ![0, 102264848, 2106696848, -2524527088, -4714896720, -2757528016, -628625936, -9859812752, -49297198304], ![-220355456, 561066688, -30229760, -1187688896, 8106892672, 31246011968, 54700071680, 59254322880, 50740027392], ![88658816, 667140608, -2631564544, 8204119936, -85213368448, -157596448256, -17321823232, 168626135424, -146835862272], ![-515731200, 2609803776, -30900604928, 159045590784, 19331293184, -446914994176, 234594304, 1802926919424, 1664928288000], ![883145472, -3623803136, 16329396992, -80730024448, -29490926080, 378897430016, 339026548224, -1290349336320, -2889025075200], ![977422336, -1550904832, -42194642944, -49127271424, 82303993856, 412234798080, 1106135654400, 2689180961280, 6162473856000], ![-3239401472, 41974693888, -75244371968, 30692646912, 102134611968, -1995423006720, -6281940910080, -3972638208000, 17653035079680], ![-6362775552, 63627755520, -38176653312, 104985796608, 381766533120, -3149573898240, -14698011525120, -23884268728320, 0]]

def s_4_0 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -3417984, -3418272], ![0, 0, 0, 0, 0, 0, -24030720, -13731840, -3432960], ![0, 0, 0, 0, 0, -2410507008, -2956837632, -3269026560, -3347074944], ![0, 0, 0, 0, -14920815168, 5866656768, 5296089792, -7479070848, -23305379616], ![0, 0, 0, 3983978880, 1657010880, -1560500928, -4882329984, -7859206272, -10378810848], ![0, 0, -1542908160, 246805248, 4529060736, -2201019264, -17852111616, -31420771584, -29675521728], ![0, 511192512, -3118667328, 4839575232, 2291544000, -8972770752, -20601387456, -27578960064, -30701505600]]

def s_4_1 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 28826496, 28826784], ![0, 0, 0, 0, 0, 0, -144587520, -82621440, -20654784], ![0, 0, 0, 0, 0, -3090471552, -1469897856, -543858048, -312350976], ![0, 0, 0, 0, 36855133056, 5284927872, -1124237184, 6844328064, 18407318976], ![0, 0, 0, -17215637376, -8172865344, -4069595712, 1133352192, 10886934144, 26053885344], ![0, 0, 15908103936, -6618040320, -28429689984, -7091262720, 40246137600, 62381807616, -397402560], ![0, -6911771328, 25573096512, -35736790464, -21707926848, 47972576448, 92796600768, 44577602496, -134263748736], ![0, 2983080384, -23169624192, 45077587008, 43369357056, -90841162944, -237763433088, -191410152768, 182132153856]]

def s_4_2 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 0, -46416384, -46416384], ![0, 0, 0, 0, 0, 0, 62625024, 35785728, 8947008], ![0, 0, 0, 0, 0, 6163670016, 4854710784, 4106734080, 3919739904], ![0, 0, 0, 0, 7041315456, -30261095424, -27885664128, -2837180160, 27879564096], ![0, 0, 0, 33936188160, 8698851840, -29734728576, -39812481408, 2209650432, 102267694464], ![0, 0, -3228999552, -22561931520, 40265623872, 28174337280, -50553164160, -93141759744, 26806752864], ![0, 1791825984, 994353984, -15224383680, 33810957504, 37818984384, -85833828672, -267216167232, -252602601984], ![0, -496350720, -571737600, 9993497088, 1933893120, -34290885120, -69482276352, -39658258944, 130674885120], ![0, -297181440, 6035717376, -48829644288, 90061475328, 233046759168, -205979585280, -1308718322688, -1785484753920]]

def s_4_3 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, 0, 701011584, 400578048, 100144800], ![0, 0, 0, 0, 0, -6529876416, -7130190144, -7473226560, -7558985376], ![0, 0, 0, 0, -38220186816, 48055529088, 55333707072, 17470432512, -31678208352], ![0, 0, 0, 26626967808, -44404727808, -33732306048, -15530352768, -32184352512, -94290685056], ![0, 0, -3036592512, 33211106304, -21117796800, -15519841920, 44937584256, 66289473024, -67653605664], ![0, 5697934848, -24263712000, 8525119488, 9508553856, 2004526080, 38000152320, 147177796608, 324171672768], ![0, -5167831104, 57853323648, -154541075904, -28741061376, 367131477312, 301271435136, -656906289984, -1590493685760], ![0, 4679481600, -67531790592, 270359643648, -10799371776, -1178427273984, -1293001785600, 2463099896832, 10168607296512], ![0, 242320896, 7068321792, -93949867008, 198357590016, 559114698240, -735453229056, -4294973085696, -5409578649600]]

def s_4_4 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 0, -425755008, 449952384, 950354304, 1075453056], ![0, 0, 0, 0, -16375810752, 14894861184, 10728508224, -13687570944, -43166081376], ![0, 0, 0, -17085987072, -16244911872, 55892704896, 98923085184, 55472653056, -88801979136], ![0, 0, 12194059392, -1920039936, -84997656768, 8767069056, 216603621504, 299412186624, -25989328800], ![0, 1918726272, -25906273920, 81403216512, -54220225536, -148787961984, 88118050944, 578701425024, 783290335680], ![0, -3435686784, -2217164544, 86043831168, -58846990848, -262915986048, -2470850304, 856478692992, 1327686998016], ![0, 5581065600, -43604770176, 59151863040, 100913721600, 126233398656, 16598037120, -1230584381952, -4846791527424], ![0, -4577352192, 66025967616, -262228227072, 147295927296, 1134374782464, -576535314432, -6942220425216, -10061519293440], ![0, -363515904, -2966630400, 38319476736, 49614716928, -217664692224, -846497046528, -1128344739840, 796042874880]]

def s_4_5 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, 0, 5270767488, -2266282368, -2640914304, 1077261696, 5818638528], ![0, 0, 0, -4336934784, 7499731008, 5666388672, -6500376960, -27093957504, -55637716128], ![0, 0, -14919970176, 32148509184, -21982643136, -39970366848, 13115160192, 113681909760, 223507387872], ![0, -9124114464, 39004126560, 23167824480, -298003898592, -215970206688, 721192809888, 2019347204256, 2065931903808], ![0, 13428582336, -106174606464, 264859973184, -50112331008, -785146317504, -274384142976, 2627792357568, 6309503144448], ![0, 5067790848, -55234211328, 105595671552, 177431798784, -184049238528, -668674954752, -323925215232, 1526275215360], ![0, -5377727232, 161799164928, -1080633742848, 902937682944, 6550098686208, 2492726175744, -27020284425216, -68407417866240], ![0, 17544771072, -330938214912, 1345427636736, 1201471477248, -7672250729472, -17004403713024, 6001032545280, 91051428188160], ![0, 9278641152, -161495746560, 456069583872, 1321315688448, -1658262509568, -10531931074560, -13947246213120, 16083882270720]]

def s_4_6 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 0, -2586076416, 5764364928, 1156934016, -5089937664, -6508561152, -1482005568], ![0, 0, -4874742144, 3704157696, 18718310976, -11208756096, -61688546688, -65038285824, 57248381664], ![0, -1824998976, -2161306944, 36056535744, -60737773248, -92933977536, 101593285440, 412820806464, 399910892544], ![0, 4959120960, -46395771264, 115989710784, 53692364544, -300607208256, -478613251968, 165199446336, 1883601122304], ![0, 3307352832, -83890315008, 516276423168, -645079534080, -2256982891776, 835712301312, 10125098671104, 15868294751232], ![0, -1222963200, 23397046272, -94003494912, 37328974848, 631213406208, 471256289280, -2888340553728, -10239845575680], ![0, 9717313536, -184032976896, 757648822272, 443411662848, -4382508490752, -7090967052288, 10828557066240, 57232713922560], ![0, -114398208, 4651665408, 56093420544, -374899531776, -1313936418816, 688566251520, 12412348692480, 33449931694080], ![0, 26481475584, -675944054784, 3008342458368, 7392330252288, -19941077975040, -100717120880640, -122344417198080, 257041929830400]]

def s_4_7 : Fin 9 → Fin 9 → ℤ := ![![0, 0, 5279178240, -21793519104, 34109182464, 19301425920, -61765143552, -114274626048, -20820079872], ![0, 6163802784, -27830075616, 38002326048, 51524636256, -30725355168, -184012781088, -338535429408, -385206129216], ![0, -1204912512, 1003182336, 34356219264, -60969733632, -176267069568, 37712476416, 866150788224, 2126499253248], ![0, -975741696, 19068076800, -65519706624, -51163885056, 296337293568, 248820972288, -1887778581504, -6492433941504], ![0, 6973788672, -120818110464, 491626558464, -46202674176, -1930846385664, -381294133248, 8184985196544, 13420095482880], ![0, -11372336640, 188682177024, -633207144960, -926689494528, 3075079504896, 9272590967808, 3313047813120, -33162968678400], ![0, -5742148608, 127795894272, -361763404800, -1669451685888, 117950515200, 12366923304960, 34150901114880, 34434625167360], ![0, 12382248960, -344677146624, 1711906062336, 3628226248704, -12758262497280, -56537468190720, -57205990195200, 181574075105280], ![0, 28632489984, -687179759616, 2405129158656, 10307696394240, -9448721694720, -113384660336640, -245666764062720, 0]]
end SumTable9
end LaughlinGap.RealOccupation

end

end OAI
end


