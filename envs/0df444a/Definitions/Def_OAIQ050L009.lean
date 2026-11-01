-- Prove2me | Definitions.Def_OAIQ050L009
-- name    : OAIQ050L009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T09:08:36.485345+00:00
-- url     : https://prove2.me/theorems/79f9df51-3ac2-4375-9a68-b5cea814817d
-- title:
--   Definitions bundle OAIQ050L009 of the split of OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 3 definitions, 4 instances and 4 theorems. The definitions and types are `OAI.Laughlin.lowerPair`, `OAI.Laughlin.pairPolynomialCoefficient`, `OAI.Laughlin.rawPairState`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Laughlin_Pair_LoweringAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/LoweringAlgebra.lean), [`Laughlin_Pair_PolynomialLadder`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Pair/PolynomialLadder.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ050L015`; the statements `OAI_Laughlin_Certificate_four_body_7_positive`, `OAI_Laughlin_Certificate_ldl_10`, `OAI_Laughlin_Certificate_ldl_11`, `OAI_Laughlin_Certificate_ldl_9`, `OAI_Laughlin_Fock_averagedFourTransferError_tendsto`, `OAI_Laughlin_Fock_finiteFourMiddle_tendsto`, `OAI_Laughlin_Fock_physicalLimitError_eq`, `OAI_Laughlin_Spin_physicalFourError_tendsto` and `OAI_Laughlin_Spin_threeGram_on_slice`; the proofs of `OAI_Laughlin_Certificate_four_body_7_positive`, `OAI_Laughlin_Certificate_ldl_10`, `OAI_Laughlin_Certificate_ldl_11`, `OAI_Laughlin_Certificate_ldl_9`, `OAI_Laughlin_Fock_averagedFourTransferError_tendsto`, `OAI_Laughlin_Fock_finiteFourMiddle_tendsto`, `OAI_Laughlin_Fock_physicalLimitError_eq`, `OAI_Laughlin_Spin_physicalFourError_tendsto` and `OAI_Laughlin_Spin_threeGram_on_slice`.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ050_Laughlin.Compat
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_LoweringAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

noncomputable def pairPolynomialCoefficient (Q i j : ℕ) : ℝ :=
  ((i : ℝ)-(j : ℝ)) * (Q.choose i : ℝ) * (Q.choose j : ℝ)

end Laughlin

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_Pair_PolynomialLadder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin

noncomputable def rawPairState (Q p i j : ℕ) : ℝ :=
  if i+j = p+1 then pairPolynomialCoefficient Q i j else 0

noncomputable def lowerPair (Q : ℕ) (f : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  (if 0 < i then ((Q : ℝ)-(i : ℝ)+1)*f (i-1) j else 0) +
  (if 0 < j then ((Q : ℝ)-(j : ℝ)+1)*f i (j-1) else 0)

end Laughlin

end OAI
end


