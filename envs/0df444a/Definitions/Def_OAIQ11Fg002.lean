-- Prove2me | Definitions.Def_OAIQ11Fg002
-- name    : OAIQ11Fg002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:29:07.753124+00:00
-- url     : https://prove2.me/theorems/20a70297-4860-46bb-b417-98331cbf8c10
-- title:
--   Definitions bundle OAIQ11Fg002 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 190 declarations of OpenAI's Lean: 66 definitions, 23 instances and 101 theorems. The definitions and types are `OAI.Generator.Tracial.CyclicFamilyIndex`, `OAI.Generator.Tracial.DyadicIndex`, `OAI.Generator.Tracial.ProductFamilyIndex`, `OAI.Generator.Tracial.ResidualWordIndex`, `OAI.Generator.Tracial.SamePowerSign`, `OAI.Generator.Tracial.Sequences`, `OAI.Generator.Tracial.TraceFreePreHilbert`, `OAI.Generator.Tracial.absorbedGapList`, `OAI.Generator.Tracial.algebraInclusion`, `OAI.Generator.Tracial.algebraMixedTail`, `OAI.Generator.Tracial.algebraOrbit`, `OAI.Generator.Tracial.algebraPatchingWord`, `OAI.Generator.Tracial.algebraSignedLetter`, `OAI.Generator.Tracial.algebraWordCore`, `OAI.Generator.Tracial.ambientUnitary`, `OAI.Generator.Tracial.ballContinuousFunctionals`, `OAI.Generator.Tracial.betweenWord`, `OAI.Generator.Tracial.binaryMasks`, `OAI.Generator.Tracial.boundedLists`, `OAI.Generator.Tracial.conjugateLinear`, `OAI.Generator.Tracial.dyadicFalseIndex`, `OAI.Generator.Tracial.dyadicSign`, `OAI.Generator.Tracial.dyadicWeight`, `OAI.Generator.Tracial.exceptionalMask`, `OAI.Generator.Tracial.finalWordSign`, `OAI.Generator.Tracial.functionalSubspaceEvaluation`, `OAI.Generator.Tracial.indexedCoefficient`, `OAI.Generator.Tracial.integerPowerBlock`, `OAI.Generator.Tracial.integerWord`, `OAI.Generator.Tracial.maskedWord`, `OAI.Generator.Tracial.middleMomentError`, `OAI.Generator.Tracial.middleWordFamily`, `OAI.Generator.Tracial.optionalCoefficient`, `OAI.Generator.Tracial.outerWordFamily`, `OAI.Generator.Tracial.patchingCoefficients`, `OAI.Generator.Tracial.patchingExpansion`, `OAI.Generator.Tracial.patchingTolerance`, `OAI.Generator.Tracial.patchingWord`, `OAI.Generator.Tracial.powerBlockGaps`, `OAI.Generator.Tracial.powerBlockWord` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_CyclicPredual`, `FactorGeneration_Dimension`, `FactorGeneration_Exponential`, `FactorGeneration_FreeWords`, `FactorGeneration_FunctionalLimits`, `FactorGeneration_GroupTrace`, `FactorGeneration_HaarPatches`, `FactorGeneration_HaarSequences`, `FactorGeneration_HilbertProjections`, `FactorGeneration_LocalizedStates`, `FactorGeneration_LongWords`, `FactorGeneration_MatrixSequence`, `FactorGeneration_MonotoneTrace`, `FactorGeneration_NormalDimension`, `FactorGeneration_OperatorLimits`, `FactorGeneration_OrbitMinima`, `FactorGeneration_PartialUnitaries`, `FactorGeneration_PatchingBounds`, `FactorGeneration_PatchingWords`, `FactorGeneration_PredualOrder`, `FactorGeneration_PredualRange`, `FactorGeneration_ProductWords`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_QuotientRepresentation`, `FactorGeneration_ResidualMoments`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralPinching`, `FactorGeneration_SpectralTruncation`, `FactorGeneration_Supports`, `FactorGeneration_Target`, `FactorGeneration_TraceHilbert`, `FactorGeneration_TraceTopology`, `FactorGeneration_Words`.
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg004` and `OAIQ11Fg005`; the statements `OAI_Generator_Tracial_betweenWord_integerValue`, `OAI_Generator_Tracial_exists_exact_residual_step`, `OAI_Generator_Tracial_exists_finite_partial_independence`, `OAI_Generator_Tracial_exists_quotient_corner_partial_sequence`, `OAI_Generator_Tracial_integerPowerBlock_eval`, `OAI_Generator_Tracial_integerValueWord_blocks`, `OAI_Generator_Tracial_optionalCoefficient_range`, `OAI_Generator_Tracial_ordered_moment_scale`, `OAI_Generator_Tracial_ordered_sum_zero_of_all_mixed`, `OAI_Generator_Tracial_patchingCoefficients_append_endpoint`, `OAI_Generator_Tracial_predualFunctional_unitBall_continuous`, `OAI.Generator.Tracial.predual_small_of_small_trace_sandwich`, `OAI_Generator_Tracial_quotient_partial_signed_tendsto`, `OAI_Generator_Tracial_quotient_residual_all_words_centered`, `OAI_Generator_Tracial_quotient_residual_word_centered`, `OAI_Generator_Tracial_quotient_residual_word_unit_right`, `OAI_Generator_Tracial_signedLetter_integer` and `OAI_Generator_Tracial_signed_conjugate`; the proofs of `OAI_Generator_FiniteMatrixStage_two_generators_of_tensor_extensions`, `OAI_Generator_MatrixUnitSystem_two_generators_of_four_commutant_generators`, `OAI_Generator_Tracial_betweenWord_integerValue`, `OAI_Generator_Tracial_exists_irreducible_centered_partition`, `OAI_Generator_Tracial_integerPowerBlock_eval`, `OAI_Generator_Tracial_optionalCoefficient_range`, `OAI_Generator_Tracial_ordered_moment_scale`, `OAI_Generator_Tracial_ordered_sum_zero_of_all_mixed`, `OAI_Generator_Tracial_patchingCoefficients_append_endpoint`, `OAI_Generator_Tracial_quotient_partial_signed_tendsto`, `OAI_Generator_Tracial_quotient_residual_all_words_centered`, `OAI_Generator_Tracial_quotient_residual_word_centered`, `OAI_Generator_Tracial_quotient_residual_word_unit_right`, `OAI_Generator_Tracial_represented_four_selfAdjoint_generators`, `OAI_Generator_Tracial_signedLetter_integer`, `OAI_Generator_Tracial_signed_conjugate` and `OAI_Generator_idempotent_mem_wstar_of_gap`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration

section
-- module Solutions.OAIQ11_FG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h

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
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem subset_wstar (s : Set (H →L[ℂ] H)) : s ⊆ wstar s := by
  intro x hx
  exact StarSubalgebra.mem_sInf.mpr fun S hS => hS.2 hx

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_OperatorLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance baseNormedAlgebraRat (M : VonNeumannAlgebra H) : NormedAlgebra ℚ M.toStarSubalgebra :=
  .restrictScalars ℚ ℂ M.toStarSubalgebra

end

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

def weakOperatorBall (M : VonNeumannAlgebra H) (C : ℝ) : Set (H →WOT[ℂ] H) :=
  {T | T.toCLM ∈ M ∧ ‖T.toCLM‖ ≤ C}

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace UltrapowerBridge

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual ultraweak topology, generated by absolutely summable vector
functionals. No continuity of a chosen trace is built into this definition. -/
@[instance_reducible] def ultraweakTopology : TopologicalSpace (H →L[ℂ] H) :=
  ⨅ (ξ : ℕ → H) (η : ℕ → H) (_ : Summable (fun n => ‖ξ n‖ * ‖η n‖)),
    TopologicalSpace.induced (fun T : H →L[ℂ] H => ∑' n, inner ℂ (ξ n) (T (η n)))
      inferInstance

variable {H}

@[instance_reducible] def algebraUltraweakTopology (M : VonNeumannAlgebra H) :
    TopologicalSpace M.toStarSubalgebra :=
  TopologicalSpace.induced (fun T : M.toStarSubalgebra => (T : H →L[ℂ] H)) (ultraweakTopology H)

end UltrapowerBridge

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Operator-norm bounded trace-norm limits remain in the same ball of the algebra, without requiring a cyclic trace vector. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

def conjugateLinear (u : unitary M.toStarSubalgebra) :
    M.toStarSubalgebra →ₗ[ℂ] M.toStarSubalgebra where
  toFun a := (u : M.toStarSubalgebra) * a * star (u : M.toStarSubalgebra)
  map_add' _ _ := by simp only [mul_add, add_mul]
  map_smul' _ _ := by simp only [mul_smul_comm, smul_mul_assoc]; rfl

@[simp] theorem conjugateLinear_one (a : M.toStarSubalgebra) : conjugateLinear 1 a = a := by
  simp [conjugateLinear]

def algebraOrbit (G : Subgroup (unitary M.toStarSubalgebra)) (b : M.toStarSubalgebra) : Set M.toStarSubalgebra :=
  {a | ∃ u : G, conjugateLinear u.val b = a}

end

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/
section
open UltrapowerBridge
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- At depth n there are 2^n indices; a successor appends a binary branch. -/
def DyadicIndex : ℕ → Type
  | 0 => Unit
  | n+1 => DyadicIndex n × Bool

instance dyadicIndexFintype : (n : ℕ) → Fintype (DyadicIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd _ _ (dyadicIndexFintype n) inferInstance

instance dyadicIndexDecidableEq (n : ℕ) : DecidableEq (DyadicIndex n) := Classical.decEq _

theorem card_dyadicIndex (n : ℕ) : Fintype.card (DyadicIndex n) = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => change Fintype.card (DyadicIndex n × Bool) = _; simp [ih,pow_succ]

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CyclicPredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A concrete candidate predual: the norm-closed complex span of vector
functionals from the faithful cyclic trace representation, with completeness,
separability, and an isometric evaluation map. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Name the existing operator-norm structure to keep the norm topology
explicit through the nested dual and submodule constructions. -/
instance algebraDualNormed (M : VonNeumannAlgebra H) :
    NormedAddCommGroup (StrongDual ℂ M.toStarSubalgebra) := inferInstance

end

/-! Every functional in the constructed norm-closed vector-functional space is
weak-operator continuous on each bounded ball of the original algebra. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def ballContinuousFunctionals (M : VonNeumannAlgebra H) (C : ℝ) :
    Submodule ℂ (StrongDual ℂ M.toStarSubalgebra) where
  carrier := {f | Continuous (fun T : weakOperatorBall M C => f ⟨T.val.toCLM,T.property.1⟩)}
  zero_mem' := by exact continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := hf.const_smul c

end

/-! Recover every functional on the constructed predual from an actual algebra
element, using compact bounded balls and weak-dual Hahn--Banach separation. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem dual_norm_le_of_re_unitBall (f : StrongDual ℂ M.toStarSubalgebra) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ a : M.toStarSubalgebra,‖a‖ ≤ 1 → (f a).re ≤ C) : ‖f‖ ≤ C := by
  let r : StrongDual ℝ M.toStarSubalgebra := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ)).symm f
  have hr : ‖r‖=‖f‖ := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ)).symm.norm_map f
  rw [← hr]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro a ha
  change |(f a).re| ≤ C
  apply abs_le.mpr
  refine ⟨?_,hf a ha.le⟩
  have hn := hf (-a) (by simpa only [norm_neg] using ha.le)
  simpa only [map_neg,Complex.neg_re,neg_le] using hn

theorem weakDual_separation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {s : Set (WeakDual ℂ E)} {x : WeakDual ℂ E}
    (hs : Convex ℝ s) (hclosed : IsClosed s) (hx : x ∉ s) :
    ∃ (g : StrongDual ℂ (WeakDual ℂ E)) (u : ℝ),
      (∀ a ∈ s, (g a).re < u) ∧ u < (g x).re := by
  let : AddCommGroup (WeakDual ℂ E) := inferInstance
  let : Module ℝ (WeakDual ℂ E) := inferInstanceAs (Module ℝ (StrongDual ℂ E))
  let : Module ℂ (WeakDual ℂ E) := inferInstanceAs (Module ℂ (StrongDual ℂ E))
  let : IsScalarTower ℝ ℂ (WeakDual ℂ E) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ E))
  let : LocallyConvexSpace ℝ (WeakDual ℂ E) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ E)))
  exact RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hs hclosed hx

end

/-! Evaluation surjectivity for any subspace of bounded-unit-ball WOT-continuous
functionals. Compactness and Hahn--Banach supply actual algebra elements. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (F : Submodule ℂ (StrongDual ℂ M.toStarSubalgebra))

instance functionalSubspaceNormed : NormedAddCommGroup F := inferInstance

instance functionalSubspaceNormedSpace : NormedSpace ℂ F := inferInstance

def functionalSubspaceEvaluation (a : M.toStarSubalgebra) : StrongDual ℂ F :=
  (ContinuousLinearMap.apply ℂ ℂ a).domRestrict F

instance functionalSubspaceWeakScalarTower : IsScalarTower ℝ ℂ (WeakDual ℂ F) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (StrongDual ℂ F))

instance functionalSubspaceWeakLocallyConvex : LocallyConvexSpace ℝ (WeakDual ℂ F) :=
  inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ F)))

end

/-! Exact characterization of the cyclic predual by WOT continuity on the
unit ball. No continuity of an arbitrary given-predual evaluation is assumed
or asserted here. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_OrbitMinima
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The least-norm unitary-orbit point is scalar when the coordinate inclusion has scalar commutant. -/
section
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def subalgebraUnitaries (P : StarSubalgebra ℂ M.toStarSubalgebra) : Subgroup (unitary M.toStarSubalgebra) where
  carrier := {u | (u : M.toStarSubalgebra) ∈ P}
  one_mem' := P.one_mem
  mul_mem' hu hv := P.mul_mem hu hv
  inv_mem' hu := by
    change star _ ∈ P
    exact star_mem hu

def ambientUnitary (P : StarSubalgebra ℂ M.toStarSubalgebra) (u : unitary P) :
    subalgebraUnitaries P :=
  ⟨Unitary.map { toFun := P.subtype, map_one' := map_one _, map_mul' := map_mul _, map_star' := map_star _ } u, u.val.property⟩

end

/-! Irreducibility excludes disconnected nonzero ambient projections.
This gives the projection part of irreducibility in every nonzero corner. -/
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Supports
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The orthogonal projection onto an operator's kernel belongs to its
von Neumann algebra. This uses the actual double-commutant definition. -/
theorem kernelProjection_mem (x : M.toStarSubalgebra) :
    (x.val.ker).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro y hy
  rw [Submodule.range_starProjection]
  intro ξ hξ
  change x.val (y ξ)=0
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hy) x.val x.property
  have he := congrArg (fun t : H →L[ℂ] H => t ξ) hc
  change x.val (y ξ)=y (x.val ξ) at he
  rw [he,show x.val ξ=0 from hξ,map_zero]

end

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Follow the false child at every level of the actual coherent dyadic system. -/
def dyadicFalseIndex : (n : ℕ) → DyadicIndex n
  | 0 => ()
  | n+1 => (dyadicFalseIndex n,false)

end Tracial

end

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

def dyadicWeight (n : ℕ) (s : Finset (DyadicIndex n)) : ℝ := (s.card : ℝ)/2^n

theorem dyadicWeight_le_one (n : ℕ) (s : Finset (DyadicIndex n)) : dyadicWeight n s ≤ 1 := by
  apply (div_le_one (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
  have h : s.card ≤ 2^n := (Finset.card_le_univ s).trans_eq (card_dyadicIndex n)
  exact_mod_cast h

theorem dyadicWeight_univ (n : ℕ) : dyadicWeight n Finset.univ=1 := by
  unfold dyadicWeight
  rw [Finset.card_univ,card_dyadicIndex,Nat.cast_pow,Nat.cast_ofNat]
  exact div_self (ne_of_gt (pow_pos (by norm_num : (0 : ℝ)<2) n))

theorem dyadicWeight_children (n : ℕ) (s : Finset (DyadicIndex n)) :
    dyadicWeight (n+1) (s ×ˢ (Finset.univ : Finset Bool))=dyadicWeight n s := by
  change ((s ×ˢ (Finset.univ : Finset Bool)).card : ℝ)/2^(n+1)=(s.card : ℝ)/2^n
  rw [Finset.card_product,Finset.card_univ,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,pow_succ]
  exact mul_div_mul_right _ _ (by norm_num : (2 : ℝ)≠0)

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem dyadicWeight_le_iff (n : ℕ) (s t : Finset (DyadicIndex n)) :
    dyadicWeight n s ≤ dyadicWeight n t ↔ s.card ≤ t.card := by
  unfold dyadicWeight
  rw [div_le_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ)<2) n)]
  exact Nat.cast_le

end

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {ι : Type*}
  [Fintype ι]

theorem exists_disjoint_card (s t : Finset ι) (h : s.card+t.card ≤ Fintype.card ι) :
    ∃ u : Finset ι, Disjoint s u ∧ u.card=t.card := by
  classical
  have hc : t.card ≤ (Finset.univ \ s).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ s),Finset.card_univ]
    omega
  obtain ⟨u,hu,huc⟩ := Finset.exists_subset_card_eq hc
  refine ⟨u,Finset.disjoint_left.mpr ?_,huc⟩
  intro i hi hui
  exact (Finset.mem_sdiff.mp (hu hui)).2 hi

end EquivalentPartition
end

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem eq_of_all_dyadic_errors (a b : ℝ) (h : ∀ n : ℕ, |a-b| ≤ 2/2^n) : a=b := by
  by_contra hab
  have hp : 0 < |a-b|/2 := div_pos (abs_pos.mpr (sub_ne_zero.mpr hab)) (by norm_num)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hh := h n
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring] at hh
  linarith

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- A subset of the n-th reference partition with weight in [c,c+2^(-n)]. -/
theorem exists_dyadicWeight_upper (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    ∃ s : Finset (DyadicIndex n), c ≤ dyadicWeight n s ∧ dyadicWeight n s ≤ c+1/2^n := by
  classical
  have hn : (0 : ℝ)<2^n := pow_pos (by norm_num) n
  have hk : Nat.ceil (c*2^n) ≤ Fintype.card (DyadicIndex n) := by
    rw [card_dyadicIndex,Nat.ceil_le]
    push_cast
    nlinarith
  obtain ⟨s,_,hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (DyadicIndex n))) (n := Nat.ceil (c*2^n))
    (by simpa only [Finset.card_univ] using hk)
  refine ⟨s,?_,?_⟩
  · change c ≤ (s.card : ℝ)/2^n
    rw [hs,le_div_iff₀ hn]
    exact Nat.le_ceil _
  · change (s.card : ℝ)/2^n ≤ c+1/2^n
    rw [hs,div_le_iff₀ hn]
    have h := (Nat.ceil_lt_add_one (mul_nonneg hc hn.le)).le
    calc (Nat.ceil (c*2^n) : ℝ) ≤ c*2^n+1 := h
         _ = (c+1/2^n)*2^n := by field_simp

theorem le_of_all_dyadic_errors (a b : ℝ) (h : ∀ n : ℕ, a ≤ b+1/2^n) : a ≤ b := by
  by_contra hab
  have hp : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (1/2 : ℝ)<1)
  rw [one_div_pow] at hn
  have hh := h n
  linarith

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Exponential
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! The homogeneous expansion of an ordered exponential product,
with factorial weights and multiplication order retained. -/
noncomputable section
open scoped BigOperators
section Algebra
variable {R : Type*} [Ring R] [Algebra ℝ R]

def exponentialDegree : List R → ℕ → R
  | [], d => if d = 0 then 1 else 0
  | a :: as, d => ∑ k ∈ Finset.range (d + 1),
      ((k.factorial : ℝ)⁻¹ • a ^ k) * exponentialDegree as (d - k)

@[simp] theorem exponentialDegree_zero (xs : List R) : exponentialDegree xs 0 = 1 := by
  induction xs with
  | nil => simp [exponentialDegree]
  | cons a as ih => simp [exponentialDegree, ih]

@[simp] theorem exponentialDegree_one (xs : List R) : exponentialDegree xs 1 = xs.sum := by
  induction xs with
  | nil => simp [exponentialDegree]
  | cons a as ih =>
    simp [exponentialDegree, Finset.sum_range_succ, ih, add_comm]

end Algebra

end

/-! Summation of homogeneous-degree remainder bounds, given the expansion and its coefficient estimates. -/

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FreeWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! Distinct nonidentity off-diagonal prefix ratios, distinguished by abelian exponent coordinates. Labels start at zero. -/

def exponentCoordinate (i : ℕ) : FreeGroup ℕ →* Multiplicative ℤ :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (if i = j then 1 else 0)

/-! The exact multiplicity sum for prefix ratios, with labels g_(k+1) indexed by k : Fin n. -/

/-! Ordered prefix products. The element h denotes the unitary exponential of a self-adjoint operator, not its logarithm. The final letter is unperturbed. -/
variable {G : Type*} [Group G]

def prefixes : List G → List G
  | [] => []
  | s :: ss => s :: (prefixes ss).map (fun g => s * g)

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FunctionalLimits
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! A functional bounded by a Hilbert-valued linear map factors through one
inner product. The proof uses the actual range, Hahn--Banach, and Riesz. -/
namespace Tracial

section
variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem exists_inner_factor_of_bound (F : E →ₗ[ℂ] V) (φ : E →ₗ[ℂ] ℂ)
    (C : ℝ) (hb : ∀ x : E, ‖φ x‖ ≤ C*‖F x‖) :
    ∃ η : V, ∀ x : E, φ x=inner ℂ η (F x) := by
  classical
  have hfiber {x y : E} (h : F x=F y) : φ x=φ y := by
    have hb' := hb (x-y)
    rw [map_sub,map_sub,h,sub_self,norm_zero,mul_zero] at hb'
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb' (norm_nonneg _)))
  have hex (z : LinearMap.range F) : ∃ x : E, F x=z.val := z.property
  choose a ha using hex
  let L : LinearMap.range F →ₗ[ℂ] ℂ :=
    { toFun := fun z => φ (a z)
      map_add' := by
        intro z w
        calc φ (a (z+w)) = φ (a z+a w) := hfiber (by rw [ha,map_add,ha,ha]; rfl)
          _ = φ (a z)+φ (a w) := map_add φ _ _
      map_smul' := by
        intro c z
        calc φ (a (c • z)) = φ (c • a z) := hfiber (by rw [ha,map_smul,ha]; rfl)
          _ = c • φ (a z) := map_smul φ _ _ }
  have hL (x : E) : L ⟨F x,LinearMap.mem_range_self F x⟩=φ x := hfiber (ha _)
  let l : LinearMap.range F →L[ℂ] ℂ := L.mkContinuous C (fun z => by
    have h := hb (a z)
    rw [ha] at h
    exact h)
  obtain ⟨g,hg,_⟩ := exists_extension_norm_eq (LinearMap.range F) l
  refine ⟨(InnerProductSpace.toDual ℂ V).symm g,?_⟩
  intro x
  rw [InnerProductSpace.toDual_symm_apply]
  exact ((hg ⟨F x,LinearMap.mem_range_self F x⟩).trans (hL x)).symm

end

/-! Pointwise ultrafilter limits of uniformly bounded complex functionals.
Compactness is used only for scalar closed balls, with no separability premise. -/
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_bounded_functional_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (f : ι → E →L[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) :
    ∃ φ : E →L[ℂ] ℂ, ‖φ‖ ≤ C ∧
      ∀ x : E, Tendsto (fun i => f i x) (ω : Filter ι) (𝓝 (φ x)) := by
  have hex (x : E) : ∃ z : ℂ, ‖z‖ ≤ C*‖x‖ ∧
      Tendsto (fun i => f i x) (ω : Filter ι) (𝓝 z) := by
    obtain ⟨z,hz,ht⟩ := (isCompact_closedBall (0 : ℂ) (C*‖x‖)).ultrafilter_le_nhds
      (ω.map (fun i => f i x)) (by
        apply le_principal_iff.mpr
        change ∀ᶠ i in (ω : Filter ι), f i x ∈ Metric.closedBall 0 (C*‖x‖)
        exact Eventually.of_forall (fun i => by
          simpa only [Metric.mem_closedBall,dist_zero_right] using
            (f i).le_of_opNorm_le (hf i) x))
    exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz,ht⟩
  choose v hv ht using hex
  have hadd (x y : E) : v (x+y)=v x+v y := by
    apply tendsto_nhds_unique (ht (x+y))
    simpa only [map_add] using (ht x).add (ht y)
  have hsmul (c : ℂ) (x : E) : v (c • x)=c • v x := by
    apply tendsto_nhds_unique (ht (c • x))
    simpa only [map_smul,smul_eq_mul] using (ht x).const_mul c
  let φ : E →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨φ,φ.opNorm_le_bound hC hv,ht⟩

end Tracial

/-! A separable normed space has a countable family of bounded linear
functionals separating its points. All functionals are constructed by
Hahn--Banach at a countable dense family of vectors. -/

/-! Hermitian symmetrization and complex polarization for bounded functionals.
No tracial functional or finite factor is supplied to these algebraic lemmas. -/
open scoped CStarAlgebra

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialUnitaries
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Popa's extension order on actual supported partial unitaries, and its
exact L2 distance identity. -/

/-! Actual L2 limits of partial unitaries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Actual orthogonal corner unitaries from dyadic trace cuts. These supply
weakly vanishing scalar matrix coefficients for the scalar-commutant case
of Popa's coordinate nonintertwining criterion. -/
section
open Filter
open scoped Topology BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

def dyadicSign (n : ℕ) (i : DyadicIndex (n+1)) : ℂ := if i.2 then -1 else 1

end

/-! Popa 1308.3982v3, §1.5, scalar-target specialization. The sequence is
constructed from actual dyadic trace cuts in each nonzero corner; neither
nonintertwining nor Haar existence is an assumption. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PatchingWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Ordered signed mixed words in Popa 1308.3982v3, Lemma 3.2.
The L2 continuity estimate keeps the order of every coefficient. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def signedLetter (v : M.toStarSubalgebra) (s : Bool) : M.toStarSubalgebra :=
  if s then star v else v

def patchingWord (v : M.toStarSubalgebra) : List (Bool × M.toStarSubalgebra) → M.toStarSubalgebra
  | [] => 1
  | (s,x)::xs => signedLetter v s*x*patchingWord v xs

end

/-! The scalar-commutant specialization of the error-constrained chain and
Zorn step in Popa 1308.3982v3 Lemma 3.2. The internal coefficients are in F;
only the two endpoints may be 1. No local-quantization or growth assumption. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The last coefficient is an endpoint; all earlier coefficients are internal. -/
def patchingCoefficients (F : Set M.toStarSubalgebra) : List (Bool × M.toStarSubalgebra) → Prop
  | [] => True
  | [a] => a.2 ∈ F ∪ {1}
  | a::b::xs => a.2 ∈ F ∧ patchingCoefficients F (b::xs)

end

/-! The error-constrained partial unitaries stay in the prescribed algebra P,
while all word coefficients and the trace live in M. This prevents replacing
the source inclusion P subset M by the trivial inclusion M subset M. -/

/-! Finite enumeration of the actual ordered word family. Only endpoints may
be 1. The middle segments retain all signs and their precise lengths. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- All lists of length at most n over a finite alphabet. -/
def boundedLists {α : Type*} (A : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | n+1 => by
    classical
    exact insert [] ((A ×ˢ boundedLists A n).image (fun z => z.1 :: z.2))

/-- A finite alphabet of signs and coefficients. -/
def signedAlphabet (F : Finset M.toStarSubalgebra) : Finset (Bool × M.toStarSubalgebra) :=
  Finset.univ ×ˢ F

@[simp] theorem mem_signedAlphabet (F : Finset M.toStarSubalgebra)
    (a : Bool × M.toStarSubalgebra) : a ∈ signedAlphabet F ↔ a.2 ∈ F := by
  simp [signedAlphabet]

/-- The uncompressed middle coefficient between the first two patch letters.
Every coefficient here is internal to the original word. -/
def middleWordFamily (F : Finset M.toStarSubalgebra) (n : ℕ) :
    Finset (M.toStarSubalgebra × List (Bool × M.toStarSubalgebra)) := by
  classical
  exact (F ×ˢ boundedLists (signedAlphabet F) n).filter (fun z => z.2.length+2 ≤ n)

/-- Actual fixed outer coefficients needed for one-patch terms. -/
def outerWordFamily (v : M.toStarSubalgebra) (F : Finset M.toStarSubalgebra) (n : ℕ) :
    Finset M.toStarSubalgebra := by
  classical
  exact ((insert 1 F) ×ˢ boundedLists (signedAlphabet (insert 1 F)) n).image
    (fun z => z.1*patchingWord v z.2)

end

/-! The two moment bounds in Popa Lemma 3.2 equation (6), derived from
admissibility for the actual signed internal segment, including length zero. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- A_i is zero for an empty middle segment, since its sole coefficient is centered. -/
def middleMomentError (ε : ℕ → ℝ) (r : ℕ) : ℝ := if r=0 then 0 else ε r

end

/-! Actual noncommutative binary expansion in Popa Lemma 3.2, equation (1).
Each list entry retains the number of patch letters used and its ordered
operator product. There is no commuting-coefficient hypothesis. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def patchingExpansion (v w : M.toStarSubalgebra) :
    List (Bool × M.toStarSubalgebra) → List (ℕ × M.toStarSubalgebra)
  | [] => [(0,1)]
  | (s,x)::xs =>
      (patchingExpansion v w xs).map (fun z => (z.1,signedLetter v s*x*z.2)) ++
      (patchingExpansion v w xs).map (fun z => (z.1+1,signedLetter w s*x*z.2))

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PatchingBounds
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact positive tolerance recurrence used in Popa Lemma 3.2. -/
section

def patchingTolerance (δ : ℝ) : ℕ → ℝ
  | 0 => δ
  | k+1 => (2 : ℝ)^(k+2)*patchingTolerance δ k

@[simp] theorem patchingTolerance_zero (δ : ℝ) : patchingTolerance δ 0=δ := rfl
@[simp] theorem patchingTolerance_succ (δ : ℝ) (k : ℕ) :
    patchingTolerance δ (k+1)=2^(k+2)*patchingTolerance δ k := rfl

end

/-! Explicit binary masks for the existing ordered expansion. A true bit is a
patch letter. Occurrences are retained even when their operator values coincide. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def binaryMasks : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => (binaryMasks n).map (false :: ·) ++ (binaryMasks n).map (true :: ·)

def maskedWord (v w : M.toStarSubalgebra) :
    List (Bool × M.toStarSubalgebra) → List Bool → M.toStarSubalgebra
  | [], _ => 1
  | (s,x)::xs, bs =>
      signedLetter (if bs.headD false then w else v) s*x*maskedWord v w xs bs.tail

end

/-! Mask uniqueness and a deliberately coarse budget that avoids off-by-one
counts: 2^k ordinary budgets plus one exceptional budget fit epsilon_k. -/
section

def exceptionalMask (k : ℕ) : List Bool := true::(List.replicate (k-2) false++[true])

end

/-! Extract actual coefficient segments and fixed one-patch outer factors.
These lemmas apply to the source lists without assuming segment membership. -/

/-! The triangle inequality for the exact noncommutative mask expansion. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/

/-! Finite dyadic trees of actual spectral interval cuts. -/

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem kernel_invariant_of_commutes (x y : H →L[ℂ] H) (h : x*y=y*x) :
    x.ker ∈ Module.End.invtSubmodule y.toLinearMap := by
  intro ξ hξ
  change x (y ξ)=0
  have he := congrArg (fun t : H →L[ℂ] H => t ξ) h
  change x (y ξ)=y (x ξ) at he
  rw [he,show x ξ=0 from hξ,map_zero]

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem selfAdjoint_commutes_star_right {x y : M.toStarSubalgebra}
    (hx : IsSelfAdjoint x) (hxy : Commute x y) : Commute x (star y) := by
  have h := congrArg star hxy.eq
  simp only [star_mul,hx.star_eq] at h
  exact h.symm

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralApproximation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/

/-! Finite spectral approximation for an actual normal operator. -/

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def algebraInclusion (h : N ≤ M) : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra :=
  StarSubalgebra.inclusion h

end

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def traceSymmetrize (a : M.toStarSubalgebra) : M.toStarSubalgebra :=
  (2 : ℂ)⁻¹ • (a+star a)

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vonNeumann_wotClosed (M : VonNeumannAlgebra H) : WOTClosed M.toStarSubalgebra := by
  change IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ (M : Set (H →L[ℂ] H))}
  rw [← M.centralizer_centralizer]
  change IsClosed {T : H →WOT[ℂ] H |
    ∀ S ∈ Set.centralizer (M : Set (H →L[ℂ] H)),S*T.toCLM=T.toCLM*S}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro S
  apply isClosed_iInter
  intro hS
  have he : {T : H →WOT[ℂ] H | S*T.toCLM=T.toCLM*S} =
      {T : H →WOT[ℂ] H |
        (ContinuousLinearMapWOT.equiv.symm S)*T=T*(ContinuousLinearMapWOT.equiv.symm S)} := by
    ext T
    let e : (H →WOT[ℂ] H) ≃ (H →L[ℂ] H) := ContinuousLinearMapWOT.equiv
    exact e.injective.eq_iff
  rw [he]
  exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)

end Tracial

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def bicommutantStar (S : StarSubalgebra ℂ (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))

theorem bicommutantStar_coe (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    (bicommutantStar S : Set (H →L[ℂ] H))=
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  unfold bicommutantStar
  rw [StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]

def bicommutantVonNeumann (S : StarSubalgebra ℂ (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := bicommutantStar S
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (bicommutantStar S : Set (H →L[ℂ] H)))=
      (bicommutantStar S : Set (H →L[ℂ] H))
    rw [bicommutantStar_coe,Set.centralizer_centralizer_centralizer]

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarPatches
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The same ordered signed words in any star algebra, with exact transport
through bounded sequence evaluation and the actual quotient homomorphism. -/
section
open UltrapowerBridge

def algebraSignedLetter {A : Type*} [Star A] (v : A) (s : Bool) : A :=
  if s then star v else v

def algebraPatchingWord {A : Type*} [Monoid A] [Star A] (v : A) :
    List (Bool × A) → A
  | [] => 1
  | (s,x)::xs => algebraSignedLetter v s*x*algebraPatchingWord v xs

def optionalCoefficient {A : Type*} [One A] (x : ℕ → A) : Option ℕ → A
  | none => 1
  | some i => x i

end

/-! The finite-error f=1 conclusion of Popa Lemma 3.2, for the irreducible
scalar-commutant inclusion with the explicit represented-factor hypotheses. -/

/-! A countable diagonal construction with actual vanishing ordered moments.
The countable coefficients may vary with the sequence coordinate. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def indexedCoefficient (x : ℕ → ℕ → M.toStarSubalgebra) (j : ℕ) :
    Option ℕ → M.toStarSubalgebra
  | none => 1
  | some i => x i j

end

/-! Actual positive-support partial independence in the bounded-sequence
tracial quotient. Freeness is expressed by domination of atTop. -/
open Filter
open scoped Topology

/-! Exact multilinearity factors for ordered words; no factors are inverted
and signs affect only the partial-unitary letters. -/

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ResidualMoments
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Valid residual-corner identities in the actual quotient. Compression
centering requires two exact moments; global centering alone is insufficient. -/

/-! A countable family containing every original coefficient and every old
nonempty ordered signed word, with both optional endpoints retained. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
  (ω : Ultrafilter ℕ)

abbrev ResidualWordIndex := ℕ ⊕ (Option ℕ × Option ℕ × List (Bool × ℕ) × Bool)

/-! Ordered mixed words grouped at each increment letter. The intervening
old runs are actual members of the previously enumerated residual family. -/

def algebraMixedTail {A : Type*} [Monoid A] [Star A] (v w : A) (x : ℕ → A)
    (last : Option ℕ) (b s : Bool) : List (Bool × Bool × ℕ) → A
  | [] => algebraSignedLetter (if b then w else v) s * optionalCoefficient x last
  | (c,t,i)::xs => algebraSignedLetter (if c then w else v) t*x i*
      algebraMixedTail v w x last b s xs

end

/-! Cyclic endpoint correction for residual patching. Outer endpoints are
multiplied before compression, and the scalar part is handled separately. -/
section
open UltrapowerBridge Filter

def algebraWordCore {A : Type*} [Monoid A] [Star A] (v : A) (x : ℕ → A)
    (s : Bool) : List (Bool × ℕ) → A
  | [] => algebraSignedLetter v s
  | (t,i)::xs => algebraSignedLetter v t*x i*algebraWordCore v x s xs

end

/-! Countable supported family for actual residual patching, including centered
cyclic products of the two outer blocks. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
  (ω : Ultrafilter ℕ)

abbrev CyclicFamilyIndex := ℕ ⊕ (Option ℕ × Option ℕ)

end

/-! Exact preservation of every original ordered moment under orthogonal
patching, once the constructed cyclic residual family has exact moments. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_ProductWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact signed-word expansion for a product of two unitaries. A unit gap
is allowed only between equal signs; opposite signs retain a centered gap. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

def productLeft (u : A) (s : Bool) : A := if s then 1 else u
def productRight (u : A) (s : Bool) : A := if s then star u else 1

def betweenWord (v : A) (s : Bool) : List (A × Bool) → A → A
  | [], b => algebraSignedLetter v s*b
  | (d,t)::xs, b => algebraSignedLetter v s*d*betweenWord v t xs b

def productGapList (u : A) (s : Bool) : List (A × Bool) → List (Bool × A)
  | [] => []
  | (d,t)::xs => (s,productRight u s*d*productLeft u t)::productGapList u t xs

def finalWordSign (s : Bool) : List (A × Bool) → Bool
  | [] => s
  | (_,t)::xs => finalWordSign t xs

end Algebra

/-! The actual countable centered coefficients needed to expand words in UV. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
  (ω : Ultrafilter ℕ)

abbrev ProductFamilyIndex := ℕ ⊕ ((Bool × Option ℕ) ⊕ ℕ)

end

/-! Expand positive-length signed powers into individual letters. Repeated
letters have unit gaps; boundaries between powers retain centered coefficients. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

def powerBlockGaps (s : Bool) (n : ℕ) : List (A × (Bool × ℕ)) → List (A × Bool)
  | [] => List.replicate n (1,s)
  | (d,(t,k))::xs => List.replicate n (1,s) ++ (d,t)::powerBlockGaps t k xs

def powerBlockWord (v : A) (s : Bool) (n : ℕ) : List (A × (Bool × ℕ)) → A → A
  | [],b => algebraSignedLetter v s^(n+1)*b
  | (d,(t,k))::xs,b => algebraSignedLetter v s^(n+1)*d*powerBlockWord v t k xs b

/-- Magnitude is encoded as predecessor, so every resulting block has positive length. -/
def integerPowerBlock : ℤ → Bool × ℕ
  | .ofNat n => (false,n-1)
  | .negSucc n => (true,n)

def integerWord (v : unitary A) (x : ℕ → A) (n : ℤ) : List (ℕ × ℤ) → A → A
  | [],b => (↑(v^n) : A)*b
  | (i,m)::xs,b => (↑(v^n) : A)*x i*integerWord v x m xs b

end Algebra

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_QuotientRepresentation
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Complete operator-norm bounded sequences and their contractive map to the
actual quotient trace Hilbert space. This map is not asserted injective. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
  (ω : Ultrafilter ℕ)

abbrev Sequences (M : VonNeumannAlgebra H) := BoundedContinuousFunction ℕ M.toStarSubalgebra

instance sequencesIsTopologicalRing : IsTopologicalRing (Sequences M) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing (Sequences M) inferInstance

end

/-! The faithful constant embedding into the tracial quotient, with its trace and trace norm, for every ultrafilter. -/
open Filter
open scoped Topology

/-! Left multiplication by bounded representatives on the completed trace
Hilbert space. The quotient ideal, not an assumed operator action, determines
which representatives induce the same operator. -/
open Filter
open scoped Topology

/-! Faithful concrete Hilbert-space representation of the tracial quotient
star algebra. Weak operator closedness of its image is not claimed here. -/
open Filter
open scoped Topology

/-! The standard completion/continuous-linear-map structures are not new hypotheses. -/

/-! Fixed-index selection for bounded coordinate representatives. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Words
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

namespace Generator

/-! All alternating word shapes, allowing either algebra at either endpoint. -/

/-! Splitting a reduced word at its first occurrence of a specified generator. -/

/-! Noncommutative ordered row words and coefficient majorization, without commuting-row assumptions. -/
variable {R : Type*} [Semiring R]

def orderedWords : List R → ℕ → R
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | a :: as, d + 1 => a * orderedWords (a :: as) d + orderedWords as (d + 1)
termination_by xs d => (d, xs.length)

@[simp] theorem orderedWords_zero (xs : List R) : orderedWords xs 0 = 1 := by
  cases xs <;> simp [orderedWords]

@[simp] theorem orderedWords_nil (d : ℕ) : orderedWords ([] : List R) d = if d = 0 then 1 else 0 := by
  cases d <;> simp [orderedWords]

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HaarSequences
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! One constructed Haar extension retains endpoint moments, represented
norm-closed freeness, and an actual unitary sequence in the included algebra. -/

/-! Scalar expansion of same-sign gaps. Opposite-sign gaps must be centered,
so deleting a scalar gap can never cancel an entire power. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
  (ω : Ultrafilter ℕ)

def SamePowerSign (n m : ℤ) : Prop := (0 < n ∧ 0 < m) ∨ (n < 0 ∧ m < 0)

/-! Expand nonzero integer powers into signs while retaining the exact rule:
only an equal-sign gap may have a nonzero scalar part. -/

def signExponent (s : Bool) : ℤ := if s then -1 else 1

end

/-! Absorption of base-algebra unitaries, with signed scalar gap expansions. -/

section Algebra
variable {A : Type*} [Monoid A] [StarMul A]

def absorbedGapList (u : A) (s : Bool) : List (A × Bool) → List (A × Bool)
  | [] => []
  | (d,t)::xs => (productRight u s*d*productLeft u t,t)::absorbedGapList u t xs

end Algebra

/-! Successive Haar choices in algebraic star subalgebras of the tracial quotient, with freeness retained in their represented operator-norm closures. -/

/-! Free variables and prefixes with Haar endpoint properties of W and y=zW*. Coordinates are retained in the sequence data. -/
open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertProjections
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Baire continuity points from rational sublevel boundaries, without a global boundedness assumption. -/
section
open Set Filter Topology
variable {X : Type*} [TopologicalSpace X]

/-- An explicit countable intersection of open sets of continuity points. -/
def continuityCore (f : X → ℝ) : Set X :=
  ⋂ q : ℚ, (frontier {x | f x ≤ (q : ℝ)})ᶜ

end

/-! Hilbert-space projection and correlation identities. The inner product is conjugate-linear in its first argument, so `inner ℂ ξ W` represents τ(ξ* W). -/

/-! Lower semicontinuity from a continuous family dense in each projected subspace. -/
open Set Filter Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalDimension
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/
namespace Tracial

/-! Continuity of the constructed dimension on arbitrary increasing projection
nets. Compatible sequential embeddings are proved first; dimension approximation
then constructs a countable subfamily with the same projection supremum. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- Every countable family in a directed preorder has an increasing majorant
above a specified index. This is not countable cofinality of the preorder. -/
theorem exists_monotone_dominating_from
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] (f : ℕ → I) (i : I) :
    ∃ a : ℕ → I, Monotone a ∧ (∀ n, f n ≤ a n) ∧ (∀ n, i ≤ a n) := by
  classical
  let upper (x y : I) := (exists_ge_ge x y).choose
  have hl (x y : I) : x ≤ upper x y := (exists_ge_ge x y).choose_spec.1
  have hr (x y : I) : y ≤ upper x y := (exists_ge_ge x y).choose_spec.2
  let a : ℕ → I := Nat.rec (upper i (f 0)) (fun n j => upper j (f (n+1)))
  have ha : Monotone a := monotone_nat_of_le_succ (fun n => hl (a n) (f (n+1)))
  refine ⟨a,ha,?_,fun n => (hl i (f 0)).trans (ha (Nat.zero_le n))⟩
  intro n
  cases n with
  | zero => exact hr i (f 0)
  | succ n => exact hr (a n) (f (n+1))

end Tracial

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem exists_unit_vector_of_unit_ne_zero (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ ξ : H, ‖ξ‖=1 := by
  classical
  have hne : ∃ ξ : H, ξ≠0 := by
    by_contra h
    push Not at h
    apply hunit
    apply Subtype.ext
    ext ξ
    exact h ξ
  obtain ⟨ξ,hξ⟩ := hne
  refine ⟨(‖ξ‖⁻¹ : ℂ) • ξ,?_⟩
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg ξ),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]

end

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LongWords
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/
section
open scoped BigOperators
local notation "G" => FreeGroup ℕ
local notation "F" => FreeGroup G
local instance instDecidableEqFreeGroupNat_solutions_1 : DecidableEq G := Classical.decEq _
local instance instDecidableEqFreeGroupNat_solutions_2 : DecidableEq F := Classical.decEq _

end

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/

/-! The exact finite free basis and its injective realization in a countable free basis. -/

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MonotoneTrace
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Bounded positive monotone nets have actual least upper bounds in M.
Every displayed vector-trace bound passes to the constructed bound. -/

/-! Absolute values in the represented algebra, with ambient order bounds
and the actual trace two-norm. -/

/-! The bounded monotone transform a ↦ 1 - (1+a)⁻¹ of positive operators.
Its bounds prepare a construction of decreasing order majorants from small
trace tails. No tail majorant or predual continuity is asserted here. -/
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveResolvent (a : A) : A := cfc (fun t : ℝ => 1 - (1 + t)⁻¹) a

end

/-! Decreasing positive order majorants for positive contractions with
summable trace. The finite-tail resolvents and their least upper bounds are
constructed in the actual algebra. -/
open Filter
open scoped Topology BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PredualOrder
attribute [-instance] _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! Operator norm geometry for the original existential Banach-predual gap.
These statements use only concrete Hilbert operators. They do not identify
any predual or prove trace-orbit separability. -/

/-! Bounded self-adjoint sets are weak-star compact for the actual Banach
predual isometry. No predual uniqueness or WOT compatibility is assumed. -/

/-! Positive operator balls are compact in the weak-star topology of the
given Banach predual. The isometry is not assumed weak-operator continuous. -/

/-! Closed and compact order intervals for the given Banach predual.
All inequalities are the concrete operator Loewner order. -/

/-! Monotone order limits in the algebra converge for the actual given
Banach predual. Greatest/least bounds are tested only against members of S,
not against all ambient operators. -/

/-! The actual given predual embeds isometrically into the norm dual of S.
Conjugation accounts for the conjugate-linear predual isometry. These
functionals preserve monotone order limits. No canonical-predual membership
or weak-operator continuity is assumed. -/
section
open Filter
open scoped Topology ComplexConjugate
variable {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- Evaluation by x, made complex-linear in the algebra argument. -/
def predualFunctional (x : X) : StrongDual ℂ S :=
  LinearMap.mkContinuous
    { toFun := fun a => conj (e.symm a x)
      map_add' := by intros; simp
      map_smul' := by
        intro c a
        rw [e.symm.map_smulₛₗ]
        simp }
    ‖x‖ (by
      intro a
      change ‖conj (e.symm a x)‖ ≤ ‖x‖ * ‖a‖
      simp only [Complex.norm_conj]
      exact ((e.symm a).le_opNorm x).trans_eq (by rw [e.symm.norm_map, mul_comm]))

@[simp] theorem predualFunctional_apply (x : X) (a : S) :
    predualFunctional S e x a = conj (e.symm a x) := rfl

theorem predualFunctional_norm (x : X) : ‖predualFunctional S e x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (predualFunctional S e x).opNorm_le_bound (norm_nonneg x)
    intro a
    rw [predualFunctional_apply, Complex.norm_conj]
    exact ((e.symm a).le_opNorm x).trans_eq (by rw [e.symm.norm_map, mul_comm])
  · obtain ⟨g, hg, hx⟩ := exists_dual_vector'' ℂ x
    calc
      ‖x‖ = ‖predualFunctional S e x (e g)‖ := by simp [hx]
      _ ≤ ‖predualFunctional S e x‖ * ‖e g‖ := (predualFunctional S e x).le_opNorm _
      _ ≤ ‖predualFunctional S e x‖ := by
        simpa only [e.norm_map, mul_one] using
          mul_le_mul_of_nonneg_left hg (norm_nonneg (predualFunctional S e x))

/-- A conjugate-linear isometric embedding of the actual given predual. -/
def predualFunctionalIsometry : X →ₗᵢ⋆[ℂ] StrongDual ℂ S where
  toFun := predualFunctional S e
  map_add' x y := by ext a; simp
  map_smul' c x := by ext a; simp
  norm_map' := predualFunctional_norm S e

end

/-! An arbitrary net squeezed into shrinking operator order intervals
converges in the topology of the given Banach predual. The net itself need
not be monotone. No normal-functional decomposition is used. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PredualRange
attribute [-instance] _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator

/-! An actual separable Banach predual for the constructed matrix-generated
factor. The existential convention is exactly Generator.HasSeparablePredual. -/

/-! Separability of the actual cyclic predual implies separability of the
trace-vector orbit. This does not identify an arbitrary given Banach predual
with the cyclic predual. -/

/-! The given predual as a closed separating subspace of the algebra norm dual, with its evaluation duality. -/
section
open scoped ComplexConjugate
variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (S : StarSubalgebra ℂ (H →L[ℂ] H))
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] S)

/-- Keep the norm topology explicit through the nested dual construction. -/
instance predualAlgebraDualNormed : NormedAddCommGroup (StrongDual ℂ S) := inferInstance

def predualFunctionals : Submodule ℂ (StrongDual ℂ S) :=
  (predualFunctionalIsometry S e).toLinearMap.range

instance predualFunctionals_normed : NormedAddCommGroup (predualFunctionals S e) := inferInstance

instance predualFunctionals_normedSpace : NormedSpace ℂ (predualFunctionals S e) := inferInstance

end

/-! Hahn–Banach comparison of preduals from normal-functional membership and evaluation surjectivity. -/

/-! Conditional comparison with the constructed cyclic predual. Membership
of the given-predual evaluations in that space is an explicit unproved input;
it is not obtained merely from their order-limit convergence. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Algebraic type copy indexed by the original factor hypotheses. -/
def TraceFreePreHilbert
(_hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
(_hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
(_hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
(_hunit : (1 : M.toStarSubalgebra) ≠ 0)
    : Type _ := M.toStarSubalgebra

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit

instance traceFreePreHilbertRing : Ring E := inferInstanceAs (Ring M.toStarSubalgebra)
instance traceFreePreHilbertAlgebra : Algebra ℂ E :=
  inferInstanceAs (Algebra ℂ M.toStarSubalgebra)
instance traceFreePreHilbertStarRing : StarRing E :=
  inferInstanceAs (StarRing M.toStarSubalgebra)

/-- Algebraic identification only: it does not identify the two norms. -/
def traceFreeCopy : M.toStarSubalgebra ≃⋆ₐ[ℂ] E :=
  _root_.StarAlgEquiv.refl ℂ M.toStarSubalgebra

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators

end Generator.Tracial

end

end OAI
end


