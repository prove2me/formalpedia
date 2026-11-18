-- Prove2me | Definitions.Def_OAIQ368Chrom027
-- name    : OAIQ368Chrom027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:24:49.699571+00:00
-- url     : https://prove2.me/theorems/33f94f34-60bc-4cc2-9d76-4789b4d53f8e
-- title:
--   Definitions bundle OAIQ368Chrom027 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 113 declarations of OpenAI's Lean: 50 definitions and 63 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.tensorSeparationSeries`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.unitalNatB`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.unitalNatS`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.unitalSeparationSeries`, `OAI.ElementaryPositivity.RawShuffle.ShuffleFiltered`, `OAI.ElementaryPositivity.RawShuffle.SlopeColumnGrid`, `OAI.ElementaryPositivity.RawShuffle.SlopeSplit`, `OAI.ElementaryPositivity.RawShuffle.SlopeWeight`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.polynomialOnLeft`, `OAI.ElementaryPositivity.RawShuffle.bothTaylorB`, `OAI.ElementaryPositivity.RawShuffle.braidCoeffTensorB`, `OAI.ElementaryPositivity.RawShuffle.braidCoeffTensorBN`, `OAI.ElementaryPositivity.RawShuffle.braidTensorCommRing`, `OAI.ElementaryPositivity.RawShuffle.braidTensorNUSemiring`, `OAI.ElementaryPositivity.RawShuffle.castBTensor`, `OAI.ElementaryPositivity.RawShuffle.cellLeadingB`, `OAI.ElementaryPositivity.RawShuffle.clearBTensorS`, `OAI.ElementaryPositivity.RawShuffle.clearingTensorRing`, `OAI.ElementaryPositivity.RawShuffle.colTaylorFourAlg`, `OAI.ElementaryPositivity.RawShuffle.colTaylorFourRing`, `OAI.ElementaryPositivity.RawShuffle.colTaylorTensorAlg`, `OAI.ElementaryPositivity.RawShuffle.colTaylorTensorRing`, `OAI.ElementaryPositivity.RawShuffle.cutShapeDimensionEquiv`, `OAI.ElementaryPositivity.RawShuffle.cutUnivRealization`, `OAI.ElementaryPositivity.RawShuffle.firstColumn`, `OAI.ElementaryPositivity.RawShuffle.firstColumnVars`, `OAI.ElementaryPositivity.RawShuffle.fourBAlgebra`, `OAI.ElementaryPositivity.RawShuffle.fourCrossPolynomial`, `OAI.ElementaryPositivity.RawShuffle.fourCrossTensor`, `OAI.ElementaryPositivity.RawShuffle.fourInterchange`, `OAI.ElementaryPositivity.RawShuffle.fourInterchangeB`, `OAI.ElementaryPositivity.RawShuffle.fourQuotient`, `OAI.ElementaryPositivity.RawShuffle.fourUnitalFiltration`, `OAI.ElementaryPositivity.RawShuffle.gradeB`, `OAI.ElementaryPositivity.RawShuffle.gridTensorBAlgebra`, `OAI.ElementaryPositivity.RawShuffle.gridTensorBCommRing`, `OAI.ElementaryPositivity.RawShuffle.secondColumn`, `OAI.ElementaryPositivity.RawShuffle.secondColumnVars`, `OAI.ElementaryPositivity.RawShuffle.shuffleTensorBUnit`, `OAI.ElementaryPositivity.RawShuffle.signedCellMultiplyB` and 10 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_GradedBuilders`, `Chromatic_GradedAlgebra_Product`, `Chromatic_Histories_ShuffleLeafFiltration`, `Chromatic_QuantumTorus_ProductUnitFiltration`, `Chromatic_Shuffle_AllPairDiagonal`, `Chromatic_Shuffle_BothTaylorB`, `Chromatic_Shuffle_CellLeadingSum`, `Chromatic_Shuffle_CellVars`, `Chromatic_Shuffle_ClearedSeparationB`, `Chromatic_Shuffle_ClearingKernel`, `Chromatic_Shuffle_ColumnTaylor`, `Chromatic_Shuffle_ComponentB`, `Chromatic_Shuffle_DegreeIdeals`, `Chromatic_Shuffle_FourBraiding`, `Chromatic_Shuffle_GradeBInternal`, `Chromatic_Shuffle_GridQuotient`, `Chromatic_Shuffle_GridShapeFiltration`, `Chromatic_Shuffle_HNExpansion`, `Chromatic_Shuffle_Interaction`, `Chromatic_Shuffle_ManyBlockDiagonal`, `Chromatic_Shuffle_Restriction`, `Chromatic_Shuffle_RestrictionB`, `Chromatic_Shuffle_ReynoldsS`, `Chromatic_Shuffle_SeparationHomogeneity`, `Chromatic_Shuffle_ShuffleUnits`, `Chromatic_Shuffle_SignedCoproductGridGrade`, `Chromatic_Shuffle_SignedTensorGradeProduct`, `Chromatic_Shuffle_SlopeGridSum`, `Chromatic_Shuffle_SymmetricSpace`, `Chromatic_Shuffle_TensorColumnSeriesFiltration`, `Chromatic_Shuffle_TwoTargetFiltration`, `Chromatic_Shuffle_UnitalFiltration`, `Chromatic_Shuffle_UnitalGradeAlgebra`, `Chromatic_Shuffle_UnitalShuffleCoproduct`, `Chromatic_Walls_BraidingFiltration`, `Chromatic_Walls_FourCellFactorization`, `Chromatic_Walls_ShuffleFiltration`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom029`, `OAIQ368Chrom032`, `OAIQ368Chrom036` and `OAIQ368Chrom037`; the statements `OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourGrid_taylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_cross`, `OAI.ElementaryPositivity.RawShuffle.fourTaylor_column_product` and `OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation`; the proofs of `OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourGrid_taylor_factor`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_cross`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second`, `OAI.ElementaryPositivity.RawShuffle.fourTaylor_column_product`, `OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation`, `OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective`, `OAI.ElementaryPositivity.RawShuffle.slopeStringCoefficient_bounds` and `OAI.ElementaryPositivity.RawShuffle.stringPBWBasis_component`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom023

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_GradedBuilders
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity

@[instance_reducible]
noncomputable def gradedAlgebraOfBilinear {J R : Type*} [AddMonoid J] [CommSemiring R]
    {A : J → Type*} [∀ j,AddCommMonoid (A j)] [∀ j,Module R (A j)]
    [DirectSum.GSemiring A]
    (hl : ∀ (r : R) (x y : GradedMonoid A),(r•x)*y=r•(x*y))
    (hr : ∀ (r : R) (x y : GradedMonoid A),x*(r•y)=r•(x*y)) :
    DirectSum.GAlgebra R A where
  toFun := (LinearMap.toSpanSingleton R (A 0) GradedMonoid.GOne.one).toAddMonoidHom
  map_one := one_smul R _
  map_mul r s := by
    change (r*s) • (1 : GradedMonoid A) = (r • (1 : GradedMonoid A)) * (s • (1 : GradedMonoid A))
    rw [hl,hr,one_mul,smul_smul]
  commutes r x := by
    change (r • (1 : GradedMonoid A))*x=x*(r • (1 : GradedMonoid A))
    rw [hl,hr,one_mul,mul_one]
  smul_def r x := by
    change r•x=(r • (1 : GradedMonoid A))*x
    rw [hl,one_mul]

end ElementaryPositivity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SymmetricSpace
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientCommRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma translation_add {α : Type*} (t s : ℚ) (p : MvPolynomial α ℚ) :
    translation t (translation s p) = translation (t+s) p := by
  have h : (translation (α := α) t).comp (translation s) = translation (t+s) := by
    ext i; simp [map_add] <;> ring
  exact DFunLike.congr_fun h p

omit [Fintype I] [DecidableEq I] in
lemma translationS_add (d : I → ℕ) (t s : ℚ) (f : S d) :
    translationS d t (translationS d s f) = translationS d (t+s) f := by
  apply Subtype.ext
  exact translation_add t s f.val

lemma translationB_add (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ)
    (t s : ℚ) (f : B a μ d) :
    translationB a μ d t (translationB a μ d s f) = translationB a μ d (t+s) f := by
  induction f using Submodule.Quotient.induction_on with
  | H f => exact congrArg (destabilizingSpace a μ d).mkQ (translationS_add d t s f)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ReynoldsS
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlgebra
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.componentB_idempotent _root_.OAI.ElementaryPositivity.RawShuffle.componentB_mk _root_.OAI.ElementaryPositivity.RawShuffle.componentS_val _root_.OAI.ElementaryPositivity.RawShuffle.cutRealizationEquiv_left _root_.OAI.ElementaryPositivity.RawShuffle.cutRealizationEquiv_right _root_.OAI.ElementaryPositivity.RawShuffle.degreeZeroB_mk _root_.OAI.ElementaryPositivity.RawShuffle.dimensionCast_trans _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.fourValue_tmul _root_.OAI.ElementaryPositivity.RawShuffle.labeledPolynomial_algebraMap _root_.OAI.ElementaryPositivity.RawShuffle.map_taylorS _root_.OAI.ElementaryPositivity.RawShuffle.map_taylorSValue _root_.OAI.ElementaryPositivity.RawShuffle.quotientAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.relativeCoeffB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylorB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.relativeTaylor_tmul _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.restrictionB_mk _root_.OAI.ElementaryPositivity.RawShuffle.separateFour_fourValue _root_.OAI.ElementaryPositivity.RawShuffle.separateFour_product _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleB_mk _root_.OAI.ElementaryPositivity.RawShuffle.shufflePolynomial_zero_left _root_.OAI.ElementaryPositivity.RawShuffle.shufflePolynomial_zero_right _root_.OAI.ElementaryPositivity.RawShuffle.shuffleTensorLinear_tmul _root_.OAI.ElementaryPositivity.RawShuffle.targetValueAt_apply _root_.OAI.ElementaryPositivity.RawShuffle.taylorB_mk _root_.OAI.ElementaryPositivity.RawShuffle.tensorValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.tensorValue_crossTensor _root_.OAI.ElementaryPositivity.RawShuffle.twoTargetTransfer_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma restrictTensor_independent {d e : I → ℕ} (A B : Cut d e) (f : S (d+e)) :
    restrictTensor A f = restrictTensor B f := by
  apply tensorValue_injective
  rw [tensorValue_restrictTensor,tensorValue_restrictTensor]
  apply rename_injective (cutSplit B) (cutSplit B).injective
  rw [split_symmetric_independent]
  simp only [rename_rename]
  simp

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellVars
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*}

variable [Fintype I] [DecidableEq I]

lemma fourValue_injective (d₁ e₁ d₂ e₂ : I → ℕ) :
    Function.Injective (fourValue d₁ e₁ d₂ e₂) :=
  Function.LeftInverse.injective (separateFour_fourValue d₁ e₁ d₂ e₂)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_Product
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.restrictionB_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleB_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

lemma onSlopeOrZero_of_mass (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (h : mass η d = θ * mass c d) : OnSlopeOrZero c η θ d := by
  by_cases hd : d=0
  · exact Or.inl hd
  · exact Or.inr ((div_eq_iff (mass_pos c hc d hd).ne').mpr h)

lemma high_mass_destabilizes (c η : I → ℝ) (hc : ∀ i,0 < c i) (d e : I → ℕ)
    (h : mass η d > slope c η (d+e) * mass c d) :
    d≠0 ∧ e≠0 ∧ slope c η d > slope c η (d+e) := by
  have hd : d≠0 := by intro hh; simp [hh] at h
  have he : e≠0 := by
    intro hh
    rw [hh,add_zero,mass_eq c η hc d] at h
    exact lt_irrefl _ h
  exact ⟨hd,he,(lt_div_iff₀ (mass_pos c hc d hd)).mpr h⟩

def CellsOnSlope (c η : I → ℝ) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) : Prop :=
  OnSlopeOrZero c η θ d₁ ∧ OnSlopeOrZero c η θ e₁ ∧
    OnSlopeOrZero c η θ d₂ ∧ OnSlopeOrZero c η θ e₂

theorem offSlope_destabilizes (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (ht : slope c η (d₁+e₁) = slope c η (d₂+e₂))
    (hs : slope c η (d₁+d₂) = slope c η (d₁+e₁))
    (hoff : ¬ CellsOnSlope c η (slope c η (d₁+e₁)) d₁ e₁ d₂ e₂) :
    (d₁≠0 ∧ e₁≠0 ∧ slope c η d₁ > slope c η (d₁+e₁)) ∨
    (d₂≠0 ∧ e₂≠0 ∧ slope c η d₂ > slope c η (d₂+e₂)) := by
  let θ := slope c η (d₁+e₁)
  by_cases h₁ : mass η d₁ > θ * mass c d₁
  · exact Or.inl (high_mass_destabilizes c η hc d₁ e₁ h₁)
  by_cases h₂ : mass η d₂ > θ * mass c d₂
  · exact Or.inr (high_mass_destabilizes c η hc d₂ e₂ (by simpa only [θ,ht] using h₂))
  have hsrc : mass η d₁ + mass η d₂ = θ * (mass c d₁ + mass c d₂) := by
    have h := mass_eq c η hc (d₁+d₂)
    rwa [mass_add,mass_add,hs] at h
  have htar₁ : mass η d₁ + mass η e₁ = θ * (mass c d₁ + mass c e₁) := by
    have h := mass_eq c η hc (d₁+e₁)
    rwa [mass_add,mass_add] at h
  have htar₂ : mass η d₂ + mass η e₂ = θ * (mass c d₂ + mass c e₂) := by
    have h := mass_eq c η hc (d₂+e₂)
    rwa [mass_add,mass_add,← ht] at h
  have hd₁ : mass η d₁ = θ * mass c d₁ := by nlinarith
  have hd₂ : mass η d₂ = θ * mass c d₂ := by nlinarith
  have he₁ : mass η e₁ = θ * mass c e₁ := by nlinarith
  have he₂ : mass η e₂ = θ * mass c e₂ := by nlinarith
  exact (hoff ⟨onSlopeOrZero_of_mass c η hc θ d₁ hd₁,
    onSlopeOrZero_of_mass c η hc θ e₁ he₁,onSlopeOrZero_of_mass c η hc θ d₂ hd₂,
    onSlopeOrZero_of_mass c η hc θ e₂ he₂⟩).elim

end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

lemma quotient_cellTransfer_offSlope (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (ht : slope c η (d₁+e₁) = slope c η (d₂+e₂))
    (hs : slope c η (d₁+d₂) = slope c η (d₁+e₁))
    (hoff : ¬ CellsOnSlope c η (slope c η (d₁+e₁)) d₁ e₁ d₂ e₂)
    (p : MvPolynomial (CellVars d₁ e₁ ⊕ CellVars d₂ e₂) ℚ) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂) (cellTransfer a d₁ e₁ d₂ e₂ p) = 0 :=
  quotient_cellTransfer_zero a (slope c η) _ _ _ _ (offSlope_destabilizes c η hc _ _ _ _ ht hs hoff) p

omit [(index : I) → Fintype (A index)] in
lemma quotient_gridShapeTensor_offSlope (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e α β : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (u : CutShape (left p)) (v : CutShape (right p))
    (ht : slope c η α = slope c η β) (hs : slope c η d = slope c η α)
    (hoff : ¬ CellsOnSlope c η (slope c η α)
      (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)) :
    quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v) = 0 := by
  unfold gridShapeTensor
  apply quotientTensor_cast_zero
  by_cases hsum : (fun i=>(u i).val) + (fun i=>(v i).val) = d
  · apply quotient_cellTransfer_offSlope a c η hc
    · rw [(shape_add_complement u).trans (realization_card R),
        (shape_add_complement v).trans (realization_card T)]
      exact ht
    · rw [hsum,(shape_add_complement u).trans (realization_card R)]
      exact hs
    · rwa [(shape_add_complement u).trans (realization_card R)]
  · rw [fourGridPolynomial_zero_of_source_mismatch a f g _ _ _ _ hsum,map_zero,map_zero]

omit [(index : I) → Fintype (A index)] in
theorem quotient_gridTensor_sameSlope_support (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) {d e α β : I → ℕ} (f : S d) (g : S e)
    {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization α (left p)) (T : Realization β (right p))
    (ht : slope c η α = slope c η β) (hs : slope c η d = slope c η α) :
    quotientTensor a (slope c η) α β (gridTensor a f g p R T) =
      ∑ u : CutShape (left p), ∑ v : CutShape (right p),
        if CellsOnSlope c η (slope c η α)
          (fun i=>(u i).val) (shapeComplement u) (fun i=>(v i).val) (shapeComplement v)
        then quotientTensor a (slope c η) α β (gridShapeTensor a f g p R T u v) else 0 := by
  classical
  simp only [gridTensor,map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs with hon
  · rfl
  · exact quotient_gridShapeTensor_offSlope a c η hc f g p R T u v ht hs hon

theorem cleared_restriction_sameSlope_support (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) {d e α β : I → ℕ} (h : d+e=α+β)
    (f : S d) (g : S e) {s : Pack (A:=A)} (R : Realization (α+β) s) (u : Cut α β)
    (ht : slope c η α = slope c η β) (hs : slope c η d = slope c η α) :
    quotientTensor a (slope c η) α β (crossTensor α β) *
      quotientTensor a (slope c η) α β
        (restrictTensor u (castS h (shufflePolynomial a f g))) =
    crossSign α β •
      ∑ x : CutShape (left (cutRealizationEquiv R u).val),
        ∑ y : CutShape (right (cutRealizationEquiv R u).val),
          if CellsOnSlope c η (slope c η α)
            (fun i=>(x i).val) (shapeComplement x) (fun i=>(y i).val) (shapeComplement y)
          then quotientTensor a (slope c η) α β
            (gridShapeTensor a f g (cutRealizationEquiv R u).val
              (leftRealization R u) (rightRealization R u) x y) else 0 := by
  rw [← map_mul,cleared_restrictTensor a h f g R u,map_smul]
  rw [quotient_gridTensor_sameSlope_support a c η hc f g _ _ _ ht hs]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_RestrictionB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

namespace SplitTree

omit [DecidableEq I] in
lemma dim_ne_zero {T : SplitTree I} {c η : I → ℝ} {θ : ℝ} (h : T.OnSlope c η θ) :
    T.dim ≠ 0 := by
  induction T with
  | leaf d => exact h.1
  | node l r ihl ihr => exact add_ne_zero_left _ _ (ihl h.1)

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ComponentB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def gradeB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) : Submodule ℚ (B a μ d) := LinearMap.range (componentB a μ d k)

lemma mem_gradeB_iff (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : B a μ d) :
    f ∈ gradeB a μ d k ↔ componentB a μ d k f=f := by
  constructor
  · rintro ⟨g,rfl⟩
    exact componentB_idempotent a μ d k g
  · intro h
    exact ⟨f,h⟩

lemma componentB_on_grade (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k l : ℤ) (f : B a μ d) (hf : f∈gradeB a μ d l) :
    componentB a μ d k f = if k=l then f else 0 := by
  obtain ⟨g,rfl⟩ := hf
  exact componentB_componentB a μ d k l g

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GradeBInternal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma gradeB_homogeneous_representative (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : B a μ d) (hf : f∈gradeB a μ d k) :
    ∃ g : S d, g.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k ∧
      (destabilizingSpace a μ d).mkQ g=f := by
  obtain ⟨x,rfl⟩ := hf
  obtain ⟨g,rfl⟩ := (destabilizingSpace a μ d).mkQ_surjective x
  exact ⟨componentS d k g,componentS_homogeneous d k g,rfl⟩

theorem shuffleB_graded (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (m n : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (g : B a (SlopeArithmetic.slope c η) e)
    (hf : f∈gradeB a (SlopeArithmetic.slope c η) d m)
    (hg : g∈gradeB a (SlopeArithmetic.slope c η) e n) :
    shuffleB a c η hc d e hs f g ∈
      gradeB a (SlopeArithmetic.slope c η) (d+e) (m+n-eulerForm a d e) := by
  obtain ⟨f,hfp,rfl⟩ := gradeB_homogeneous_representative a _ d m f hf
  obtain ⟨g,hgp,rfl⟩ := gradeB_homogeneous_representative a _ e n g hg
  rw [shuffleB_mk,mem_gradeB_iff,componentB_mk,
    componentS_of_homogeneous _ _ (shufflePolynomial_homogeneous a f g hfp hgp),ite_eq_left rfl]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Interaction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.separationCoefficient_apply _root_.OAI.ElementaryPositivity.RawShuffle.castB_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castB_trans _root_.OAI.ElementaryPositivity.RawShuffle.castS_rfl _root_.OAI.ElementaryPositivity.RawShuffle.castS_trans _root_.OAI.ElementaryPositivity.RawShuffle.degreeZeroB_mk _root_.OAI.ElementaryPositivity.RawShuffle.fourValueAlg_apply _root_.OAI.ElementaryPositivity.RawShuffle.relativeCoeffB_tmul _root_.OAI.ElementaryPositivity.RawShuffle.restrictionBUnit_mk _root_.OAI.ElementaryPositivity.RawShuffle.shuffleBUnit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma sourceFiltration_antitone (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) : Antitone (sourceFiltration a c η hc θ d) := by
  intro W V h f hf T hT hs hd k z hw
  exact hf T hT hs hd k z (lt_of_lt_of_le hw h)

lemma coeff_zero_toMvPolynomial {R α : Type*} [CommRing R] (i : α) (p : Polynomial R) :
    (Polynomial.toMvPolynomial i p).coeff 0=p.coeff 0 := by
  change MvPolynomial.constantCoeff (Polynomial.toMvPolynomial i p)=p.coeff 0
  rw [← MvPolynomial.eval_zero']
  have h := RingHom.congr_fun (MvPolynomial.eval_comp_toMvPolynomial (fun _ : α=> (0:R)) i) p
  simpa [Polynomial.coeff_zero_eq_eval_zero] using h

lemma restrictionTest_leaf_zero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (hs : (SplitTree.leaf d).OnSlope c η θ)
    (k : ℤ) (f : B a (SlopeArithmetic.slope c η) d) :
    restrictionTest a c η hc θ (.leaf d) hs rfl k 0 f = componentB a (SlopeArithmetic.slope c η) d k f := by
  change componentB a (SlopeArithmetic.slope c η) d k
    ((Polynomial.toMvPolynomial () (taylorB a (SlopeArithmetic.slope c η) d f)).coeff 0) = _
  rw [coeff_zero_toMvPolynomial,taylorB_coeff_zero]

end ElementaryPositivity.RawShuffle

namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity ElementaryPositivity.SeparatedSymmetry ElementaryPositivity.ShufflePolynomiality
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma reynoldsS_homogeneous (d : I → ℕ) (p : MvPolynomial (Σi,Fin (d i)) ℚ)
    (k : ℤ) (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) :
    (reynoldsS d p).val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k := by
  change (average (packAction (fun i=>Fin (d i))) p).IsWeightedHomogeneous _ _
  rw [average_apply]
  apply (weightedHomogeneousSubmodule ℚ (fun _=>(1:ℤ)) k).smul_mem
  exact IsWeightedHomogeneous.sum _ _ _ (fun σ _=>constantWeight_rename _ _ hp)

lemma separateTensor_product_any (d e : I → ℕ)
    (f : MvPolynomial (Σi,Fin (d i)) ℚ) (g : MvPolynomial (Σi,Fin (e i)) ℚ) :
    separateTensor d e (rename Sum.inl f * rename Sum.inr g) = reynoldsS d f ⊗ₜ[ℚ] reynoldsS e g := by
  rw [← tensorEquivSum_tmul]
  simp [separateTensor]

lemma totalWeight_sumElim {α β : Type*} (x : α →₀ ℕ) (y : β →₀ ℕ) :
    Finsupp.weight (fun _=>(1:ℤ)) (x.sumElim y) =
      Finsupp.weight (fun _=>(1:ℤ)) x + Finsupp.weight (fun _=>(1:ℤ)) y := by
  simp only [Finsupp.weight_apply,Finsupp.sum_sumElim,Function.comp_def]

lemma component_quotientTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) (m n : ℤ) (f : S d ⊗[ℚ] S e) :
    TensorProduct.map (componentB a μ d m) (componentB a μ e n) (quotientTensor a μ d e f)=
      quotientTensor a μ d e (TensorProduct.map (componentS d m) (componentS e n) f) := by
  induction f using OAI.tensorInductionOn with
  | tmul f g => rfl
  | add f g hf hg => simp [hf,hg]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_BothTaylorB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma tensorValue_translation (d e : I → ℕ) (t : ℚ) (x : S d ⊗[ℚ] S e) :
    tensorValue d e (TensorProduct.map (translationS d t) (translationS e t) x)=
      translation t (tensorValue d e x) := by
  induction x using OAI.tensorInductionOn with
  | tmul f g =>
    simp only [TensorProduct.map_tmul,tensorValue_tmul,map_mul,translation_rename]
    rfl
  | add x y hx hy => simp only [map_add,hx,hy]

lemma restrictTensor_translation {d e : I → ℕ} (A : Cut d e) (t : ℚ) (f : S (d+e)) :
    restrictTensor A (translationS (d+e) t f)=
      TensorProduct.map (translationS d t) (translationS e t) (restrictTensor A f) := by
  apply tensorValue_injective
  rw [tensorValue_translation,tensorValue_restrictTensor,tensorValue_restrictTensor,translation_rename]
  rfl

lemma restrictionB_translation (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (A : Cut d e) (t : ℚ) (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    restrictionB a c η hc hs A (translationB a (SlopeArithmetic.slope c η) (d+e) t f)=
      TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d t)
        (translationB a (SlopeArithmetic.slope c η) e t) (restrictionB a c η hc hs A f) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change restrictionB a c η hc hs A (quotientAlg a _ (d+e) (translationS (d+e) t f))=
      TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d t)
        (translationB a (SlopeArithmetic.slope c η) e t)
          (restrictionB a c η hc hs A (quotientAlg a _ (d+e) f))
    rw [restrictionB_mk,restrictionB_mk,restrictTensor_translation]
    generalize restrictTensor A f=x
    induction x using OAI.tensorInductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add,hx,hy]

noncomputable def bothTaylorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    B a μ d ⊗[ℚ] B a μ e →ₐ[ℚ] Polynomial (Polynomial (B a μ d ⊗[ℚ] B a μ e)) :=
  let L : B a μ d →ₐ[ℚ] Polynomial (Polynomial (B a μ d ⊗[ℚ] B a μ e)) := (Polynomial.CAlgHom : Polynomial (B a μ d ⊗[ℚ] B a μ e) →ₐ[ℚ] Polynomial (Polynomial (B a μ d ⊗[ℚ] B a μ e))).comp
    ((Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft :
      B a μ d →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e)).comp (taylorB a μ d))
  let R : B a μ e →ₐ[ℚ] Polynomial (Polynomial (B a μ d ⊗[ℚ] B a μ e)) := (Polynomial.mapAlgHom ((Polynomial.CAlgHom : (B a μ d ⊗[ℚ] B a μ e) →ₐ[ℚ] Polynomial (B a μ d ⊗[ℚ] B a μ e)).comp
    (Algebra.TensorProduct.includeRight : B a μ e →ₐ[ℚ] B a μ d ⊗[ℚ] B a μ e))).comp (taylorB a μ e)
  Algebra.TensorProduct.lift (S:=ℚ) L R (by
    let : CommRing (Polynomial (B a μ d ⊗[ℚ] B a μ e)) := inferInstance
    intro x y
    exact mul_comm (L x) (R y))

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ManyBlockDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def polynomialOnLeft {A D Q : Type*} [CommRing A] [CommRing D]
    [CommRing Q] [Algebra ℚ A] [Algebra ℚ D] [Algebra ℚ Q]
    (f : A →ₐ[ℚ] Polynomial D) : A ⊗[ℚ] Q →ₐ[ℚ] Polynomial (D ⊗[ℚ] Q) :=
  let L : A →ₐ[ℚ] Polynomial (D ⊗[ℚ] Q) :=
    (Polynomial.mapAlgHom (Algebra.TensorProduct.includeLeft : D →ₐ[ℚ] D ⊗[ℚ] Q)).comp f
  let R : Q →ₐ[ℚ] Polynomial (D ⊗[ℚ] Q) :=
    (Polynomial.CAlgHom : D ⊗[ℚ] Q →ₐ[ℚ] Polynomial (D ⊗[ℚ] Q)).comp
      Algebra.TensorProduct.includeRight
  Algebra.TensorProduct.lift (S:=ℚ) L R (fun x y => mul_comm (L x) (R y))

lemma polynomialOnLeft_eval_tmul {A D Q : Type*} [CommRing A] [CommRing D]
    [CommRing Q] [Algebra ℚ A] [Algebra ℚ D] [Algebra ℚ Q]
    (f : A →ₐ[ℚ] Polynomial D) (g : A) (h : Q) (t : ℚ) :
    (polynomialOnLeft f (g ⊗ₜ[ℚ] h)).eval (algebraMap ℚ _ t) =
      (f g).eval (algebraMap ℚ D t) ⊗ₜ[ℚ] h := by
  change (Polynomial.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℚ] D ⊗[ℚ] Q).toRingHom
      (f g) * Polynomial.C
        ((Algebra.TensorProduct.includeRight : Q →ₐ[ℚ] D ⊗[ℚ] Q) h)).eval _ = _
  rw [Polynomial.eval_mul,eval_map_rat,Polynomial.eval_C]
  change (_ ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] h) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

lemma polynomialOnLeft_coeff_tmul {A D Q : Type*} [CommRing A] [CommRing D]
    [CommRing Q] [Algebra ℚ A] [Algebra ℚ D] [Algebra ℚ Q]
    (f : A →ₐ[ℚ] Polynomial D) (g : A) (h : Q) (s : ℕ) :
    (polynomialOnLeft f (g ⊗ₜ[ℚ] h)).coeff s = (f g).coeff s ⊗ₜ[ℚ] h := by
  change (Polynomial.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℚ] D ⊗[ℚ] Q).toRingHom
      (f g) * Polynomial.C
        ((Algebra.TensorProduct.includeRight : Q →ₐ[ℚ] D ⊗[ℚ] Q) h)).coeff s = _
  rw [Polynomial.coeff_mul_C,Polynomial.coeff_map]
  change (_ ⊗ₜ[ℚ] 1) * (1 ⊗ₜ[ℚ] h) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_AllPairDiagonal
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma dimensionEquivB_mem_sourceFiltration (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ)
    (f : B a (SlopeArithmetic.slope c η) d)
    (hf : f∈sourceFiltration a c η hc θ d W) :
    dimensionEquivB a (SlopeArithmetic.slope c η) h f ∈ sourceFiltration a c η hc θ e W := by
  subst e
  exact hf

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_DegreeIdeals
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma componentB_mul_components (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k i j : ℤ) (x y : B a μ d) :
    componentB a μ d k (componentB a μ d i x * componentB a μ d j y)=
      if k=i+j then componentB a μ d i x * componentB a μ d j y else 0 := by
  obtain ⟨f,hf,hqf⟩:=gradeB_homogeneous_representative a μ d i _ ⟨x,rfl⟩
  obtain ⟨g,hg,hqg⟩:=gradeB_homogeneous_representative a μ d j _ ⟨y,rfl⟩
  rw [←hqf,←hqg]
  change componentB a μ d k (quotientAlg a μ d f * quotientAlg a μ d g)=_
  rw [←map_mul]
  change quotientAlg a μ d (componentS d k (f*g))=_
  rw [componentS_of_homogeneous d (f*g) (hf.mul hg)]
  split_ifs
  · exact (quotientAlg a μ d).map_mul f g
  · exact (quotientAlg a μ d).map_zero

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Histories_ShuffleLeafFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma translationB_shuffleB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (t : ℚ) (f : B a (SlopeArithmetic.slope c η) d) (g : B a (SlopeArithmetic.slope c η) e) :
    translationB a (SlopeArithmetic.slope c η) (d+e) t (shuffleB a c η hc d e hs f g)=
      shuffleB a c η hc d e hs (translationB a (SlopeArithmetic.slope c η) d t f)
        (translationB a (SlopeArithmetic.slope c η) e t g) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g =>
      exact congrArg (destabilizingSpace a (SlopeArithmetic.slope c η) (d+e)).mkQ
        (translation_shufflePolynomial a t f g)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ShuffleUnits
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma shuffleBUnit_eq_shuffleB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : slope c η d=slope c η e) :
    shuffleBUnit a c η hc d e (Or.inr (Or.inr hs))=shuffleB a c η hc d e hs := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro g
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    induction g using Submodule.Quotient.induction_on with
    | H g => rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_Restriction
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma castB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) {d e : I → ℕ}
    (h : d=e) (f : S d) : castB a μ h (quotientAlg a μ d f)=quotientAlg a μ e (castS h f) := by
  subst e; rfl

lemma restrictionBUnit_zero_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {e : I → ℕ} (A : Cut 0 e) (f : B a (slope c η) e) :
    restrictionBUnit a c η hc (Or.inl rfl) A (castB a _ (zero_add e).symm f)=
      (1 : B a (slope c η) 0)⊗ₜ[ℚ]f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change restrictionBUnit a c η hc (Or.inl rfl) A
      (castB a _ (zero_add e).symm (quotientAlg a (slope c η) e f))=
      (1 : B a (slope c η) 0)⊗ₜ[ℚ]quotientAlg a (slope c η) e f
    rw [castB_mk,restrictionBUnit_mk,restrictTensor_zero_left,quotientTensor_tmul,map_one]

lemma restrictionBUnit_zero_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d : I → ℕ} (A : Cut d 0) (f : B a (slope c η) d) :
    restrictionBUnit a c η hc (Or.inr (Or.inl rfl)) A (castB a _ (add_zero d).symm f)=
      f⊗ₜ[ℚ](1 : B a (slope c η) 0) := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change restrictionBUnit a c η hc (Or.inr (Or.inl rfl)) A
      (castB a _ (add_zero d).symm (quotientAlg a (slope c η) d f))=
      quotientAlg a (slope c η) d f⊗ₜ[ℚ](1 : B a (slope c η) 0)
    rw [castB_mk,restrictionBUnit_mk,restrictTensor_zero_right,quotientTensor_tmul,map_one]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FourCellFactorization
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
attribute [-simp] _root_.OAI.ElementaryPositivity.RawShuffle.targetValueAt_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

def firstColumn (d₁ e₁ d₂ e₂ : I → ℕ) (i : I) :
    (Fin (d₁ i) ⊕ Fin (d₂ i)) ↪ FourPacks d₁ e₁ d₂ e₂ i :=
  Function.Embedding.sumMap Function.Embedding.inl Function.Embedding.inl

def secondColumn (d₁ e₁ d₂ e₂ : I → ℕ) (i : I) :
    (Fin (e₁ i) ⊕ Fin (e₂ i)) ↪ FourPacks d₁ e₁ d₂ e₂ i :=
  Function.Embedding.sumMap Function.Embedding.inr Function.Embedding.inr

omit [Fintype I] [DecidableEq I] in
lemma canonical_first_column (d₁ e₁ d₂ e₂ : I → ℕ) :
    (fun i=>left (canonicalLeftCut d₁ e₁ d₂ e₂) i ∪
      left (canonicalRightCut d₁ e₁ d₂ e₂) i) =
      embedPack (firstColumn d₁ e₁ d₂ e₂) (fun _=>Finset.univ) := by
  funext i
  ext x
  rcases x with ((x|x)|(x|x)) <;>
    simp [canonicalLeftCut,canonicalRightCut,left,embedPackCut,sumPackCut,
      embedPack,firstColumn,Finset.mem_map,Function.Embedding.sumMap]

omit [Fintype I] [DecidableEq I] in
lemma canonical_second_column (d₁ e₁ d₂ e₂ : I → ℕ) :
    (fun i=>right (canonicalLeftCut d₁ e₁ d₂ e₂) i ∪
      right (canonicalRightCut d₁ e₁ d₂ e₂) i) =
      embedPack (secondColumn d₁ e₁ d₂ e₂) (fun _=>Finset.univ) := by
  funext i
  ext x
  rcases x with ((x|x)|(x|x)) <;>
    simp [canonicalLeftCut,canonicalRightCut,right,embedPackCut,sumPackCut,
      embedPack,secondColumn,Finset.mem_map,Function.Embedding.sumMap]

noncomputable def cutUnivRealization {d e : I → ℕ} (A : Cut d e) :
    Realization (d+e) (A:=fun i=>Fin (d i) ⊕ Fin (e i)) (fun _=>Finset.univ) :=
  fun i=>(packSplit A i).symm.trans (Equiv.subtypeUnivEquiv (fun _=>Finset.mem_univ _)).symm

lemma labeledPolynomial_univ_restrict {d e : I → ℕ} (A : Cut d e) (f : S (d+e)) :
    labeledPolynomial (A:=fun i=>Fin (d i) ⊕ Fin (e i)) f (fun _=>Finset.univ) =
      rename (Equiv.sigmaSumDistrib _ _).symm (tensorValue d e (restrictTensor A f)) := by
  rw [labeledPolynomial_eq (cutUnivRealization A),tensorValue_restrictTensor,rename_rename]
  congr 2
  funext x
  obtain ⟨y,rfl⟩ := (cutSplit A).surjective x
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  cases y with
  | inl x =>
    change (⟨x.1, (packSplit A x.1).symm (packSplit A x.1 (.inl x.2))⟩ : Σi,Fin (d i) ⊕ Fin (e i))=_
    rw [Equiv.symm_apply_apply]
    rfl
  | inr x =>
    change (⟨x.1, (packSplit A x.1).symm (packSplit A x.1 (.inr x.2))⟩ : Σi,Fin (d i) ⊕ Fin (e i))=_
    rw [Equiv.symm_apply_apply]
    rfl

def firstColumnVars (d₁ e₁ d₂ e₂ : I → ℕ) :
    CellVars d₁ d₂ → CellVars d₁ e₁ ⊕ CellVars d₂ e₂
  | Sum.inl x => Sum.inl (Sum.inl x)
  | Sum.inr x => Sum.inr (Sum.inl x)

def secondColumnVars (d₁ e₁ d₂ e₂ : I → ℕ) :
    CellVars e₁ e₂ → CellVars d₁ e₁ ⊕ CellVars d₂ e₂
  | Sum.inl x => Sum.inl (Sum.inr x)
  | Sum.inr x => Sum.inr (Sum.inr x)

lemma fourGridPolynomial_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ d₂) (B : Cut e₁ e₂) (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    fourGridPolynomial a f g d₁ e₁ d₂ e₂ =
      rename (firstColumnVars d₁ e₁ d₂ e₂) (tensorValue d₁ d₂ (restrictTensor A f)) *
      rename (secondColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ e₂ (restrictTensor B g)) *
      rename (fourPackEquiv d₁ e₁ d₂ e₂)
        (crossKernelPolynomial a (canonicalGridCut d₁ e₁ d₂ e₂)
          (canonicalLeftCut d₁ e₁ d₂ e₂) (canonicalRightCut d₁ e₁ d₂ e₂)) := by
  unfold fourGridPolynomial canonicalGridPolynomial gridPolynomial
  rw [canonical_first_column,canonical_second_column,←embed_labeledPolynomial,
    ←embed_labeledPolynomial,labeledPolynomial_univ_restrict A,labeledPolynomial_univ_restrict B]
  simp only [map_mul,rename_rename]
  congr 2
  · congr 2
    funext x
    cases x <;> rfl
  · congr 2
    funext x
    cases x <;> rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNExpansion
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.ShufflePolynomiality ElementaryPositivity.PackConvolution
open ElementaryPositivity.SeparatedSymmetry
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.tensorSCommRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.tensorSAlgebra
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.fourSCommRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.fourSAlgebra
noncomputable def fourInterchange (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S d₂) ⊗[ℚ] (S e₁ ⊗[ℚ] S e₂) ≃ₗ[ℚ]
      (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) :=
  TensorProduct.tensorTensorTensorComm ℚ _ _ _ _

omit [Fintype I] [DecidableEq I] in
lemma fourValue_interchange (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁ ⊗[ℚ] S d₂) (g : S e₁ ⊗[ℚ] S e₂) :
    fourValue d₁ e₁ d₂ e₂ (fourInterchange d₁ e₁ d₂ e₂ (f⊗ₜ[ℚ]g))=
      rename (firstColumnVars d₁ e₁ d₂ e₂) (tensorValue d₁ d₂ f) *
      rename (secondColumnVars d₁ e₁ d₂ e₂) (tensorValue e₁ e₂ g) := by
  induction f using OAI.tensorInductionOn with
  | add f h hf hh =>
    rw [TensorProduct.add_tmul, (fourInterchange d₁ e₁ d₂ e₂).map_add,
      (fourValue d₁ e₁ d₂ e₂).map_add, (tensorValue d₁ d₂).map_add, map_add, hf, hh, add_mul]
  | tmul x y =>
    induction g using OAI.tensorInductionOn with
    | add g h hg hh =>
      rw [TensorProduct.tmul_add, (fourInterchange d₁ e₁ d₂ e₂).map_add,
        (fourValue d₁ e₁ d₂ e₂).map_add, (tensorValue e₁ e₂).map_add, map_add, hg, hh, mul_add]
    | tmul z w =>
      simp only [fourInterchange,TensorProduct.tensorTensorTensorComm_tmul,
        fourValue_tmul,tensorValue_tmul,map_mul,rename_rename]
      have h₁ : Sum.inl ∘ Sum.inl = firstColumnVars d₁ e₁ d₂ e₂ ∘ Sum.inl := rfl
      have h₂ : Sum.inl ∘ Sum.inr = secondColumnVars d₁ e₁ d₂ e₂ ∘ Sum.inl := rfl
      have h₃ : Sum.inr ∘ Sum.inl = firstColumnVars d₁ e₁ d₂ e₂ ∘ Sum.inr := rfl
      have h₄ : Sum.inr ∘ Sum.inr = secondColumnVars d₁ e₁ d₂ e₂ ∘ Sum.inr := rfl
      rw [h₁,h₂,h₃,h₄]
      ring

noncomputable def fourCrossPolynomial (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :=
  rename (fourPackEquiv d₁ e₁ d₂ e₂)
    (crossKernelPolynomial a (canonicalGridCut d₁ e₁ d₂ e₂)
      (canonicalLeftCut d₁ e₁ d₂ e₂) (canonicalRightCut d₁ e₁ d₂ e₂))

lemma fourGridPolynomial_one (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourGridPolynomial a (1 : S (d₁+d₂)) (1 : S (e₁+e₂)) d₁ e₁ d₂ e₂=
      fourCrossPolynomial a d₁ e₁ d₂ e₂ := by
  rw [fourGridPolynomial_factor a d₁ e₁ d₂ e₂ (firstCut d₁ d₂) (firstCut e₁ e₂)]
  simp only [tensorValue_restrictTensor,OneMemClass.coe_one,map_one,one_mul,fourCrossPolynomial]

lemma fourCrossPolynomial_invariant (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (σ : CellGroup d₁ e₁ × CellGroup d₂ e₂) :
    rename (sumAction (cellAction d₁ e₁) (cellAction d₂ e₂) σ)
      (fourCrossPolynomial a d₁ e₁ d₂ e₂)=fourCrossPolynomial a d₁ e₁ d₂ e₂ := by
  rw [←fourGridPolynomial_one]
  exact fourGridPolynomial_invariant _ _ _ _ _ _ _ _

noncomputable def fourCrossTensor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁ ⊗[ℚ] S e₁) ⊗[ℚ] (S d₂ ⊗[ℚ] S e₂) :=
  separateFour d₁ e₁ d₂ e₂ (fourCrossPolynomial a d₁ e₁ d₂ e₂)

lemma fourValue_fourCrossTensor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourValue d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)=
      fourCrossPolynomial a d₁ e₁ d₂ e₂ :=
  fourValue_separateFour _ _ _ _ _ (fourCrossPolynomial_invariant _ _ _ _ _)

lemma separateFour_grid_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ d₂) (B : Cut e₁ e₂) (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)=
      fourInterchange d₁ e₁ d₂ e₂ (restrictTensor A f⊗ₜ[ℚ]restrictTensor B g)*
        fourCrossTensor a d₁ e₁ d₂ e₂ := by
  apply fourValue_injective
  rw [fourValue_separateFour _ _ _ _ _ (fourGridPolynomial_invariant _ _ _ _ _ _ _)]
  change _=fourValueAlg d₁ e₁ d₂ e₂ (_*_)
  rw [map_mul,fourValueAlg_apply,fourValueAlg_apply,fourValue_interchange,fourValue_fourCrossTensor]
  exact fourGridPolynomial_factor _ _ _ _ _ A B f g

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ColumnTaylor
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance colTaylorTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance colTaylorTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance colTaylorFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance colTaylorFourAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SeparationHomogeneity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SeparatedSymmetry ElementaryPositivity.Homogeneity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable def tensorSeparationSeries (a : I → I → ℕ) (d e : I → ℕ) (f : S (d+e)) :
    LaurentSeries (S d ⊗[ℚ] S e) :=
  (inverseKernelUnit a d e).val * polynomial (R:=S d ⊗[ℚ] S e) (relativeTaylor d e (restrictTensor (firstCut d e) f))
end ElementaryPositivity.RawShuffle.SeparationInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_BraidingFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open SplitTree SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance braidTensorCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidTensorAlgebra_r46a8db_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidTensorNUSemiring (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) :=
  (braidTensorCommRing a μ d e).toNonUnitalNonAssocSemiring

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def unitalSourceFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) : Submodule ℚ (B a (slope c η) d) := by
  classical
  exact if d=0 then if W≤0 then ⊤ else ⊥ else sourceFiltration a c η hc θ d W

lemma unitalSourceFiltration_nonzero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) (hd : d≠0) (W : ℤ) :
    unitalSourceFiltration a c η hc θ d W=sourceFiltration a c η hc θ d W := by
  simp only [unitalSourceFiltration,ite_eq_right hd]

lemma castB_mem_unitalSourceFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} (h : d=e) (W : ℤ) {f : B a (slope c η) d}
    (hf : f∈unitalSourceFiltration a c η hc θ d W) :
    castB a (slope c η) h f∈unitalSourceFiltration a c η hc θ e W := by
  subst e
  exact hf

lemma unitalSourceFiltration_unit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) : (1 : B a (slope c η) 0)∈unitalSourceFiltration a c η hc θ 0 0 := by
  simp only [unitalSourceFiltration,le_refl,ite_true, if_true,Submodule.mem_top]

lemma unitalSourceFiltration_antitone (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d : I → ℕ) : Antitone (unitalSourceFiltration a c η hc θ d) := by
  classical
  intro u v huv
  by_cases hd : d=0
  · by_cases hu : u≤0
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_left hu,le_top]
    · have hv : ¬v≤0 := by omega
      simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_right hu,ite_eq_right hv,le_refl]
  · simpa only [unitalSourceFiltration_nonzero a c η hc θ d hd] using
      sourceFiltration_antitone a c η hc θ d huv

noncomputable def unitalSourceTensorFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :=
  additiveTensorFiltration (unitalSourceFiltration a c η hc θ d)
    (unitalSourceFiltration a c η hc θ e) W

lemma unitalSourceTensorFiltration_nonzero (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) (hd : d≠0) (he : e≠0) (W : ℤ) :
    unitalSourceTensorFiltration a c η hc θ d e W=sourceTensorFiltration a c η hc θ d e W := by
  unfold unitalSourceTensorFiltration sourceTensorFiltration
  congr 1 <;> funext w
  · exact unitalSourceFiltration_nonzero a c η hc θ d hd w
  · exact unitalSourceFiltration_nonzero a c η hc θ e he w

lemma restrictionBUnit_independent (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (A C : Cut d e)
    (f : B a (slope c η) (d+e)) :
    restrictionBUnit a c η hc hs A f=restrictionBUnit a c η hc hs C f := by
  induction f using Submodule.Quotient.induction_on with
  | H f => exact congrArg (quotientTensor a (slope c η) d e) (restrictTensor_independent A C f)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open HahnSeries SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance braidCoeffTensorS_r46a8db_1 (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance braidCoeffTensorSA_r46a8db_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance braidCoeffTensorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance

noncomputable local instance braidCoeffTensorBA_r46a8db_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidCoeffTensorBN (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) := (braidCoeffTensorB a μ d e).toNonUnitalNonAssocSemiring

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_ProductUnitFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]
lemma OnSlopeOrZero.compatible {c η : I → ℝ} {θ : ℝ} {d e : I → ℕ}
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e) :
    d=0 ∨ e=0 ∨ slope c η d=slope c η e := by
  rcases hd with hd|hd
  · exact Or.inl hd
  rcases he with he|he
  · exact Or.inr (Or.inl he)
  exact Or.inr (Or.inr (hd.trans he.symm))

end ElementaryPositivity.SlopeArithmetic

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma shuffleBUnit_one_left (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d : I → ℕ) (hs : (0 : I → ℕ)=0 ∨ d=0 ∨ slope c η 0=slope c η d)
    (f : B a (slope c η) d) :
    shuffleBUnit a c η hc 0 d hs 1 f=castB a (slope c η) (zero_add d).symm f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change shuffleBUnit a c η hc 0 d hs (quotientAlg a (slope c η) 0 1)
      (quotientAlg a (slope c η) d f)=_
    change quotientAlg a (slope c η) (0+d) (shufflePolynomial a 1 f)=_
    rw [shufflePolynomial_unit_left,←castB_mk]
    rfl

lemma shuffleBUnit_one_right (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d : I → ℕ) (hs : d=0 ∨ (0 : I → ℕ)=0 ∨ slope c η d=slope c η 0)
    (f : B a (slope c η) d) :
    shuffleBUnit a c η hc d 0 hs f 1=castB a (slope c η) (add_zero d).symm f := by
  induction f using Submodule.Quotient.induction_on with
  | H f =>
    change shuffleBUnit a c η hc d 0 hs (quotientAlg a (slope c η) d f)
      (quotientAlg a (slope c η) 0 1)=_
    change quotientAlg a (slope c η) (d+0) (shufflePolynomial a f 1)=_
    rw [shufflePolynomial_unit_right,←castB_mk]
    rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_FourBraiding
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open HahnSeries SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensor
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensorN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourTensorM
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.braidFourM
noncomputable def fourUnitalFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) (W : ℤ) :=
  additiveTensorFiltration (unitalSourceTensorFiltration a c η hc θ d₁ e₁)
    (unitalSourceTensorFiltration a c η hc θ d₂ e₂) W

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection ElementaryPositivity.LaurentAtInfinity
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensor
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorA
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorM
noncomputable def unitalRestrictionRelativeB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) (d+e) →ₐ[ℚ] Polynomial (B a (slope c η) d ⊗[ℚ] B a (slope c η) e) :=
  (relativeTaylorB a (slope c η) d e).comp (restrictionBUnit a c η hc hs (firstCut d e))

namespace SeparationInfinity
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensor
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorA
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorN
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.unitalSepTensorM
noncomputable def unitalSeparationSeries (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) (d+e) →ₗ[ℚ] LaurentSeries (B a (slope c η) d⊗[ℚ]B a (slope c η) e) :=
  (mulPolynomial (quotientInverseKernelUnit a (slope c η) d e).val).comp
    (unitalRestrictionRelativeB a c η hc hs).toLinearMap

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GridQuotient
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] tensorSCommRing tensorSAlgebra fourSCommRing fourSAlgebra
noncomputable local instance tensorBCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d ⊗[ℚ] B a μ e) := inferInstance
noncomputable local instance tensorBAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d ⊗[ℚ] B a μ e) := inferInstance

noncomputable local instance fourBCommRing_r46a8db_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := inferInstance
noncomputable local instance fourBAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := inferInstance

noncomputable local instance tensorBNonUnitalNonAssocSemiring (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) := (tensorBCommRing a μ d e).toNonUnitalNonAssocSemiring

noncomputable def shuffleTensorBUnit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) d⊗[ℚ]B a (slope c η) e →ₗ[ℚ] B a (slope c η) (d+e) :=
  TensorProduct.lift (shuffleBUnit a c η hc d e hs)

lemma quotient_shuffleTensorUnit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (x : S d⊗[ℚ]S e) :
    quotientAlg a (slope c η) (d+e) (shuffleTensorLinear a d e x)=
    shuffleTensorBUnit a c η hc d e hs (quotientTensor a (slope c η) d e x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => rfl

noncomputable def fourQuotient (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂) →ₐ[ℚ]
    (B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  Algebra.TensorProduct.map (quotientTensor a μ d₁ e₁) (quotientTensor a μ d₂ e₂)

noncomputable def fourInterchangeB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (B a μ d₁⊗[ℚ]B a μ d₂)⊗[ℚ](B a μ e₁⊗[ℚ]B a μ e₂) ≃ₗ[ℚ]
    (B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  TensorProduct.tensorTensorTensorComm ℚ _ _ _ _

lemma fourQuotient_interchange (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁⊗[ℚ]S d₂) (g : S e₁⊗[ℚ]S e₂) :
    (fourQuotient a μ d₁ e₁ d₂ e₂).toLinearMap (fourInterchange d₁ e₁ d₂ e₂ (f⊗ₜ[ℚ]g))=
    fourInterchangeB a μ d₁ e₁ d₂ e₂
      (quotientTensor a μ d₁ d₂ f⊗ₜ[ℚ]quotientTensor a μ e₁ e₂ g) := by
  exact (LinearMap.congr_fun (TensorProduct.tensorTensorTensorComm_comp_map ℚ
    (quotientAlg a μ d₁).toLinearMap (quotientAlg a μ d₂).toLinearMap
    (quotientAlg a μ e₁).toLinearMap (quotientAlg a μ e₂).toLinearMap) (f⊗ₜ[ℚ]g)).symm

lemma quotient_twoTargetTransfer_unit (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ x)=
    TensorProduct.map (shuffleTensorBUnit a c η hc d₁ e₁ h₁) (shuffleTensorBUnit a c η hc d₂ e₂ h₂)
      ((fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toLinearMap x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy =>
    change (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)).toLinearMap
      ((twoTargetTransfer a d₁ e₁ d₂ e₂) (x+y))=_
    rw [(twoTargetTransfer a d₁ e₁ d₂ e₂).map_add,LinearMap.map_add,LinearMap.map_add,LinearMap.map_add]
    exact congrArg₂ (·+·) hx hy
  | tmul x y =>
    change quotientAlg a (slope c η) (d₁+e₁) (shuffleTensorLinear a d₁ e₁ x)⊗ₜ[ℚ]
      quotientAlg a (slope c η) (d₂+e₂) (shuffleTensorLinear a d₂ e₂ y)=_
    rw [quotient_shuffleTensorUnit a c η hc d₁ e₁ h₁,
      quotient_shuffleTensorUnit a c η hc d₂ e₂ h₂]
    rfl

lemma fourQuotient_grid_factor (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (A : Cut d₁ d₂) (C : Cut e₁ e₂) (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toLinearMap
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))=
    fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂
      (restrictionBUnit a c η hc hd A (quotientAlg a (slope c η) (d₁+d₂) f)⊗ₜ[ℚ]
       restrictionBUnit a c η hc he C (quotientAlg a (slope c η) (e₁+e₂) g)) *
    (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toLinearMap (fourCrossTensor a d₁ e₁ d₂ e₂) := by
  rw [separateFour_grid_factor a d₁ e₁ d₂ e₂ A C]
  change (fourQuotient a (slope c η) d₁ e₁ d₂ e₂) (_ * _)=_
  rw [map_mul]
  change (fourQuotient a (slope c η) d₁ e₁ d₂ e₂).toLinearMap _ * _=_
  rw [fourQuotient_interchange]
  rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TensorColumnSeriesFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance unitalNatS (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance unitalNatSA_r46a8db_1 (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance unitalNatB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance

end ElementaryPositivity.RawShuffle.SeparationInfinity

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ClearingKernel
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance clearingTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ClearedSeparationB
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance clearBTensorS (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance gridTensorBCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d ⊗[ℚ] B a μ e) := inferInstance
noncomputable local instance gridTensorBAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d ⊗[ℚ] B a μ e) := inferInstance

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_GridShapeFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

def ShuffleFiltered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) (d e : I → ℕ) : Prop :=
  ∀ (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e)
    (U V : ℤ) (f : B a (slope c η) d) (g : B a (slope c η) e),
    f∈unitalSourceFiltration a c η hc θ d U →
    g∈unitalSourceFiltration a c η hc θ e V →
    shuffleBUnit a c η hc d e (hd.compatible he) f g∈unitalSourceFiltration a c η hc θ (d+e) (U+V)

lemma quotientTensor_cast_mem_unitalSource (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (W : ℤ) (f : S d⊗[ℚ]S e)
    (hf : quotientTensor a (slope c η) d e f∈unitalSourceTensorFiltration a c η hc θ d e W) :
    quotientTensor a (slope c η) d' e' (castTensor h k f)∈
      unitalSourceTensorFiltration a c η hc θ d' e' W := by
  subst d'
  subst e'
  exact hf

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ShuffleFiltration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma size_positive (d : I → ℕ) (hd : d≠0) : 0<∑ i,d i := by
  classical
  obtain ⟨i,hi⟩ : ∃ i,d i≠0 := by
    by_contra h
    push Not at h
    exact hd (funext h)
  exact Finset.sum_pos' (fun _ _=>Nat.zero_le _) ⟨i,Finset.mem_univ _,Nat.pos_of_ne_zero hi⟩

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_TwoTargetFiltration
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def twoTargetTransferB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂) :
    (B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂) →ₗ[ℚ]
    B a (slope c η) (d₁+e₁)⊗[ℚ]B a (slope c η) (d₂+e₂) :=
  TensorProduct.map (shuffleTensorBUnit a c η hc d₁ e₁ h₁)
    (shuffleTensorBUnit a c η hc d₂ e₂ h₂)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CellLeadingSum
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open ElementaryPositivity.PackConvolution HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA Classical.propDecidable

noncomputable local instance cellLeadTensorN_r46a8db_1 (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) :=
  (clearBTensorB a μ d e).toNonUnitalNonAssocSemiring
noncomputable def cellLeadingB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) (f : S d) (g : S e) :
    B a (slope c η) (d₁+e₁)⊗[ℚ]B a (slope c η) (d₂+e₂) :=
  if h : d₁+d₂=d ∧ e₁+e₂=e then
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ (hon.1.compatible hon.2.1) (hon.2.2.1.compatible hon.2.2.2)
        (fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂
          ((unitalSeparationSeries a c η hc (hon.1.compatible hon.2.2.1)
              (quotientAlg a (slope c η) (d₁+d₂) (castS h.1.symm f))).coeff 0⊗ₜ[ℚ]
           (unitalSeparationSeries a c η hc (hon.2.1.compatible hon.2.2.2)
              (quotientAlg a (slope c η) (e₁+e₂) (castS h.2.symm g))).coeff 0))
  else 0

noncomputable def castBTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') :
    B a μ d⊗[ℚ]B a μ e ≃ₗ[ℚ] B a μ d'⊗[ℚ]B a μ e' := by
  subst d'
  subst e'
  exact LinearEquiv.refl ℚ _

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SignedCoproductGridGrade
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.PackConvolution
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

def cutShapeDimensionEquiv {d : I → ℕ} {s : Pack (A:=A)} (R : Realization d s) :
    CutShape s ≃ DimensionSplit d :=
  Equiv.piCongrRight fun i => finCongr (congrArg (·+1) (congrFun (realization_card R) i))

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)] in
@[simp] lemma cutShapeDimensionEquiv_left {d : I → ℕ} {s : Pack (A:=A)}
    (R : Realization d s) (u : CutShape s) :
    DimensionSplit.left (cutShapeDimensionEquiv R u) = (fun i=>(u i).val) := rfl

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (A index)] [∀ index, DecidableEq (A index)] in
@[simp] lemma cutShapeDimensionEquiv_right {d : I → ℕ} {s : Pack (A:=A)}
    (R : Realization d s) (u : CutShape s) :
    DimensionSplit.right (cutShapeDimensionEquiv R u) = shapeComplement u := by
  funext i
  change d i-(u i).val=(s i).card-(u i).val
  exact congrArg (fun n=>n-(u i).val) (congrFun (realization_card R) i).symm

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalGradeAlgebra
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def unitalFiltrationCast (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (θ : ℝ) {d e : I → ℕ} {U V : ℤ} (h : d=e) (k : U=V) :
    unitalSourceFiltration a c η hc θ d U ≃ₗ[ℚ] unitalSourceFiltration a c η hc θ e V := by
  subst e
  subst V
  exact LinearEquiv.refl _ _

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
open scoped DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev SlopeWeight (c η : I → ℝ) (hc : ∀ i,0 < c i) (θ : ℝ) :=
  slopeDimensions c η hc θ × ℤ

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SignedTensorGradeProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def signedCellMultiplyB (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂) :
    B a (slope c η) d₁⊗[ℚ]B a (slope c η) d₂ →ₗ[ℚ]
    B a (slope c η) e₁⊗[ℚ]B a (slope c η) e₂ →ₗ[ℚ]
    B a (slope c η) (d₁+e₁)⊗[ℚ]B a (slope c η) (d₂+e₂) :=
  ((-1 : ℚ)^eulerForm a d₂ e₁) • TensorProduct.curry
    ((twoTargetTransferB a c η hc d₁ e₁ d₂ e₂
      (hon.1.compatible hon.2.1) (hon.2.2.1.compatible hon.2.2.2)).comp
      (fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂).toLinearMap)

lemma signedCellMultiplyB_apply (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hon : CellsOnSlope c η θ d₁ e₁ d₂ e₂)
    (x : B a (slope c η) d₁⊗[ℚ]B a (slope c η) d₂)
    (y : B a (slope c η) e₁⊗[ℚ]B a (slope c η) e₂) :
    signedCellMultiplyB a c η hc θ d₁ e₁ d₂ e₂ hon x y=
      ((-1 : ℚ)^eulerForm a d₂ e₁) •
        twoTargetTransferB a c η hc d₁ e₁ d₂ e₂
          (hon.1.compatible hon.2.1) (hon.2.2.1.compatible hon.2.2.2)
          (fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂ (x⊗ₜ[ℚ]y)) := rfl

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_UnitalShuffleCoproduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct DirectSum
open DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

abbrev SlopeSplit (c η : I → ℝ) (_hc : ∀ i,0 < c i) (θ : ℝ) (d : I → ℕ) :=
  {s : DimensionSplit d // OnSlopeOrZero c η θ (left s) ∧ OnSlopeOrZero c η θ (right s)}

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_SlopeGridSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

abbrev SlopeColumnGrid (c η : I → ℝ) (θ : ℝ) (d e α β : I → ℕ) :=
  {s : ColumnDimensionGrid d e α β //
    CellsOnSlope c η θ (left s.val.1) (left s.val.2) (right s.val.1) (right s.val.2)}

end ElementaryPositivity.RawShuffle

end

end OAI
end


