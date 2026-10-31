-- Prove2me | Definitions.Def_OAIQ025S003
-- name    : OAIQ025S003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:48:39.650287+00:00
-- url     : https://prove2.me/theorems/a7993b35-2962-4701-a1a7-7bd972dba2f0
-- title:
--   Definitions bundle OAIQ025S003 of the split of OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 157 declarations of OpenAI's Lean: 73 definitions, 1 inductive type or structure, 12 instances and 71 theorems. The definitions and types are `OAI.Release061.Biholomorph.generatorAdjoint`, `OAI.Release061.Biholomorph.generatorAdjointHom`, `OAI.Release061.Biholomorph.generatorAdjointMatrix`, `OAI.Release061.Biholomorph.generatorDeterminant`, `OAI.Release061.Biholomorph.generatorLieAdjoint`, `OAI.Release061.Biholomorph.generatorPushForwardLinear`, `OAI.Release061.Biholomorph.modelComplexField`, `OAI.Release061.Biholomorph.modelEulerWeight`, `OAI.Release061.Biholomorph.modelRotationWeight`, `OAI.Release061.Biholomorph.oneParameterGenerator`, `OAI.Release061.Biholomorph.restrict`, `OAI.Release061.MeromorphicGermField`, `OAI.Release061.NashBoundaryScalingChart.domain`, `OAI.Release061.NashBoundaryScalingChart.scaled_local_biholomorph`, `OAI.Release061.Wiener.BoundarySpace`, `OAI.Release061.Wiener.LocalBishopData`, `OAI.Release061.Wiener.Space`, `OAI.Release061.Wiener.bishopDisc`, `OAI.Release061.Wiener.bishopInput`, `OAI.Release061.Wiener.bishopNormal`, `OAI.Release061.Wiener.bishopRHS`, `OAI.Release061.Wiener.boundary`, `OAI.Release061.Wiener.coeff`, `OAI.Release061.Wiener.conjPoly`, `OAI.Release061.Wiener.conjugate`, `OAI.Release061.Wiener.constantReal`, `OAI.Release061.Wiener.cutoff`, `OAI.Release061.Wiener.discSlice`, `OAI.Release061.Wiener.discValue`, `OAI.Release061.Wiener.fromModes`, `OAI.Release061.Wiener.hilbert`, `OAI.Release061.Wiener.limitModel`, `OAI.Release061.Wiener.modesCLM`, `OAI.Release061.Wiener.modesLinear`, `OAI.Release061.Wiener.multiplier`, `OAI.Release061.Wiener.normalSlice`, `OAI.Release061.Wiener.normalizedHilbert`, `OAI.Release061.Wiener.polyDisc`, `OAI.Release061.Wiener.realAlgebra`, `OAI.Release061.Wiener.realEvaluation` and 34 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `SymmetricDomains_ActionAutomorphismHomRange`, `SymmetricDomains_AlgebraicIndependentNashPartials`, `SymmetricDomains_AnalyticDirectionalDerivationFun`, `SymmetricDomains_AnalyticMulZeroGerm`, `SymmetricDomains_AnalyticNashRank`, `SymmetricDomains_BishopAnalyticDiscs`, `SymmetricDomains_BishopBoundarySolution`, `SymmetricDomains_BishopNormalZeroDeformation`, `SymmetricDomains_BoundaryInjective`, `SymmetricDomains_CayleyTangentBound`, `SymmetricDomains_CompleteGeneratorLieAlgebra`, `SymmetricDomains_ComplexificationRankLeReal`, `SymmetricDomains_EtaleDerivationExtensionUnique`, `SymmetricDomains_FiniteCoveringRamifiedSection`, `SymmetricDomains_ForwardBackwardGerm`, `SymmetricDomains_GeneratorAdjointContinuous`, `SymmetricDomains_GeneratorAdjointHom`, `SymmetricDomains_GeneratorDeterminantDerivZero`, `SymmetricDomains_GeneratorLieAdjoint`, `SymmetricDomains_GeneratorPushForwardLinear`, `SymmetricDomains_LocalBishopData`, `SymmetricDomains_ModelChartOpen`, `SymmetricDomains_ModelComplexField`, `SymmetricDomains_ModelRotationWeight`, `SymmetricDomains_NormalizedLocalInverse`, `SymmetricDomains_PolynomialRamifiedAnalyticRoot`, `SymmetricDomains_ScaledDiscDeltaC1`, `SymmetricDomains_ScaledLocal`, `SymmetricDomains_ScaledModelC1Limit`, `SymmetricDomains_ScaledRadialOperatorApply`, `SymmetricDomains_SchwarzRadialExpansion`, `SymmetricDomains_SupportCayleyOpenImage`, `SymmetricDomains_TransverseCutoffs`, `SymmetricDomains_VerticalPieceBasePolynomial`, `SymmetricDomains_WeightedChartTwoSided`, `SymmetricDomains_ZeroLocusPolynomialSmooth`.
--
--   **Imports.** It imports the published bundle `Def_SymmetricDomains`; the bundles `OAIQ025S000`, `OAIQ025S001` and `OAIQ025S002` of this split.
--
--   **Imported by** (directly, in this split): the statement `OAI.Release061.NashBoundaryScalingChart.global_from_two_sided`; the proofs of `OAI.Release061.Biholomorph.WeightedLieModel.exists_positive_real`, `OAI.Release061.Biholomorph.exists_actual_aut_chart_unimodular_jacobian`, `OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric`, `OAI.Release061.NashBoundaryChart.locally_small_slope_good`, `OAI.Release061.NashBoundaryScalingChart.global_from_two_sided`, `OAI.Release061.NashPatch.principal_rank_dichotomy`, `OAI.Release061.cocompact_bounded_affine_smooth`, `OAI.Release061.interior_balls_from_small_slope_graphs`, `OAI.Release061.isSemialgebraic_centered_nash_cover`, `OAI.Release061.main`, `OAI.Release061.original_supported_hermitian_model` and `OAI.Release061.semialgebraic_inward_analytic_from_family`.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S000
import Definitions.Def_OAIQ025S001
import Definitions.Def_OAIQ025S002

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ZeroLocusPolynomialSmooth
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


namespace Biholomorph

noncomputable def restrict {n m : ℕ} {S S' : Set (Affine n)} {T T' : Set (Affine m)}
    (e : Biholomorph S T) (hS : S' ⊆ S) (hT : T' ⊆ T)
    (he : ∀ x : S, x.val ∈ S' ↔ (e.toHomeomorph x).val ∈ T') :
    Biholomorph S' T' := by
  let F : S' → T' := fun x => ⟨(e.toHomeomorph (Set.inclusion hS x)).val,
    (he (Set.inclusion hS x)).mp x.property⟩
  let G : T' → S' := fun y => ⟨(e.toHomeomorph.symm (Set.inclusion hT y)).val,
    (he (e.toHomeomorph.symm (Set.inclusion hT y))).mpr (by
      simpa only [Homeomorph.apply_symm_apply] using y.property)⟩
  have hF : Continuous F :=
    (continuous_subtype_val.comp (e.toHomeomorph.continuous.comp
      (Topology.IsEmbedding.inclusion hS).continuous)).subtype_mk _
  have hG : Continuous G :=
    (continuous_subtype_val.comp (e.toHomeomorph.symm.continuous.comp
      (Topology.IsEmbedding.inclusion hT).continuous)).subtype_mk _
  refine ⟨⟨⟨F,G,?_,?_⟩,hF,hG⟩,?_,?_⟩
  · intro x
    apply Subtype.ext
    exact congrArg (Subtype.val : S → Affine n) (e.toHomeomorph.symm_apply_apply (Set.inclusion hS x))
  · intro y
    apply Subtype.ext
    exact congrArg (Subtype.val : T → Affine m) (e.toHomeomorph.apply_symm_apply (Set.inclusion hT y))
  · exact e.holomorphic_toFun.comp (f := Set.inclusion hS) (holomorphicOnSubset_val S')
  · exact e.holomorphic_invFun.comp (f := Set.inclusion hT) (holomorphicOnSubset_val T')

end Biholomorph

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BoundaryInjective
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Complex
open scoped Topology
noncomputable section
namespace Release061.Wiener
open scoped BigOperators ComplexConjugate Topology
open Set Filter

noncomputable def wnorm (p : Poly) : ℝ := p.coeff.sum (fun n z => weight n*‖z‖)

lemma wnorm_eq_sum (p : Poly) {s : Finset ℤ} (hs : p.coeff.support ⊆ s) :
    wnorm p = ∑ n ∈ s, weight n*‖p.coeff n‖ :=
  Finsupp.sum_of_support_subset p.coeff hs _ (by simp)

lemma wnorm_zero : wnorm 0 = 0 := by simp [wnorm]

lemma wnorm_add_le (p q : Poly) : wnorm (p+q) ≤ wnorm p+wnorm q := by
  classical
  let s := p.coeff.support ∪ q.coeff.support
  have hp : p.coeff.support ⊆ s := Finset.subset_union_left
  have hq : q.coeff.support ⊆ s := Finset.subset_union_right
  have hpq : (p+q).coeff.support ⊆ s := by
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.support_add
  rw [wnorm_eq_sum _ hpq,wnorm_eq_sum _ hp,wnorm_eq_sum _ hq,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
  calc weight n*‖p.coeff n+q.coeff n‖ ≤ weight n*(‖p.coeff n‖+‖q.coeff n‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (weight_pos n).le
    _ = _ := by ring

lemma wnorm_neg (p : Poly) : wnorm (-p) = wnorm p := by
  simp [wnorm,Finsupp.sum_neg_index]

lemma wnorm_eq_zero {p : Poly} (hp : wnorm p = 0) : p = 0 := by
  classical
  have hz : ∀ n ∈ p.coeff.support, weight n*‖p.coeff n‖ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun n _ => mul_nonneg (weight_pos n).le (norm_nonneg _))).mp hp
  apply AddMonoidAlgebra.ext
  ext n
  by_cases hn : n ∈ p.coeff.support
  · exact norm_eq_zero.mp ((mul_eq_zero.mp (hz n hn)).resolve_left (weight_pos n).ne')
  · simpa using Finsupp.notMem_support_iff.mp hn

lemma wnorm_single (n : ℤ) (z : ℂ) : wnorm (.single n z) = weight n*‖z‖ := by
  unfold wnorm
  rw [AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)

lemma wnorm_sum_le {ι : Type*} (s : Finset ι) (p : ι → Poly) :
    wnorm (∑ i ∈ s, p i) ≤ ∑ i ∈ s, wnorm (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wnorm_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (wnorm_add_le _ _).trans (add_le_add (le_refl _) ih)

lemma wnorm_mul_le (p q : Poly) : wnorm (p*q) ≤ wnorm p*wnorm q := by
  classical
  rw [AddMonoidAlgebra.mul_def]
  simp only [Finsupp.sum]
  calc
    _ ≤ ∑ n ∈ p.coeff.support,
        ∑ m ∈ q.coeff.support, wnorm (.single (n+m) (p.coeff n*q.coeff m)) :=
      (wnorm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => wnorm_sum_le _ _)
    _ ≤ ∑ n ∈ p.coeff.support,
        ∑ m ∈ q.coeff.support, (weight n*‖p.coeff n‖)*(weight m*‖q.coeff m‖) := by
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro m _
      rw [wnorm_single,norm_mul]
      calc _ ≤ (weight n*weight m)*(‖p.coeff n‖*‖q.coeff m‖) :=
              mul_le_mul_of_nonneg_right (weight_add_le n m) (by positivity)
        _ = _ := by ring
    _ = wnorm p*wnorm q := by simp only [wnorm,Finsupp.sum,Finset.sum_mul_sum]

noncomputable def ringNorm : RingNorm Poly where
  toFun := wnorm
  map_zero' := wnorm_zero
  add_le' := wnorm_add_le
  neg' := wnorm_neg
  mul_le' := wnorm_mul_le
  eq_zero_of_map_eq_zero' := fun _ => wnorm_eq_zero

noncomputable instance instNormedCommRingPoly : NormedCommRing Poly where
  toNormedRing := ringNorm.toNormedRing
  mul_comm := mul_comm

lemma norm_def (p : Poly) : ‖p‖ = wnorm p := rfl

lemma wnorm_smul (c : ℂ) (p : Poly) : wnorm (c • p) = ‖c‖*wnorm p := by
  unfold wnorm
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.sum_smul_index (by simp)]
  simp only [norm_mul,Finsupp.sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring

noncomputable instance instNormedAlgebraComplexPoly : NormedAlgebra ℂ Poly where
  toAlgebra := inferInstance
  norm_smul_le c p := (wnorm_smul c p).le

noncomputable instance instNormOneClassPoly : NormOneClass Poly where
  norm_one := by
    change wnorm (1 : Poly) = 1
    rw [AddMonoidAlgebra.one_def,wnorm_single]
    simp [weight]

abbrev Space := UniformSpace.Completion Poly

section Modes
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def modesLinear (v : ℤ → F) : Poly →ₗ[ℂ] F :=
  (Finsupp.linearCombination ℂ v).comp (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

lemma modesLinear_apply (v : ℤ → F) (p : Poly) :
    modesLinear v p = p.coeff.sum (fun n z => z • v n) := rfl

lemma modesLinear_bound (v : ℤ → F) {C : ℝ} (hv : ∀ n, ‖v n‖ ≤ C*weight n)
    (p : Poly) : ‖modesLinear v p‖ ≤ C*‖p‖ := by
  simp only [modesLinear_apply,norm_def,wnorm,Finsupp.sum,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_smul]
  calc ‖p.coeff n‖*‖v n‖ ≤ ‖p.coeff n‖*(C*weight n) :=
        mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _)
    _ = _ := by ring

def modesCLM (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) : Poly →L[ℂ] F :=
  (modesLinear v).mkContinuous C (modesLinear_bound v hv)

variable [CompleteSpace F]
def fromModes (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) : Space →L[ℂ] F :=
  (modesCLM v C hv).extend UniformSpace.Completion.toComplL

lemma fromModes_coe (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) (p : Poly) :
    fromModes v C hv (p : Space) = p.coeff.sum (fun n z => z • v n) :=
  (modesCLM v C hv).extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe Poly) p

lemma fromModes_bound (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) (f : Space) :
    ‖fromModes v C hv f‖ ≤ C*‖f‖ := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih p =>
    rw [fromModes_coe,UniformSpace.Completion.norm_coe]
    exact modesLinear_bound v hv p

lemma fromModes_single (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n)
    (n : ℤ) (z : ℂ) :
    fromModes v C hv ((AddMonoidAlgebra.single n z : Poly) : Space) = z • v n := by
  rw [fromModes_coe,AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)
end Modes

def boundary : Space →L[ℂ] C(Circle,ℂ) :=
  fromModes (fun n => fourier n) 1 (fun n => by simpa only [fourier_norm,one_mul] using one_le_weight n)

lemma boundary_coe (p : Poly) :
    boundary (p : Space) = p.coeff.sum (fun n z => z • fourier n) :=
  fromModes_coe _ _ _ _

lemma boundary_single (n : ℤ) (z : ℂ) :
    boundary ((AddMonoidAlgebra.single n z : Poly) : Space) = z • fourier n :=
  fromModes_single _ _ _ _ _

lemma boundary_norm_le (f : Space) : ‖boundary f‖ ≤ ‖f‖ := by
  simpa only [boundary,one_mul] using fromModes_bound (fun n => (fourier n : C(Circle,ℂ))) 1 (fun n => by simpa only [fourier_norm,one_mul] using one_le_weight n) f

lemma boundary_one : boundary 1 = 1 := by
  rw [← UniformSpace.Completion.coe_one]
  change boundary ((AddMonoidAlgebra.single 0 1 : Poly) : Space) = 1
  rw [boundary_single,one_smul]
  ext; exact fourier_zero

lemma boundary_poly_mul (p q : Poly) : boundary ((p*q : Poly) : Space) =
    boundary (p : Space)*boundary (q : Space) := by
  classical
  rw [AddMonoidAlgebra.mul_def]
  simp only [Finsupp.sum]
  change boundary ((UniformSpace.Completion.toComplL : Poly →L[ℂ] Space) (∑ a ∈ p.coeff.support,
    ∑ b ∈ q.coeff.support, AddMonoidAlgebra.single (a+b) (p.coeff a*q.coeff b))) = _
  simp only [map_sum]
  change (∑ a ∈ p.coeff.support, ∑ b ∈ q.coeff.support,
    boundary ((AddMonoidAlgebra.single (a+b) (p.coeff a*q.coeff b) : Poly) : Space)) = _
  simp_rw [boundary_single]
  rw [boundary_coe,boundary_coe]
  simp only [Finsupp.sum,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  ext θ
  simp only [ContinuousMap.smul_apply,smul_eq_mul,ContinuousMap.mul_apply,fourier_add]
  ring

lemma boundary_mul (f g : Space) : boundary (f*g) = boundary f*boundary g := by
  induction f,g using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p q => simpa only [← UniformSpace.Completion.coe_mul] using boundary_poly_mul p q

lemma poly_expansion (p : Poly) :
    (p : Space) = ∑ n ∈ p.coeff.support, ((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  change (UniformSpace.Completion.toComplL : Poly →L[ℂ] Space) (∑ n ∈ p.coeff.support,
    AddMonoidAlgebra.single n (p.coeff n)) = _
  exact map_sum _ _ _

def conjPoly : Poly →ₗ[ℝ] Poly :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap.comp
    ((Finsupp.lmapDomain ℂ ℝ (fun n : ℤ => -n)).comp
      ((Finsupp.mapRange.linearMap Complex.conjCLE.toLinearMap).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap))

lemma conjPoly_coeff (p : Poly) :
    (conjPoly p).coeff = (p.coeff.mapRange (starRingEnd ℂ) (map_zero _)).mapDomain (fun n => -n) := rfl

lemma conjPoly_single (n : ℤ) (z : ℂ) :
    conjPoly (.single n z) = .single (-n) (conj z) := by
  apply AddMonoidAlgebra.ext
  rw [conjPoly_coeff]
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.mapRange_single,Finsupp.mapDomain_single]

lemma conjPoly_norm (p : Poly) : ‖conjPoly p‖ = ‖p‖ := by
  change wnorm (conjPoly p) = wnorm p
  unfold wnorm
  rw [conjPoly_coeff,Finsupp.sum_mapDomain_index_inj (neg_injective : Function.Injective (fun n : ℤ => -n)),
    Finsupp.sum_mapRange_index (by simp)]
  simp [weight]

def conjugate : Space →L[ℝ] Space :=
  ((UniformSpace.Completion.toComplL : Poly →L[ℝ] Space).comp
    (conjPoly.mkContinuous 1 (by intro p; simp [conjPoly_norm]))).extend
      UniformSpace.Completion.toComplL

lemma conjugate_coe (p : Poly) : conjugate (p : Space) = (conjPoly p : Space) := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe Poly) p

lemma conjugate_single (n : ℤ) (z : ℂ) :
    conjugate ((AddMonoidAlgebra.single n z : Poly) : Space) =
      ((AddMonoidAlgebra.single (-n) (conj z) : Poly) : Space) := by
  rw [conjugate_coe,conjPoly_single]

lemma boundary_conjugate (f : Space) (θ : Circle) :
    boundary (conjugate f) θ = conj (boundary f θ) := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,conjugate_single,boundary_single,ContinuousMap.sum_apply,
      ContinuousMap.smul_apply,smul_eq_mul,map_mul]
    apply Finset.sum_congr rfl
    intro _ _
    rw [fourier_neg]

def multiplier (σ : ℤ → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C) : Space →L[ℂ] Space :=
  fromModes (fun n => ((AddMonoidAlgebra.single n (σ n) : Poly) : Space)) C (by
    intro n
    rw [UniformSpace.Completion.norm_coe,norm_def,wnorm_single]
    calc weight n*‖σ n‖ ≤ weight n*C := mul_le_mul_of_nonneg_left (hσ n) (weight_pos n).le
      _ = C*weight n := mul_comm _ _)

lemma multiplier_single (σ : ℤ → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C) (n : ℤ) (z : ℂ) :
    multiplier σ C hσ ((AddMonoidAlgebra.single n z : Poly) : Space) =
      ((AddMonoidAlgebra.single n (z*σ n) : Poly) : Space) := by
  rw [multiplier,fromModes_single]
  rw [← UniformSpace.Completion.coe_smul]
  congr 1
  apply AddMonoidAlgebra.ext
  ext m
  simp only [AddMonoidAlgebra.coeff_smul,AddMonoidAlgebra.coeff_single,Finsupp.smul_apply,
    Finsupp.single_apply,smul_eq_mul]
  split_ifs <;> simp_all

lemma multiplier_bound (σ : ℤ → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C) (f : Space) :
    ‖multiplier σ C hσ f‖ ≤ C*‖f‖ := fromModes_bound _ _ _ _

def hilbert : Space →L[ℂ] Space := multiplier hilbertSymbol 1 hilbertSymbol_bound

lemma hilbert_norm (f : Space) : ‖hilbert f‖ ≤ ‖f‖ := by
  simpa only [hilbert,one_mul] using multiplier_bound hilbertSymbol 1 hilbertSymbol_bound f

lemma hilbert_conjugate (f : Space) : hilbert (conjugate f) = conjugate (hilbert f) := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,conjugate_single,hilbert,multiplier_single]
    apply Finset.sum_congr rfl
    intro _ _
    rw [hilbertSymbol_neg,map_mul]

def realSubspace : Submodule ℝ Space := LinearMap.ker (conjugate.toLinearMap-LinearMap.id)

lemma mem_realSubspace {f : Space} : f ∈ realSubspace ↔ conjugate f = f := by
  simp [realSubspace,sub_eq_zero]

lemma real_boundary {f : Space} (hf : f ∈ realSubspace) (θ : Circle) : (boundary f θ).im = 0 := by
  have h := boundary_conjugate f θ
  rw [mem_realSubspace.mp hf] at h
  exact (Complex.conj_eq_iff_im).mp h.symm

def schwarz : Space →L[ℂ] C(ClosedDisc,ℂ) :=
  fromModes schwarzModeC 3 (by
    intro n
    apply ((schwarzModeC n).norm_le (mul_nonneg (by norm_num) (weight_pos n).le)).mpr
    intro z
    apply (schwarzMode_bound n (by simpa only [ClosedDisc,Metric.mem_closedBall,dist_zero_right] using z.property)).trans
    simpa using (mul_le_mul_of_nonneg_left (one_le_weight n) (by norm_num : (0:ℝ) ≤ 3)))

def discValue (f : Space) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ ClosedDisc then schwarz f ⟨z,hz⟩ else 0

def polyDisc (p : Poly) (z : ℂ) : ℂ := p.coeff.sum (fun n c => c*schwarzMode n z)

lemma single_mul (n m : ℤ) (z w : ℂ) :
    ((AddMonoidAlgebra.single n z : Poly) : Space) *
      ((AddMonoidAlgebra.single m w : Poly) : Space) =
        ((AddMonoidAlgebra.single (n+m) (z*w) : Poly) : Space) := by
  rw [← UniformSpace.Completion.coe_mul,AddMonoidAlgebra.single_mul_single]

lemma conjugate_mul (f g : Space) : conjugate (f*g) = conjugate f*conjugate g := by
  induction f,g using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p q =>
    rw [poly_expansion p,poly_expansion q]
    simp only [Finset.sum_mul_sum,map_sum,conjugate_single,single_mul]
    apply Finset.sum_congr rfl
    intro _ _
    apply Finset.sum_congr rfl
    intro _ _
    rw [neg_add,map_mul]

lemma conjugate_one : conjugate (1 : Space) = 1 := by
  rw [← UniformSpace.Completion.coe_one]
  change conjugate ((AddMonoidAlgebra.single 0 1 : Poly) : Space) =
    ((AddMonoidAlgebra.single 0 1 : Poly) : Space)
  rw [conjugate_single,neg_zero,map_one]

lemma conjugate_real (r : ℝ) : conjugate (algebraMap ℝ Space r) = algebraMap ℝ Space r := by
  rw [Algebra.algebraMap_eq_smul_one,map_smul,conjugate_one]

def realAlgebra : Subalgebra ℝ Space where
  carrier := {f | conjugate f = f}
  mul_mem' hf hg := by rw [Set.mem_ofPred_eq,conjugate_mul,hf,hg]
  add_mem' hf hg := by rw [Set.mem_ofPred_eq,map_add,hf,hg]
  algebraMap_mem' := conjugate_real
  zero_mem' := map_zero _
  one_mem' := conjugate_one

noncomputable instance instNormOneClassSpace : NormOneClass Space where
  norm_one := by
    rw [← UniformSpace.Completion.coe_one Poly,UniformSpace.Completion.norm_coe]
    exact norm_one

noncomputable instance instNormOneClassSubtypeSpaceMemSubalgebraRealRealAlgebra : NormOneClass realAlgebra where
  norm_one := by change ‖(1 : Space)‖ = 1; exact norm_one

lemma realAlgebra_mem_subspace (f : realAlgebra) : (f : Space) ∈ realSubspace :=
  mem_realSubspace.mpr f.property

lemma realAlgebra_boundary_im (f : realAlgebra) (θ : Circle) : (boundary f θ).im = 0 :=
  real_boundary (realAlgebra_mem_subspace f) θ

def realEvaluation (θ : Circle) : realAlgebra →ₐ[ℝ] ℝ where
  toFun f := (boundary f θ).re
  map_zero' := by simp
  map_one' := by simp [boundary_one]
  map_add' f g := by simp
  map_mul' f g := by simp [boundary_mul,Complex.mul_re,realAlgebra_boundary_im]
  commutes' r := by
    change (boundary (algebraMap ℝ Space r) θ).re = r
    rw [Algebra.algebraMap_eq_smul_one]
    have hb : boundary (r • (1 : Space)) = r • (1 : C(Circle,ℂ)) := by
      have h := (boundary.restrictScalars ℝ).map_smul r 1
      change boundary (r • (1 : Space)) = r • boundary 1 at h
      simpa only [boundary_one] using h
    rw [hb]
    simp

lemma realEvaluation_bound (θ : Circle) (f : realAlgebra) : |realEvaluation θ f| ≤ ‖f‖ := by
  exact (Complex.abs_re_le_norm _).trans
    (((boundary (f : Space)).norm_coe_le_norm θ).trans (boundary_norm_le f))

def realEvaluationCLM (θ : Circle) : realAlgebra →L[ℝ] ℝ :=
  (realEvaluation θ).toLinearMap.mkContinuous 1 (by
    intro f
    change |realEvaluation θ f| ≤ 1*‖f‖
    simpa only [one_mul] using realEvaluation_bound θ f)

def realHilbert : realAlgebra →L[ℝ] realAlgebra :=
  ({ toFun f := ⟨hilbert f,by
        change conjugate (hilbert f) = hilbert f
        rw [← hilbert_conjugate,f.property]⟩
     map_add' f g := by ext; exact map_add hilbert _ _
     map_smul' c f := by ext; exact (hilbert.restrictScalars ℝ).map_smul c f } :
    realAlgebra →ₗ[ℝ] realAlgebra).mkContinuous 1 (by
      intro f
      change ‖hilbert (f : Space)‖ ≤ 1*‖(f : Space)‖
      simpa only [one_mul] using hilbert_norm (f : Space))

def constantReal : ℝ →L[ℝ] realAlgebra :=
  (Algebra.linearMap ℝ realAlgebra).mkContinuous 1 (by
    intro r
    simp [Algebra.linearMap_apply,Algebra.algebraMap_eq_smul_one])

def normalizedHilbert : realAlgebra →L[ℝ] realAlgebra :=
  realHilbert-constantReal.comp ((realEvaluationCLM 0).comp realHilbert)

open MeasureTheory

def coeff (n : ℤ) : Space →L[ℂ] ℂ := (fourierCLM n).comp boundary

def cutoff (s : Finset ℤ) : Space →L[ℂ] Space :=
  fromModes (fun n => if n ∈ s then ((AddMonoidAlgebra.single n 1 : Poly) : Space) else 0) 1 (by
    intro n
    split_ifs
    · rw [UniformSpace.Completion.norm_coe,norm_def,wnorm_single]
      simp
    · simpa only [norm_zero,one_mul] using (weight_pos n).le)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ActionAutomorphismHomRange
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology TopologicalSpace
open scoped Classical

theorem bounded_divisible_automorphism_locallyCompact {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    LocallyCompactSpace (Biholomorph U U) := by
  have hp := bounded_divisible_automorphism_evaluation_proper hU hc hb Γ hhol p
  let : WeaklyLocallyCompactSpace (Biholomorph U U) := ⟨fun a => by
    obtain ⟨K,hK,hKa⟩ := exists_compact_mem_nhds (a.toHomeomorph p)
    exact ⟨_,hp.isCompact_preimage hK,hp.continuous.continuousAt.preimage_mem_nhds hKa⟩⟩
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def actionAutomorphismHom {n : ℕ} (U : Set (Affine n))
    (Γ : Type*) [Group Γ] [MulAction Γ U] [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    Γ →* Biholomorph U U where
  toFun := actionBiholomorph U Γ hhol
  map_one' := by apply Biholomorph.ext; intro x; exact one_smul Γ x
  map_mul' a b := by apply Biholomorph.ext; intro x; exact mul_smul a b x

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticMulZeroGerm
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def analyticGermConst : ℂ →+* AnalyticGerm E where
  toFun c := ⟨Filter.Germ.const c,⟨fun _ => c,analyticAt_const,rfl⟩⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

noncomputable instance instAlgebraComplexSubtypeGermNhdsOfNatMemSubringAnalyticGerm : Algebra ℂ (AnalyticGerm E) :=
  (analyticGermConst E).toAlgebra

instance instNontrivialSubtypeGermNhdsOfNatComplexMemSubringAnalyticGerm : Nontrivial (AnalyticGerm E) := by
  exact ⟨⟨0,1,fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩

instance instNoZeroDivisorsSubtypeGermNhdsOfNatComplexMemSubringAnalyticGerm : NoZeroDivisors (AnalyticGerm E) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    rintro ⟨a,f,hf,rfl⟩ ⟨b,g,hg,rfl⟩ hab
    have hfg : f*g =ᶠ[𝓝 (0 : E)] 0 := Filter.Germ.coe_eq.mp (congrArg Subtype.val hab)
    rcases analyticAt_mul_eq_zero_germ E hf hg hfg with h | h
    · exact Or.inl (Subtype.ext (Filter.Germ.coe_eq.mpr h))
    · exact Or.inr (Subtype.ext (Filter.Germ.coe_eq.mpr h))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticDirectionalDerivationFun
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def analyticDirectionalDerivative (v : E) : AnalyticGerm E → AnalyticGerm E :=
  fun g => ⟨germDirectionalDerivative E v g.val,by
    obtain ⟨f,hf,he⟩ := g.property
    refine ⟨fun x => fderiv ℂ f x v,?_,?_⟩
    · exact ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hf.fderiv
    · rw [← he]; rfl⟩

noncomputable def analyticDirectionalDerivation (v : E) :
    Derivation ℂ (AnalyticGerm E) (AnalyticGerm E) where
  toFun := analyticDirectionalDerivative E v
  map_add' := by
    rintro ⟨_,f,hf,rfl⟩ ⟨_,g,hg,rfl⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    change (fun x => fderiv ℂ (f+g) x v) =ᶠ[𝓝 (0:E)] (fun x => fderiv ℂ f x v + fderiv ℂ g x v)
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with x hfx hgx
    simp only [fderiv_add hfx.differentiableAt hgx.differentiableAt,
      add_apply]
  map_smul' := by
    intro c
    rintro ⟨_,f,hf,rfl⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    change (fun x => fderiv ℂ (c • f) x v) =ᶠ[𝓝 (0:E)] (fun x => c • fderiv ℂ f x v)
    filter_upwards [hf.eventually_analyticAt] with x hfx
    simp only [fderiv_const_smul hfx.differentiableAt,
      smul_apply]
  map_one_eq_zero' := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun x => by simp
  leibniz' := by
    rintro ⟨_,f,hf,rfl⟩ ⟨_,g,hg,rfl⟩
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    change (fun x => fderiv ℂ (f*g) x v) =ᶠ[𝓝 (0:E)] (fun x => f x * fderiv ℂ g x v + g x * fderiv ℂ f x v)
    filter_upwards [hf.eventually_analyticAt,hg.eventually_analyticAt] with x hfx hgx
    simp only [fderiv_mul hfx.differentiableAt hgx.differentiableAt,
      add_apply,smul_apply,smul_eq_mul]

abbrev MeromorphicGermField := FractionRing (AnalyticGerm E)

noncomputable def analyticGermOf (f : E → ℂ) (hf : AnalyticAt ℂ f 0) : AnalyticGerm E :=
  ⟨(f : Filter.Germ (𝓝 (0 : E)) ℂ),⟨f,hf,rfl⟩⟩

@[simp] theorem analyticGermOf_eq_iff (f g : E → ℂ)
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    analyticGermOf E f hf = analyticGermOf E g hg ↔ f =ᶠ[𝓝 (0:E)] g := by
  exact Subtype.ext_iff.trans Filter.Germ.coe_eq

@[simp] theorem analyticDirectionalDerivation_ofFun (v : E)
    (f : E → ℂ) (hf : AnalyticAt ℂ f 0) :
    analyticDirectionalDerivation E v (analyticGermOf E f hf) =
      analyticGermOf E (fun x => fderiv ℂ f x v)
        (((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hf.fderiv) := rfl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EtaleDerivationExtensionUnique
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology
variable {n : ℕ}

noncomputable def analyticCoordinate (i : Fin n) : AnalyticGerm (Fin n → ℂ) :=
  analyticGermOf _ (fun x => x i) ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt _)

end

open Algebra KaehlerDifferential
open scoped TensorProduct

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AlgebraicIndependentNashPartials
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology Algebra KaehlerDifferential
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def meromorphicDirectionalDerivation (v : E) :
    Derivation ℂ (MeromorphicGermField E) (MeromorphicGermField E) := by
  let A := AnalyticGerm E
  let K := MeromorphicGermField E
  letI : Algebra.FormallyEtale A K :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := K) (nonZeroDivisors A)
  exact etaleDerivationExtension ℂ A K
    ((Algebra.linearMap A K).compDer (analyticDirectionalDerivation E v))

@[simp] theorem meromorphicDirectionalDerivation_algebraMap (v : E) (a : AnalyticGerm E) :
    meromorphicDirectionalDerivation E v (algebraMap (AnalyticGerm E) (MeromorphicGermField E) a) =
      algebraMap (AnalyticGerm E) (MeromorphicGermField E)
        (analyticDirectionalDerivation E v a) := by
  exact etaleDerivationExtension_algebraMap ℂ _ _ _ a

@[simp] theorem analyticDirectionalDerivation_coordinate {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    analyticDirectionalDerivation (Fin n → ℂ) v (analyticCoordinate i) =
      algebraMap ℂ (AnalyticGerm (Fin n → ℂ)) (v i) := by
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun x => by
    change fderiv ℂ (fun z : Fin n → ℂ => z i) x v = v i
    exact congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L v)
      (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).hasFDerivAt.fderiv

noncomputable def meromorphicCoordinate {n : ℕ} (i : Fin n) :
    MeromorphicGermField (Fin n → ℂ) :=
  algebraMap (AnalyticGerm (Fin n → ℂ)) (MeromorphicGermField (Fin n → ℂ)) (analyticCoordinate i)

@[simp] theorem meromorphicDirectionalDerivation_coordinate {n : ℕ}
    (v : Fin n → ℂ) (i : Fin n) :
    meromorphicDirectionalDerivation (Fin n → ℂ) v (meromorphicCoordinate i) =
      algebraMap ℂ (MeromorphicGermField (Fin n → ℂ)) (v i) := by
  simp only [meromorphicCoordinate,meromorphicDirectionalDerivation_algebraMap,
    analyticDirectionalDerivation_coordinate,←IsScalarTower.algebraMap_apply]

end

open Set Algebra KaehlerDifferential _root_.Module
open scoped IntermediateField.algebraAdjoinAdjoin

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticNashRank
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology

noncomputable def meromorphicGermOf {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : E → ℂ) (hf : AnalyticAt ℂ f 0) : MeromorphicGermField E :=
  algebraMap (AnalyticGerm E) (MeromorphicGermField E) (analyticGermOf E f hf)

@[simp] theorem meromorphicGermOf_eq_zero_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : E → ℂ) (hf : AnalyticAt ℂ f 0) :
    meromorphicGermOf f hf = 0 ↔ f =ᶠ[𝓝 (0:E)] 0 := by
  rw [meromorphicGermOf, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact (analyticGermOf_eq_iff E f 0 hf analyticAt_const)

noncomputable def meromorphicPartial {n : ℕ} (i : Fin n) :
    Derivation ℂ (MeromorphicGermField (Fin n → ℂ)) (MeromorphicGermField (Fin n → ℂ)) :=
  meromorphicDirectionalDerivation _ (Pi.single i 1)

@[simp] theorem meromorphicPartial_coordinate {n : ℕ} (i j : Fin n) :
    meromorphicPartial i (meromorphicCoordinate j) = if j = i then 1 else 0 := by
  rw [meromorphicPartial,meromorphicDirectionalDerivation_coordinate]
  by_cases h : j = i
  · subst j; simp
  · simp [h]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopBoundarySolution
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter

namespace Release061.Wiener

abbrev BoundarySpace (k : ℕ) := Fin k → realAlgebra

def bishopInput {k : ℕ} (lam : realAlgebra) :
    (BishopParams k × BoundarySpace k) →L[ℝ] (Fin (k+1) → realAlgebra) :=
  ContinuousLinearMap.pi (fun j => Fin.cases
    ((ContinuousLinearMap.smulRight
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) (ℝ × ℝ)).comp
          ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) ((Fin k → ℝ) × ℝ × ℝ)).comp
            (ContinuousLinearMap.fst ℝ (BishopParams k) (BoundarySpace k))))) lam) +
      constantReal.comp
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) (ℝ × ℝ)).comp
          ((ContinuousLinearMap.snd ℝ (Fin k → ℝ) ((Fin k → ℝ) × ℝ × ℝ)).comp
            (ContinuousLinearMap.fst ℝ (BishopParams k) (BoundarySpace k))))))
    (fun i => (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℝ (BishopParams k) (BoundarySpace k))) j)

def bishopRHS {k : ℕ} (lam η : realAlgebra)
    (F : (Fin (k+1) → realAlgebra) → BoundarySpace k)
    (q : BishopParams k × BoundarySpace k) : BoundarySpace k :=
  fun i => constantReal (q.1.1 i) + normalizedHilbert (F (bishopInput lam q) i + q.1.2.1 i • η)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopAnalyticDiscs
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter

namespace Release061.Wiener

def realSchwarz : realAlgebra →L[ℝ] C(ClosedDisc,ℂ) :=
  (schwarz.restrictScalars ℝ).comp realAlgebra.toSubmodule.subtypeL

def bishopDisc {k : ℕ} (Y : BishopParams k → BoundarySpace k)
    (p : BishopParams k) (i : Fin k) : C(ClosedDisc,ℂ) :=
  constantDisc (p.1 i)+realSchwarz (Y p i)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SchwarzRadialExpansion
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

def vanishingFactor : Space := 2-((AddMonoidAlgebra.single 1 1 : Poly) : Space)-
  ((AddMonoidAlgebra.single (-1) 1 : Poly) : Space)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_TransverseCutoffs
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener

lemma vanishingFactor_real : conjugate vanishingFactor = vanishingFactor := by
  have h2 : conjugate (2 : Space) = 2 := by
    rw [show (2 : Space) = 1+1 by ring,map_add,conjugate_one]
  simp only [vanishingFactor,map_sub,h2,conjugate_single,map_one,neg_neg]
  ring

def vanishingReal : realAlgebra := ⟨vanishingFactor,vanishingFactor_real⟩

def realMean : realAlgebra →L[ℝ] ℝ :=
  Complex.reCLM.comp (((coeff 0).restrictScalars ℝ).comp realAlgebra.toSubmodule.subtypeL)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BishopNormalZeroDeformation
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
namespace Release061.Wiener
open scoped Topology
open Set Filter

def bishopNormal {k : ℕ} (κ : realAlgebra) (Y : BishopParams k → BoundarySpace k)
    (p : BishopParams k) : Fin k → ℝ := fun i => 2*realMean (κ*Y p i)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CayleyTangentBound
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Complex Set Filter Metric
open scoped Topology

lemma normalCayley_sub_one {u : ℂ} (hu : u+I ≠ 0) :
    1-normalCayley u = 2*I/(u+I) := by
  simp only [normalCayley]
  field_simp
  ring

lemma normalCayley_ne_one {u : ℂ} (hu : u+I ≠ 0) : normalCayley u ≠ 1 := by
  have hh : 1-normalCayley u ≠ 0 := by
    rw [normalCayley_sub_one hu]
    exact div_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hu
  exact fun h => hh (by rw [h,sub_self])

lemma normalUncayley_add_I {v : ℂ} (hv : 1-v ≠ 0) :
    normalUncayley v+I = 2*I/(1-v) := by
  simp only [normalUncayley]
  field_simp
  ring

lemma normalUncayley_add_I_ne_zero {v : ℂ} (hv : 1-v ≠ 0) :
    normalUncayley v+I ≠ 0 := by
  rw [normalUncayley_add_I hv]
  exact div_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hv

lemma normalUncayley_cayley {u : ℂ} (hu : u+I ≠ 0) :
    normalUncayley (normalCayley u) = u := by
  rw [normalUncayley,normalCayley_sub_one hu,normalCayley]
  field_simp
  ring

lemma normalCayley_uncayley {v : ℂ} (hv : 1-v ≠ 0) :
    normalCayley (normalUncayley v) = v := by
  rw [normalCayley,normalUncayley_add_I hv,normalUncayley]
  field_simp
  ring

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteCoveringRamifiedSection
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Function

open Complex
open scoped UpperHalfPlane
open Function.Periodic

instance instTopologicalSpacePuncturedUnitDisk : TopologicalSpace PuncturedUnitDisk := inferInstanceAs (TopologicalSpace {z : ℂ // z ≠ 0 ∧ ‖z‖ < 1})

noncomputable def halfPlaneQ (h : ℝ) (hh : 0 < h) (z : ℍ) : PuncturedUnitDisk :=
  ⟨qParam h z,qParam_ne_zero (h := h) z,norm_qParam_lt_one hh z.im_pos⟩

noncomputable def halfPlaneInvQ (h : ℝ) (hh : 0 < h) (q : PuncturedUnitDisk) : ℍ :=
  ⟨invQParam h q.val,by
    apply (norm_qParam_lt_iff hh 0 _).mp
    simpa only [qParam_right_inv hh.ne' q.property.1,mul_zero,zero_div,Real.exp_zero] using q.property.2⟩

noncomputable def puncturedPower (l : ℕ) (hl : 0 < l) (q : PuncturedUnitDisk) :
    PuncturedUnitDisk :=
  ⟨q.val^l,pow_ne_zero l q.property.1,by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) q.property.2 hl.ne'⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialRamifiedAnalyticRoot
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Filter Set Complex UpperHalfPlane Function
open scoped Topology
instance instT2SpacePuncturedUnitDisk : T2Space PuncturedUnitDisk := inferInstanceAs (T2Space {z : ℂ // z ≠ 0 ∧ ‖z‖ < 1})

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocalBishopData
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.radiusCircleCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

structure LocalBishopData (k : ℕ) (f : (Fin (k+1) → ℝ) → Fin k → ℝ) (ε : ℝ) where
  lam : realAlgebra
  eta : realAlgebra
  kappa : realAlgebra
  X : BishopParams k → BoundarySpace k
  Y : BishopParams k → BoundarySpace k
  radius : ℝ
  radius_pos : 0 < radius
  cut_nonneg : ∀ θ, 0 ≤ realEvaluation θ lam ∧ 0 ≤ realEvaluation θ eta
  cut_zero : ∀ θ, (1/2 : ℝ) ≤ dist (circleCos θ) (-1 : ℝ) →
    realEvaluation θ lam = 0 ∧ realEvaluation θ eta = 0
  cut_nested : ∀ θ, realEvaluation θ eta ≠ 0 → realEvaluation θ lam = 1
  cut_division : ∀ θ, dist (circleCos θ) (-1 : ℝ) ≤ 1/2 →
    (2-2*circleCos θ)*realEvaluation θ kappa = 1
  smoothX : ContDiffOn ℝ 1 X (ball 0 radius)
  smoothY : ContDiffOn ℝ 1 Y (ball 0 radius)
  small : ∀ p ∈ ball 0 radius, ‖X p‖ < ε ∧ ‖Y p‖ < ε ∧ ‖bishopDisc Y p‖ < ε
  equation : ∀ p ∈ ball 0 radius,
    (∀ i, X p i = constantReal (p.1 i)+normalizedHilbert (Y p i)) ∧
    (∀ θ i, realEvaluation θ (Y p i) =
      f (Fin.cons (p.2.2.1*realEvaluation θ lam+p.2.2.2)
        (fun j => realEvaluation θ (X p j))) i+realEvaluation θ eta*p.2.1 i)
  localized : ∀ p ∈ ball 0 radius, p.2.2.2 = 0 →
    ∀ θ, (1/2 : ℝ) < dist (circleCos θ) (-1 : ℝ) →
      ∀ i, realEvaluation θ (Y p i) = 0
  constant : ∀ q ∈ ball (0 : (Fin k → ℝ) × ℝ) radius, ∀ i (z : ClosedDisc),
    bishopDisc Y (q.1,0,0,q.2) i z =
      (q.1 i : ℂ)+Complex.I*(f (Fin.cons q.2 q.1) i : ℂ)
  transverse : ∀ᶠ α in 𝓝 (0 : ℝ), IsUnit
    (fderiv ℝ (fun e : Fin k → ℝ => bishopNormal kappa Y (0,e,α,0)) 0)

end Release061.Wiener

open Set Metric

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledRadialOperatorApply
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

def schwarzDifference {k : ℕ} (z : ClosedDisc) : BoundarySpace k →L[ℝ] (Fin k → ℂ) :=
  ContinuousLinearMap.pi (fun i =>
    (((ContinuousMap.evalCLM ℝ (M := ℂ) z)-(ContinuousMap.evalCLM ℝ (M := ℂ) (⟨0,by simp [ClosedDisc]⟩ : ClosedDisc))).comp
      realSchwarz).comp (ContinuousLinearMap.proj i))

def scaledRadialOperator {k : ℕ} (t : ℝ) : BoundarySpace k →L[ℝ] (Fin k → ℂ) :=
  (-(t/(1-t))) • schwarzDifference (radialPoint t)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledModelC1Limit
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

def normalSlice {k : ℕ} (κ : realAlgebra) (Y : RealDiscParams k → BoundarySpace k)
    (q : RealDiscParams k) : Fin k → ℝ := fun i => 2*realMean (κ*Y q i)

def discSlice {k : ℕ} (Y : RealDiscParams k → BoundarySpace k)
    (q : RealDiscParams k) (i : Fin k) : C(ClosedDisc,ℂ) :=
  constantDisc (q.1 i)+realSchwarz (Y q i)

def scaledModel {k : ℕ} (κ : realAlgebra) (Y : RealDiscParams k → BoundarySpace k)
    (t : ℝ) (q : RealDiscParams k) : Fin k → ℂ :=
  (fun i => (q.1 i : ℂ)+Complex.I*(normalSlice κ Y (t • q.1,q.2) i : ℂ))+
    scaledRadialOperator t (fun i => κ*Y (t • q.1,q.2) i)

def limitModel {k : ℕ} (κ : realAlgebra) (Y : RealDiscParams k → BoundarySpace k)
    (q : RealDiscParams k) : Fin k → ℂ :=
  fun i => (q.1 i : ℂ)+Complex.I*(normalSlice κ Y (0,q.2) i : ℂ)

def scaledDisc {k : ℕ} (Y : RealDiscParams k → BoundarySpace k)
    (t : ℝ) (q : RealDiscParams k) : Fin k → ℂ :=
  t⁻¹ • fun i => discSlice Y (t • q.1,q.2) i (radialPoint t)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledDiscDeltaC1
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

def regularizedSlice {k : ℕ} (Y : BishopParams k → BoundarySpace k) (α δ : ℝ)
    (q : RealDiscParams k) : BoundarySpace k := Y (q.1,q.2,α,δ)

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_VerticalPieceBasePolynomial
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

def verticalPieceSet {r : ℕ} (v : Fin r → ℝ) : VerticalPiece r → Set ℝ
  | .inl i => {v i}
  | .inr (none,none) => univ
  | .inr (some i,none) => Ioi (v i)
  | .inr (none,some j) => Iio (v j)
  | .inr (some i,some j) => Ioo (v i) (v j)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GeneratorPushForwardLinear
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

variable (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

def generatorPushForwardLinear (q : Biholomorph U U) :
    completeGeneratorSpace hU hc hbd Γ hhol →ₗ[ℝ] completeGeneratorSpace hU hc hbd Γ hhol where
  toFun X := ⟨pushForwardGenerator q X.val,X.property.pushForward hU hbd q⟩
  map_add' X Y := by
    apply Subtype.ext
    funext x
    by_cases hx : x∈U
    · simp only [pushForwardGenerator,dite_eq_left hx,Submodule.coe_add,Pi.add_apply,map_add]
    · simp only [pushForwardGenerator,dite_eq_right hx,Submodule.coe_add,Pi.add_apply,add_zero]
  map_smul' c X := by
    apply Subtype.ext
    funext x
    by_cases hx : x∈U
    · simp only [pushForwardGenerator,dite_eq_left hx,Submodule.coe_smul,Pi.smul_apply,ContinuousLinearMap.map_smul_of_tower,RingHom.id_apply]
    · simp only [pushForwardGenerator,dite_eq_right hx,Submodule.coe_smul,Pi.smul_apply,smul_zero]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CompleteGeneratorLieAlgebra
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

instance completeGeneratorLieRing : LieRing (completeGeneratorSpace hU hc hbd Γ hhol) where
  bracket := completeGeneratorBracket hU hc hbd Γ hhol
  add_lie X Y Z := by
    apply Subtype.ext
    funext x
    change VectorField.lieBracket ℂ (X.val+Y.val) Z.val x =
      VectorField.lieBracket ℂ X.val Z.val x + VectorField.lieBracket ℂ Y.val Z.val x
    by_cases hx : x∈U
    · exact VectorField.lieBracket_add_left ((X.property.analyticOnNhd hU hbd) x hx).differentiableAt
        ((Y.property.analyticOnNhd hU hbd) x hx).differentiableAt
    · simp only [VectorField.lieBracket,Pi.add_apply,X.property.eq_zero_of_not_mem hx,
        Y.property.eq_zero_of_not_mem hx,Z.property.eq_zero_of_not_mem hx,add_zero,map_zero,sub_zero]
  lie_add X Y Z := by
    apply Subtype.ext
    funext x
    change VectorField.lieBracket ℂ X.val (Y.val+Z.val) x =
      VectorField.lieBracket ℂ X.val Y.val x + VectorField.lieBracket ℂ X.val Z.val x
    by_cases hx : x∈U
    · exact VectorField.lieBracket_add_right ((Y.property.analyticOnNhd hU hbd) x hx).differentiableAt
        ((Z.property.analyticOnNhd hU hbd) x hx).differentiableAt
    · simp only [VectorField.lieBracket,Pi.add_apply,X.property.eq_zero_of_not_mem hx,
        Y.property.eq_zero_of_not_mem hx,Z.property.eq_zero_of_not_mem hx,add_zero,map_zero,sub_zero]
  lie_self X := by
    apply Subtype.ext
    exact VectorField.lieBracket_self
  leibniz_lie X Y Z := by
    apply Subtype.ext
    funext x
    change VectorField.lieBracket ℂ X.val (VectorField.lieBracket ℂ Y.val Z.val) x =
      VectorField.lieBracket ℂ (VectorField.lieBracket ℂ X.val Y.val) Z.val x +
      VectorField.lieBracket ℂ Y.val (VectorField.lieBracket ℂ X.val Z.val) x
    by_cases hx : x∈U
    · exact VectorField.leibniz_identity_lieBracket (le_top : minSmoothness ℂ 2 ≤ ⊤)
        ((X.property.analyticOnNhd hU hbd) x hx).contDiffAt
        ((Y.property.analyticOnNhd hU hbd) x hx).contDiffAt
        ((Z.property.analyticOnNhd hU hbd) x hx).contDiffAt
    · simp only [VectorField.lieBracket,X.property.eq_zero_of_not_mem hx,
        Y.property.eq_zero_of_not_mem hx,Z.property.eq_zero_of_not_mem hx,map_zero,sub_zero,add_zero]

instance completeGeneratorLieAlgebra : LieAlgebra ℝ (completeGeneratorSpace hU hc hbd Γ hhol) where
  lie_smul c X Y := by
    apply Subtype.ext
    funext x
    change VectorField.lieBracket ℂ X.val (c • Y.val) x = c • VectorField.lieBracket ℂ X.val Y.val x
    by_cases hx : x∈U
    · simp only [VectorField.lieBracket,Pi.smul_apply,
        fderiv_const_smul ((Y.property.analyticOnNhd hU hbd) x hx).differentiableAt,
        smul_apply,ContinuousLinearMap.map_smul_of_tower,smul_sub]
    · simp only [VectorField.lieBracket,Pi.smul_apply,X.property.eq_zero_of_not_mem hx,
        Y.property.eq_zero_of_not_mem hx,smul_zero,map_zero,sub_zero]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ComplexificationRankLeReal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Matrix _root_.Module _root_.Matrix.Module

@[simp] theorem meromorphicPartial_germ {n : ℕ}
    (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) (i : Fin n) :
    meromorphicPartial i (meromorphicGermOf f hf) =
      meromorphicGermOf (fun z => fderiv ℂ f z (Pi.single i 1))
        (((ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ) : Fin n → ℂ)).analyticAt _).comp hf.fderiv) := by
  simp only [meromorphicPartial,meromorphicGermOf,meromorphicDirectionalDerivation_algebraMap,
    analyticDirectionalDerivation_ofFun]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_WeightedChartTwoSided
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology
variable {E F S V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def chartScaledDomain (e : OpenPartialHomeomorph (E × F) (S × V))
    (A : S → Set V) (t : ℝ) : Set (E × F) :=
  {x | weightedScale t x ∈ e.source ∧
    (e (weightedScale t x)).2 ∈ A (e (weightedScale t x)).1}

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ForwardBackwardGerm
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

noncomputable def domain (s : NashBoundaryScalingChart c x) (t : ℝ) :
    Set (Affine s.tangentDim × Affine s.normalDim) :=
  {z | weightedScale t z ∈ s.offsets.source ∧ s.forward (weightedScale t z) ∈ U}

end NashBoundaryScalingChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GeneratorAdjointHom
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
include hU

theorem pushForwardGenerator_mul (q r : Biholomorph U U) (X : Affine n → Affine n) :
    pushForwardGenerator (q*r) X=pushForwardGenerator q (pushForwardGenerator r X) := by
  funext x
  by_cases hx : x∈U
  · rw [pushForwardGenerator_apply (q*r) X ⟨x,hx⟩,
      pushForwardGenerator_apply q (pushForwardGenerator r X) ⟨x,hx⟩]
    rw [pushForwardGenerator_apply,derivativeAt_mul hU]
    have he : (q*r).toHomeomorph.symm ⟨x,hx⟩=
        r.toHomeomorph.symm (q.toHomeomorph.symm ⟨x,hx⟩) := rfl
    rw [he,Homeomorph.apply_symm_apply]
    rfl
  · simp only [pushForwardGenerator,dite_eq_right hx]

theorem pushForwardGenerator_one {X : Affine n → Affine n} (hX : ∀ x∉U, X x=0) :
    pushForwardGenerator (1 : Biholomorph U U) X=X := by
  funext x
  by_cases hx : x∈U
  · rw [pushForwardGenerator_apply (1 : Biholomorph U U) X ⟨x,hx⟩]
    change (1 : Biholomorph U U).derivativeAt ⟨x,hx⟩ (X x)=X x
    rw [derivativeAt_one hU]
    rfl
  · simp only [pushForwardGenerator,dite_eq_right hx,hX x hx]

variable [LocallyCompactSpace U] (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

def generatorAdjoint (q : Biholomorph U U) :
    completeGeneratorSpace hU hc hbd Γ hhol ≃ₗ[ℝ] completeGeneratorSpace hU hc hbd Γ hhol where
  toLinearMap := generatorPushForwardLinear hU hc hbd Γ hhol q
  invFun := generatorPushForwardLinear hU hc hbd Γ hhol q⁻¹
  left_inv X := by
    apply Subtype.ext
    change pushForwardGenerator q⁻¹ (pushForwardGenerator q X.val)=X.val
    rw [← pushForwardGenerator_mul hU,inv_mul_cancel]
    exact pushForwardGenerator_one hU (fun _ hx => X.property.eq_zero_of_not_mem hx)
  right_inv X := by
    apply Subtype.ext
    change pushForwardGenerator q (pushForwardGenerator q⁻¹ X.val)=X.val
    rw [← pushForwardGenerator_mul hU,mul_inv_cancel]
    exact pushForwardGenerator_one hU (fun _ hx => X.property.eq_zero_of_not_mem hx)

def generatorAdjointHom : Biholomorph U U →*
    (completeGeneratorSpace hU hc hbd Γ hhol ≃ₗ[ℝ] completeGeneratorSpace hU hc hbd Γ hhol) where
  toFun := generatorAdjoint hU hc hbd Γ hhol
  map_one' := by
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    exact pushForwardGenerator_one hU (fun _ hx => X.property.eq_zero_of_not_mem hx)
  map_mul' q r := by
    apply LinearEquiv.ext
    intro X
    apply Subtype.ext
    exact pushForwardGenerator_mul hU q r X.val
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GeneratorAdjointContinuous
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

namespace Biholomorph

section
open Set Filter Topology Metric
open scoped Classical
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)

def oneParameterGenerator : completeGeneratorSpace hU hc hbd Γ hhol :=
  ⟨infinitesimalGenerator a,⟨a,ha,ha0,ham,rfl⟩⟩

end

open Set Filter Topology Metric
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GeneratorDeterminantDerivZero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (completeGeneratorSpace hU hc hbd Γ hhol))

def generatorAdjointMatrix (q : Biholomorph U U) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b b (generatorAdjoint hU hc hbd Γ hhol q).toLinearMap

 theorem generatorAdjointMatrix_one : generatorAdjointMatrix hU hc hbd Γ hhol b 1=1 := by
  have h := (generatorAdjointHom hU hc hbd Γ hhol).map_one
  change generatorAdjoint hU hc hbd Γ hhol 1=1 at h
  unfold generatorAdjointMatrix
  rw [h]
  exact LinearMap.toMatrix_one b

 theorem generatorAdjointMatrix_mul (q r : Biholomorph U U) :
    generatorAdjointMatrix hU hc hbd Γ hhol b (q*r)=
      generatorAdjointMatrix hU hc hbd Γ hhol b q * generatorAdjointMatrix hU hc hbd Γ hhol b r := by
  have h := (generatorAdjointHom hU hc hbd Γ hhol).map_mul q r
  change generatorAdjoint hU hc hbd Γ hhol (q*r)=
    generatorAdjoint hU hc hbd Γ hhol q * generatorAdjoint hU hc hbd Γ hhol r at h
  unfold generatorAdjointMatrix
  rw [h]
  exact LinearMap.toMatrix_mul b _ _

def generatorDeterminant : Biholomorph U U →* ℝ where
  toFun q := (generatorAdjointMatrix hU hc hbd Γ hhol b q).det
  map_one' := by rw [generatorAdjointMatrix_one,Matrix.det_one]
  map_mul' q r := by rw [generatorAdjointMatrix_mul,Matrix.det_mul]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GeneratorLieAdjoint
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
include hU hbd

theorem pushForwardGenerator_lieBracket (q : Biholomorph U U)
    {X Y : Affine n → Affine n} (hX : IsCompleteGenerator U X)
    (hY : IsCompleteGenerator U Y) :
    pushForwardGenerator q (VectorField.lieBracket ℂ X Y) =
      VectorField.lieBracket ℂ (pushForwardGenerator q X) (pushForwardGenerator q Y) := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  let b : ℝ → Biholomorph U U := fun t => q*a t*q⁻¹
  have hb : Continuous b := (continuous_const.mul ha).mul continuous_const
  have hb0 : b 0=1 := by simp [b,ha0]
  have hbm : ∀ s t, b (s+t)=b s*b t := by
    intro s t
    dsimp only [b]
    rw [ham]
    group
  have hgen : infinitesimalGenerator b=pushForwardGenerator q (infinitesimalGenerator a) :=
    infinitesimalGenerator_conjugate hU hbd a ha ha0 ham q
  funext x
  by_cases hx : x∈U
  · let y : U := q.toHomeomorph.symm ⟨x,hx⟩
    have hd1 := pushForwardGenerator_hasDerivAt_zero hU hbd b hb hb0 hbm
      (pushForwardGenerator q Y) ((hY.pushForward hU hbd q).analyticOnNhd hU hbd) x hx
    rw [hgen] at hd1
    have hd2 := ((q.derivativeAt y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (pushForwardGenerator_hasDerivAt_zero hU hbd a ha ha0 ham Y
        (hY.analyticOnNhd hU hbd) y.val y.property)
    have heq : (fun t => (q.derivativeAt y) (pushForwardGenerator (a t) Y y.val))=
        (fun t => pushForwardGenerator (b t) (pushForwardGenerator q Y) x) := by
      funext t
      rw [← pushForwardGenerator_mul hU]
      have hg : b t*q=q*a t := by dsimp only [b]; group
      rw [hg,pushForwardGenerator_mul hU]
      exact (pushForwardGenerator_apply q _ ⟨x,hx⟩).symm
    change HasDerivAt (fun t => (q.derivativeAt y) (pushForwardGenerator (a t) Y y.val))
      ((q.derivativeAt y) (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y y.val)) 0 at hd2
    rw [heq] at hd2
    have hd := hd1.unique hd2
    rw [map_neg] at hd
    rw [pushForwardGenerator,dite_eq_left hx]
    exact (neg_injective hd).symm
  · have hqX : pushForwardGenerator q (infinitesimalGenerator a) x=0 := by
      simp only [pushForwardGenerator,dite_eq_right hx]
    have hqY : pushForwardGenerator q Y x=0 := by
      simp only [pushForwardGenerator,dite_eq_right hx]
    rw [pushForwardGenerator,dite_eq_right hx,
      VectorField.lieBracket_eq_zero_of_eq_zero (𝕜 := ℂ) hqX hqY]

variable (hc : IsConnected U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

def generatorLieAdjoint (q : Biholomorph U U) :
    completeGeneratorSpace hU hc hbd Γ hhol ≃ₗ⁅ℝ⁆ completeGeneratorSpace hU hc hbd Γ hhol where
  __ := generatorAdjoint hU hc hbd Γ hhol q
  map_lie' := by
    intro X Y
    apply Subtype.ext
    exact pushForwardGenerator_lieBracket hU hbd q X.property Y.property
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SupportCayleyOpenImage
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Complex Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

theorem supportUncayley_cayley {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, x.2 i+I ≠ 0) : supportUncayley (supportCayley x) = x := by
  apply Prod.ext
  · simp only [supportUncayley,supportCayley,normalUncayley_cayley (hx 0),
      smul_smul,mul_inv_cancel₀ (hx 0),one_smul]
  · funext i
    exact normalUncayley_cayley (hx i)

theorem supportCayley_uncayley {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, 1-x.2 i ≠ 0) : supportCayley (supportUncayley x) = x := by
  apply Prod.ext
  · simp only [supportUncayley,supportCayley,smul_smul,
      inv_mul_cancel₀ (normalUncayley_add_I_ne_zero (hx 0)),one_smul]
  · funext i
    exact normalCayley_uncayley (hx i)

theorem analyticAt_supportCayley {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, x.2 i+I ≠ 0) : AnalyticAt ℂ supportCayley x := by
  have hw (i : Fin (k+1)) : AnalyticAt ℂ (fun q : E × (Fin (k+1) → ℂ) => q.2 i) x :=
    ((ContinuousLinearMap.proj i : (Fin (k+1) → ℂ) →L[ℂ] ℂ).analyticAt x.2).comp analyticAt_snd
  have hz : AnalyticAt ℂ (fun q : E × (Fin (k+1) → ℂ) => (q.2 0+I)⁻¹ • q.1) x :=
    (((hw 0).add analyticAt_const).inv (hx 0)).smul analyticAt_fst
  refine hz.prod (AnalyticAt.pi fun i => ?_)
  exact ((hw i).sub analyticAt_const).div ((hw i).add analyticAt_const) (hx i)

theorem analyticAt_supportUncayley {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, 1-x.2 i ≠ 0) : AnalyticAt ℂ supportUncayley x := by
  have hw (i : Fin (k+1)) : AnalyticAt ℂ (fun q : E × (Fin (k+1) → ℂ) => q.2 i) x :=
    ((ContinuousLinearMap.proj i : (Fin (k+1) → ℂ) →L[ℂ] ℂ).analyticAt x.2).comp analyticAt_snd
  have hu (i : Fin (k+1)) : AnalyticAt ℂ (fun q : E × (Fin (k+1) → ℂ) => normalUncayley (q.2 i)) x :=
    (analyticAt_const.mul (analyticAt_const.add (hw i))).div
      (analyticAt_const.sub (hw i)) (hx i)
  exact ((hu 0).add analyticAt_const).smul analyticAt_fst |>.prod (AnalyticAt.pi hu)

def supportCayleyChart : OpenPartialHomeomorph (E × (Fin (k+1) → ℂ)) (E × (Fin (k+1) → ℂ)) where
  toFun := supportCayley
  invFun := supportUncayley
  source := {x | ∀ i, x.2 i+I ≠ 0}
  target := {x | ∀ i, 1-x.2 i ≠ 0}
  map_source' := by
    intro x hx i
    exact sub_ne_zero.mpr (normalCayley_ne_one (hx i)).symm
  map_target' := by
    intro x hx i
    exact normalUncayley_add_I_ne_zero (hx i)
  left_inv' _ hx := supportUncayley_cayley hx
  right_inv' _ hx := supportCayley_uncayley hx
  open_source := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_ne.preimage ((continuous_apply i |>.comp continuous_snd).add continuous_const)
  open_target := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_ne.preimage (continuous_const.sub (continuous_apply i |>.comp continuous_snd))
  continuousOn_toFun := fun _ hx => (analyticAt_supportCayley hx).continuousAt.continuousWithinAt
  continuousOn_invFun := fun _ hx => (analyticAt_supportUncayley hx).continuousAt.continuousWithinAt

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelChartOpen
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

def modelBoundedChart (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) :
    OpenPartialHomeomorph (E × (Fin (k+1) → ℂ)) (E × (Fin (k+1) → ℂ)) :=
  (supportLinearCoordinates e).toHomeomorph.toOpenPartialHomeomorph.trans supportCayleyChart

@[simp] lemma modelBoundedChart_apply
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) (x : E × (Fin (k+1) → ℂ)) :
    modelBoundedChart e x = supportCayley (supportLinearCoordinates e x) := rfl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelComplexField
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
open scoped TensorProduct
namespace Biholomorph

open scoped Classical
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

variable (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

def modelComplexField (e : Biholomorph U D) :
    ComplexGenerators hU hc hbd Γ hhol →ₗ[ℂ] (Affine m → Affine m) :=
  (coordinateFieldComplexLinear e).comp (complexGeneratorField hU hc hbd Γ hhol)

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelRotationWeight
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
namespace Biholomorph

def modelEulerWeight {r k : ℕ} : ModelIndex r k → ℂ
  | .inl _ => 1/2
  | .inr _ => 1

def modelRotationWeight {r k : ℕ} : ModelIndex r k → ℂ
  | .inl _ => Complex.I
  | .inr _ => 0

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalizedLocalInverse
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

@[simp] lemma ambientAction_subtype {n : ℕ} {U : Set (Affine n)} {Γ : Type*}
    [Group Γ] [MulAction Γ U] (γ : Γ) (y : U) :
    ambientAction U Γ γ y.val = (γ • y).val := by
  simp only [ambientAction,dite_eq_left y.property]

noncomputable def actionLocalSet {n : ℕ} (U : Set (Affine n)) (Γ : Type*)
    [Group Γ] [MulAction Γ U] (γ : Γ) (Ω : Set (Affine n)) : Set (Affine n) :=
  U ∩ (ambientAction U Γ γ) ⁻¹' Ω

lemma actionLocalSet_subset {n : ℕ} {U : Set (Affine n)} {Γ : Type*}
    [Group Γ] [MulAction Γ U] (γ : Γ) (Ω : Set (Affine n)) :
    actionLocalSet U Γ γ Ω ⊆ U := inter_subset_left

noncomputable def normalizedLocalBiholomorph {n m : ℕ} {U Ω : Set (Affine n)}
    {D : Set (Affine m)} {Γ : Type*} [Group Γ] [MulAction Γ U]
    [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun y => (γ • y : U).val))
    (γ : Γ) (b : Biholomorph (U ∩ Ω) D) :
    Biholomorph (actionLocalSet U Γ γ Ω) D :=
  ((actionBiholomorph U Γ hhol γ).restrict
    (actionLocalSet_subset γ Ω) inter_subset_left (by
      intro y
      simp only [actionLocalSet,mem_inter_iff,mem_preimage,y.property,
        ambientAction_subtype,true_and]
      exact (and_iff_right (γ • y).property).symm)).trans b

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScaledLocal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology
open scoped Classical
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma weightedScale_analytic (t : ℝ) (x : E × F) : AnalyticAt ℂ (weightedScale t) x := by
  change AnalyticAt ℂ (fun z : E × F => (Real.sqrt t • z.1,t • z.2)) x
  exact (analyticAt_fst.const_smul (c := Real.sqrt t)).prod
    (analyticAt_snd.const_smul (c := t))

lemma weightedUnscale_analytic (t : ℝ) (x : E × F) : AnalyticAt ℂ (weightedUnscale t) x := by
  change AnalyticAt ℂ (fun z : E × F => ((Real.sqrt t)⁻¹ • z.1,t⁻¹ • z.2)) x
  exact (analyticAt_fst.const_smul (c := (Real.sqrt t)⁻¹)).prod
    (analyticAt_snd.const_smul (c := t⁻¹))

end

open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

noncomputable def scaled_local_biholomorph (s : NashBoundaryScalingChart c x)
    (hcut : s.HasCutoffs) (Ω : Set (Affine N))
    (hfΩ : MapsTo s.forward s.offsets.source Ω)
    (hgS : MapsTo s.backward Ω s.offsets.source)
    (hfg : ∀ y ∈ Ω, s.forward (s.backward y)=y) {t : ℝ} (ht : 0 < t) :
    Biholomorph (U ∩ Ω)
      ((affineProductCoordinates s.tangentDim s.normalDim) '' s.domain t) := by
  let e := affineProductCoordinates s.tangentDim s.normalDim
  let f : Affine N → Affine (s.tangentDim+s.normalDim) :=
    fun y => e (weightedUnscale t (s.backward y))
  let g : Affine (s.tangentDim+s.normalDim) → Affine N :=
    fun z => s.forward (weightedScale t (e.symm z))
  have hfd : MapsTo f (U ∩ Ω) (e '' s.domain t) := by
    intro y hy
    refine ⟨weightedUnscale t (s.backward y),?_,rfl⟩
    change weightedScale t (weightedUnscale t (s.backward y)) ∈ s.offsets.source ∧ _
    rw [weightedScale_unscale ht,hfg y hy.2]
    exact ⟨hgS hy.2,hy.1⟩
  have hgu : MapsTo g (e '' s.domain t) (U ∩ Ω) := by
    rintro _ ⟨z,hz,rfl⟩
    change s.forward (weightedScale t (e.symm (e z))) ∈ _
    rw [e.symm_apply_apply]
    exact ⟨hz.2,hfΩ hz.1⟩
  refine biholomorphOfAmbientInverse _ _ f g ?_ ?_ hfd hgu ?_ ?_
  · intro y _
    exact (e.toContinuousLinearMap.analyticAt _).comp
      ((weightedUnscale_analytic t _).comp (s.backward_analytic y (mem_univ _)))
  · rintro _ ⟨z,hz,rfl⟩
    have ha := s.forward_analytic hcut (weightedScale t z) hz.1
    have ha' : AnalyticAt ℂ s.forward (weightedScale t (e.symm (e z))) := by
      simpa only [e.symm_apply_apply] using ha
    have he : AnalyticAt ℂ (fun y => e.symm y) (e z) :=
      e.symm.toContinuousLinearMap.analyticAt (e z)
    have hs : AnalyticAt ℂ (fun y => weightedScale t (e.symm y)) (e z) :=
      (weightedScale_analytic t (e.symm (e z))).comp he
    exact AnalyticAt.comp (f := fun y => weightedScale t (e.symm y)) ha' hs
  · intro y hy
    change s.forward (weightedScale t (e.symm (e (weightedUnscale t (s.backward y)))))=y
    rw [e.symm_apply_apply,weightedScale_unscale ht,hfg y hy.2]
  · rintro _ ⟨z,hz,rfl⟩
    change e (weightedUnscale t (s.backward (s.forward (weightedScale t (e.symm (e z))))))=e z
    rw [e.symm_apply_apply,s.backward_forward hcut hz.1,weightedUnscale_scale ht]

end NashBoundaryScalingChart
end Release061

end

end OAI
end


