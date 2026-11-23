-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
-- name    : GroundTheory_AutomorphicForms_MeasuresModulus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:15.207996+00:00
-- url     : https://prove2.me/theorems/d7d18633-b34d-4e2e-ab58-8a6472217051
-- title:
--   Measures Modulus
-- statement:
--   Definitions and structural lemmas for Measures Modulus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
namespace Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
section Topology
theorem countable_units_valueGroup : Countable (ValueGroupWithZero F)ˣ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ValueGroupWithZero F)ˣ)
  refine Function.Surjective.countable (f := fun k : ℤ => g ^ k) fun x => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  exact ⟨k, hk⟩
theorem metrizableSpace : TopologicalSpace.MetrizableSpace F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have := countable_units_valueGroup F
  have : (𝓝 (0 : F)).IsCountablyGenerated :=
    (IsValuativeTopology.hasBasis_nhds_zero F).isCountablyGenerated
  have : (uniformity F).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero F]
    infer_instance
  exact UniformSpace.metrizableSpace
theorem sigmaCompactSpace : SigmaCompactSpace F := by
  refine ⟨⟨fun k : ℕ => {x | valuation F x ≤ (valuation F (GLnLocal.uniformizer F : F))⁻¹ ^ k},
    fun k => IsNonarchimedeanLocalField.isCompact_closedBall F _, ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hvx : valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (GLnLocal.valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹
  refine ⟨m, ?_⟩
  have hϖ := GLnLocal.valuation_uniformizer_ne_zero F
  have h1 : valuation F (GLnLocal.uniformizer F : F) ^ m * valuation F x < 1 := by
    have := mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)
    simpa [hvx] using this
  have hm0 : valuation F (GLnLocal.uniformizer F : F) ^ m ≠ 0 := pow_ne_zero _ hϖ
  rw [inv_pow, ← mul_one ((valuation F (GLnLocal.uniformizer F : F) ^ m)⁻¹),
    le_inv_mul_iff₀ (zero_lt_iff.mpr hm0)]
  exact h1.le
instance secondCountableTopology : SecondCountableTopology F := by
  have := metrizableSpace F
  have := sigmaCompactSpace F
  let := TopologicalSpace.metrizableSpaceMetric F
  exact EMetric.secondCountable_of_sigmaCompact F
theorem secondCountableTopology_units {M : Type*} [Monoid M] [TopologicalSpace M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ :=
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology
instance secondCountableTopology_GL (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SecondCountableTopology (GL ι F) :=
  haveI : SecondCountableTopology (Matrix ι ι F) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → F))
  secondCountableTopology_units
end Topology
section Modulus
variable {F} {ι : Type*} [Fintype ι]
instance continuousConstSMul_linearEquiv :
    ContinuousConstSMul ((ι → F) ≃ₗ[F] (ι → F)) (ι → F) :=
  ⟨fun L => (L.toLinearMap).continuous_on_pi⟩
variable (F ι) in

def box : Set (ι → F) := Set.univ.pi fun _ => (𝒪[F] : Set F)
variable [DecidableEq ι]
noncomputable def modulus : F →*₀ ℝ≥0 where
  toFun x := by classical exact if h : x = 0 then 0 else distribHaarChar F (Units.mk0 x h)
  map_zero' := dif_pos rfl
  map_one' := by
    rw [dif_neg one_ne_zero]
    convert map_one (distribHaarChar F (G := Fˣ))
    ext
    rfl
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    rw [dif_neg (mul_ne_zero hx hy), dif_neg hx, dif_neg hy, ← map_mul]
    congr 1
    ext
    rfl
noncomputable def glEquiv : GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))
end Modulus
end Measures
end GroundTheory.Automorphic


