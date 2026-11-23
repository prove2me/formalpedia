-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleInvolutiveAlgebraSplittingSmaller
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:46.575802+00:00
-- url     : https://prove2.me/theorems/5ccea332-12c9-49be-ac7d-972baa677538
-- title:
--   Exists Etale Involutive Algebra Splitting Smaller
-- statement:
--   Definitions and structural lemmas for Exists Etale Involutive Algebra Splitting Smaller, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleInvolutiveAlgebraSplittingSmaller.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
section star
variable {L : Type} [CommRing L] [StarRing L]
def quotStarRing (J : Ideal L) (hJ : ∀ a ∈ J, star a ∈ J) : StarRing (L ⧸ J) where
  star := Ideal.Quotient.lift J ((Ideal.Quotient.mk J).comp (starRingEnd L))
    (fun a ha => by
      simp only [RingHom.comp_apply, starRingEnd_apply]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hJ a ha))
  star_involutive x := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  star_mul x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [← map_mul, mul_comm]
  star_add x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp [← map_add]
end star
variable (A : Et F E) (e : A.K)
abbrev QK := A.K ⧸ Ideal.span {e}
abbrev QL := A.L ⧸ (Ideal.span {e}).map (algebraMap A.K A.L)
instance twQ : IsScalarTower F (QK A e) (QL A e) := IsScalarTower.of_algebraMap_eq fun x => by
  rw [IsScalarTower.algebraMap_apply F A.K (QK A e)]
  simp only [Ideal.Quotient.algebraMap_eq, RingHom.comp_apply, Ideal.Quotient.algebraMap_quotient_map_quotient]
  show Ideal.Quotient.mk _ (algebraMap F A.L x) = _
  rw [IsScalarTower.algebraMap_apply F A.K A.L]
theorem star_mem (a : A.L) (ha : a ∈ (Ideal.span {e}).map (algebraMap A.K A.L)) :
    star a ∈ (Ideal.span {e}).map (algebraMap A.K A.L) := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at ha ⊢
  obtain ⟨c, rfl⟩ := ha
  exact ⟨star c, by rw [star_mul, A.star_K, mul_comm]⟩
def eq0 : TensorProduct A.K (QK A e) A.L ≃ₗ[A.K] QL A e :=
  (TensorProduct.comm A.K (QK A e) A.L).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A.L (Ideal.span {e})).symm.toLinearEquiv.restrictScalars A.K)
theorem etaleQuotientTensorLinearEquiv_one_tmul (x : A.L) : eq0 A e (1 ⊗ₜ x) = Ideal.Quotient.mk _ x := by
  simp only [eq0, LinearEquiv.trans_apply, TensorProduct.comm_tmul, LinearEquiv.restrictScalars_apply,
    AlgEquiv.toLinearEquiv_apply]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {e})), Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
    one_smul]
  rfl
theorem isBaseChange_quot : IsBaseChange (QK A e) (IsScalarTower.toAlgHom A.K A.L (QL A e)).toLinearMap :=
  IsBaseChange.of_equiv ((eq0 A e).extendScalarsOfSurjective Ideal.Quotient.mk_surjective) fun x => by
    simpa using etaleQuotientTensorLinearEquiv_one_tmul A e x
theorem push_quot : Algebra.IsPushout F E (QK A e) (QL A e) := by
  have h2 : IsBaseChange A.K (IsScalarTower.toAlgHom F E A.L).toLinearMap :=
    (Algebra.isPushout_iff F A.K E A.L).1 A.push.symm
  have h5 := h2.comp (isBaseChange_quot A e)
  refine Algebra.IsPushout.symm ((Algebra.isPushout_iff F (QK A e) E (QL A e)).2 ?_)
  have hm : (IsScalarTower.toAlgHom F E (QL A e)).toLinearMap =
      (IsScalarTower.toAlgHom A.K A.L (QL A e)).toLinearMap.restrictScalars F ∘ₗ
        (IsScalarTower.toAlgHom F E A.L).toLinearMap := by
    ext y; rfl
  rw [hm]; exact h5
end GlobalTheory.JR.EtQuot
namespace GlobalTheory.JR.EtQuot
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable (A : Et F E) (e : A.K)
theorem isReduced_quot (he : IsIdempotentElem e) : IsReduced (QK A e) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, hn⟩ := hx
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hn
  obtain ⟨c, hc⟩ := hn
  have h1 : IsNilpotent (y * (1 - e)) := ⟨n + 1, by
    rw [mul_pow, he.one_sub.pow_succ_eq, pow_succ, ← hc]
    linear_combination (-(c * y)) * he.eq⟩
  have h2 := IsReduced.eq_zero _ h1
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  exact ⟨y, by linear_combination -h2⟩
def quotEt (he : IsIdempotentElem e) : Et F E :=
  letI tK : TopologicalSpace (QK A e) := moduleTopology F _
  haveI mtK : IsModuleTopology F (QK A e) := ⟨rfl⟩
  letI tL : TopologicalSpace (QL A e) := moduleTopology F _
  haveI mtL : IsModuleTopology F (QL A e) := ⟨rfl⟩
  letI mK : MeasurableSpace (QK A e) := borel _
  letI mL : MeasurableSpace (QL A e) := borel _
  letI sL : StarRing (QL A e) := quotStarRing _ (star_mem A e)
  { K := QK A e
    L := QL A e
    redK := isReduced_quot A e he
    trK := IsModuleTopology.isTopologicalRing F _
    lcK := (IsModuleTopology.isOpenQuotientMap_of_surjective (R := F) (A := A.K)
      (φ := (Ideal.Quotient.mkₐ F (Ideal.span {e})).toLinearMap) (Ideal.Quotient.mkₐ_surjective F _)).locallyCompactSpace
    bK := ⟨rfl⟩
    bL := ⟨rfl⟩
    push := push_quot A e
    star_K := fun x => by
      obtain ⟨k, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
      show Ideal.Quotient.mk _ (star _) = _
      rw [A.star_K]
    star_E := fun y => by
      show Ideal.Quotient.mk _ (star (algebraMap E A.L y)) = Ideal.Quotient.mk _ (algebraMap E A.L (star y))
      rw [A.star_E] }
end GlobalTheory.JR.EtQuot
namespace GlobalTheory.JR.EtQuot
end GlobalTheory.JR.EtQuot


