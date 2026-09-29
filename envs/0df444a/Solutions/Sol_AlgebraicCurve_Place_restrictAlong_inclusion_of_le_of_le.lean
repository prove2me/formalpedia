-- Prove2me | solution 1 for AlgebraicCurve.Place.restrictAlong_inclusion_of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/53c88eb5-b54e-55c9-9165-7bb08a1a7afe

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_restrictAlong_inclusion_of_le_of_le

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_restrictAlong_inclusion_of_le_of_le.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.ramificationIndexAlong Place.ord_restrictAlong Place Place.ext"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndexAlong ord_restrictAlong ext ord ord_coe_irreducible toValuationSubring"
namespace ITransportSeam
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

theorem restrictAlong_incl_incl {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (h₁ : S ≤ T) (h₂ : T ≤ S)
    (hι₁ : (IntermediateField.inclusion h₁).toRingHom.IsIntegral) (hι₂ : (IntermediateField.inclusion h₂).toRingHom.IsIntegral)
    (W : Place K ↥S) :
    (W.restrictAlong (IntermediateField.inclusion h₂) hι₂).restrictAlong (IntermediateField.inclusion h₁) hι₁ = W := by
  apply Place.ext
  ext x
  exact (show IntermediateField.inclusion h₂ (IntermediateField.inclusion h₁ x) ∈ W.toValuationSubring ↔ x ∈ W.toValuationSubring by
    rw [IntermediateField.inclusion_inclusion, IntermediateField.inclusion_self, AlgHom.id_apply])

theorem ramificationIndexAlong_incl_eq_one {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (h₁ : S ≤ T) (h₂ : T ≤ S)
    (hι₁ : (IntermediateField.inclusion h₁).toRingHom.IsIntegral) (hι₂ : (IntermediateField.inclusion h₂).toRingHom.IsIntegral)
    (W' : Place K ↥T) : W'.ramificationIndexAlong (IntermediateField.inclusion h₁) = 1 := by
  classical
  set W := W'.restrictAlong (IntermediateField.inclusion h₁) hι₁ with hW
  have hWW' : W.restrictAlong (IntermediateField.inclusion h₂) hι₂ = W' := restrictAlong_incl_incl h₂ h₁ hι₂ hι₁ W'
  have e1 : ∀ f : ↥S, W'.ord (IntermediateField.inclusion h₁ f) =
      Place.ramificationIndexAlong (IntermediateField.inclusion h₁) W' * W.ord f :=
    fun f => Place.ord_restrictAlong _ hι₁ W' f
  have e2 : ∀ f' : ↥T, W.ord (IntermediateField.inclusion h₂ f') =
      Place.ramificationIndexAlong (IntermediateField.inclusion h₂) W * W'.ord f' := by
    intro f'
    have := Place.ord_restrictAlong _ hι₂ W f'
    rwa [hWW'] at this
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W.toValuationSubring
  have hπ1 : W.ord (π : ↥S) = 1 := W.ord_coe_irreducible hπ
  have hprod : (Place.ramificationIndexAlong (IntermediateField.inclusion h₂) W : ℤ) *
      Place.ramificationIndexAlong (IntermediateField.inclusion h₁) W' = 1 := by
    have hh := e2 (IntermediateField.inclusion h₁ (π : ↥S))
    rw [IntermediateField.inclusion_inclusion, IntermediateField.inclusion_self, AlgHom.id_apply, hπ1, e1, hπ1, mul_one] at hh
    exact hh.symm
  have hone : (Place.ramificationIndexAlong (IntermediateField.inclusion h₁) W' : ℤ) = 1 := by
    have hnn1 : (0 : ℤ) ≤ Place.ramificationIndexAlong (IntermediateField.inclusion h₁) W' := Int.natCast_nonneg _
    rw [mul_comm] at hprod
    exact Int.eq_one_of_mul_eq_one_right hnn1 hprod
  exact_mod_cast hone

end AlgebraicCurve.Place.ITransportSeam

open AlgebraicCurve.Place.ITransportSeam in

theorem solution
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (hST : S ≤ T) (hTS : T ≤ S)
    (h : (IntermediateField.inclusion hST).toRingHom.IsIntegral)
    (h' : (IntermediateField.inclusion hTS).toRingHom.IsIntegral) :
    (∀ w : Place K T, (w.restrictAlong (IntermediateField.inclusion hST) h).restrictAlong (IntermediateField.inclusion hTS) h' = w) ∧
    (∀ v : Place K S, (v.restrictAlong (IntermediateField.inclusion hTS) h').restrictAlong (IntermediateField.inclusion hST) h = v) ∧
    (∀ w : Place K T, w.ramificationIndexAlong (IntermediateField.inclusion hST) = 1) ∧
    (∀ (w : Place K T) (f : S), (w.restrictAlong (IntermediateField.inclusion hST) h).ord f = w.ord (IntermediateField.inclusion hST f)) := by

  refine ⟨fun w => restrictAlong_incl_incl hTS hST h' h w, fun v => restrictAlong_incl_incl hST hTS h h' v,
    fun w => ramificationIndexAlong_incl_eq_one hST hTS h h' w, fun w f => ?_⟩
  rw [Place.ord_restrictAlong _ h w f, ramificationIndexAlong_incl_eq_one hST hTS h h' w, Nat.cast_one, one_mul]

end S_AlgebraicCurve_Place_restrictAlong_inclusion_of_le_of_le
end P2MW
export P2MW.S_AlgebraicCurve_Place_restrictAlong_inclusion_of_le_of_le (solution)
