-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsRingHomModXPowSuccLift
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsRingHomModXPowSuccLift
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:02.191604+00:00
-- url     : https://prove2.me/theorems/2b41cd4a-cbbb-446b-bd97-fa517581d908
-- title:
--   Exists Is Ring Hom Mod XPow Succ Lift
-- statement:
--   Definitions and structural lemmas for Exists Is Ring Hom Mod XPow Succ Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsRingHomModXPowSuccLift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply


set_option autoImplicit false
open GlobalTheory.Nef
namespace GlobalTheory.Nef.PathJet
open PowerSeries
theorem mk_eq_iff_X_pow_dvd {R : Type} [CommRing R] (k : ℕ) (x y : PowerSeries R) :
    Ideal.Quotient.mk (Ideal.span {(X : PowerSeries R) ^ k}) x =
      Ideal.Quotient.mk (Ideal.span {(X : PowerSeries R) ^ k}) y ↔ (X : PowerSeries R) ^ k ∣ x - y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
noncomputable def quotRingHom {A B R : Type} [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (β : B →+* R) (n : ℕ)
    (φ : A → PowerSeries R) (hφ : IsRingHomMod π β n φ) :
    A →+* PowerSeries R ⧸ Ideal.span {(X : PowerSeries R) ^ n} where
  toFun f := Ideal.Quotient.mk _ (φ f)
  map_one' := by rw [← map_one (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd]; exact hφ.2.2.1
  map_mul' f g := by rw [← map_mul, mk_eq_iff_X_pow_dvd]; exact hφ.1 f g
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk _), mk_eq_iff_X_pow_dvd]
    have := hφ.2.1 0 0
    simp only [add_zero] at this
    simpa using this
  map_add' f g := by rw [← map_add, mk_eq_iff_X_pow_dvd]; exact hφ.2.1 f g
end GlobalTheory.Nef.PathJet


