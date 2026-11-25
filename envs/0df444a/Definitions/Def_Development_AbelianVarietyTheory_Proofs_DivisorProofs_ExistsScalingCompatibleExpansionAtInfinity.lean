-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsScalingCompatibleExpansionAtInfinity
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:14.004795+00:00
-- url     : https://prove2.me/theorems/ea48dc20-0b68-4ba1-bb03-adce842df82f
-- title:
--   Exists Scaling Compatible Expansion At Infinity
-- statement:
--   Definitions and structural lemmas for Exists Scaling Compatible Expansion At Infinity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsScalingCompatibleExpansionAtInfinity.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
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
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
namespace GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]
noncomputable def polyScale (c : F) : F[X] →ₐ[F] F[X] := Polynomial.aeval (Polynomial.C c * Polynomial.X)
theorem polyScale_polyScale (c d : F) (p : F[X]) :
    polyScale d (polyScale c p) = polyScale (c * d) p := by
  have : (polyScale d).comp (polyScale c) = polyScale (c * d) := by
    apply Polynomial.algHom_ext
    simp only [polyScale, AlgHom.comp_apply, Polynomial.aeval_X, map_mul, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, Polynomial.C_mul]
    ring
  exact congrArg (fun φ : F[X] →ₐ[F] F[X] => φ p) this
theorem polyScale_one (p : F[X]) : polyScale (1 : F) p = p := by
  show Polynomial.aeval (Polynomial.C (1 : F) * Polynomial.X) p = p
  rw [map_one, one_mul, Polynomial.aeval_X_left_apply]
theorem polyScale_injective {c : F} (hc : c ≠ 0) : Function.Injective (polyScale c) := by
  intro p q h
  have := congrArg (polyScale c⁻¹) h
  rwa [polyScale_polyScale, polyScale_polyScale, mul_inv_cancel₀ hc, polyScale_one, polyScale_one] at this
theorem rescale_injective {c : F} (hc : c ≠ 0) : Function.Injective (PowerSeries.rescale c) := by
  intro p q h
  have := congrArg (PowerSeries.rescale c⁻¹) h
  rwa [PowerSeries.rescale_rescale, PowerSeries.rescale_rescale, mul_inv_cancel₀ hc,
    PowerSeries.rescale_one, RingHom.id_apply, RingHom.id_apply] at this
theorem transcendental_X : Transcendental F (RatFunc.X : RatFunc F) := by
  rw [transcendental_iff_injective]
  intro p q h
  have e : ∀ r : F[X], Polynomial.aeval (RatFunc.X : RatFunc F) r = algebraMap F[X] (RatFunc F) r := by
    intro r
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [e, e] at h
  exact IsFractionRing.injective F[X] (RatFunc F) h
end GlobalTheory.Nef.InfScale
namespace GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]
noncomputable def ratScale (c : F) (hc : c ≠ 0) : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (algebraMap F[X] (RatFunc F)).comp (polyScale c).toRingHom)
    ((IsFractionRing.injective F[X] (RatFunc F)).comp (polyScale_injective hc))
noncomputable def lsScale (c : F) (hc : c ≠ 0) : LaurentSeries F →+* LaurentSeries F :=
  IsFractionRing.lift (g := (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale c))
    ((IsFractionRing.injective (PowerSeries F) (LaurentSeries F)).comp (rescale_injective hc))
noncomputable def ratInv : RatFunc F →+* RatFunc F :=
  IsFractionRing.lift (g := (Polynomial.aeval (RatFunc.X : RatFunc F)⁻¹).toRingHom)
    (fun x y h => (transcendental_iff_injective.1 fun h => transcendental_X (IsAlgebraic.inv_iff.1 h)) h)
end GlobalTheory.Nef.InfScale
namespace GlobalTheory.Nef.InfScale
variable {F : Type} [Field F]
end GlobalTheory.Nef.InfScale


