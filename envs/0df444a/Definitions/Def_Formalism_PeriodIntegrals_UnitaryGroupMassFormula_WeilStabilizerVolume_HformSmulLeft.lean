-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HformSmulLeft
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_HformSmulLeft
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:35.311368+00:00
-- url     : https://prove2.me/theorems/d32102d1-122d-4c2d-8035-3a5c3017371e
-- title:
--   Hform Smul Left
-- statement:
--   Definitions and structural lemmas for Hform Smul Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/HformSmulLeft.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
@[reducible] def starOfInv {E : Type} [Field E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) :
    StarRing E where
  star := σ
  star_involutive := hσ
  star_mul x y := by
    show σ (x * y) = σ y * σ x
    rw [map_mul, mul_comm]
  star_add x y := map_add σ x y
section General
variable {E : Type} [Field E] {M : ℕ}
theorem hform_add_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
theorem hform_smul_left' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J (c • x) y = σ c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
theorem hform_add_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
theorem hform_smul_right' (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E) (c : E) (x y : Fin M → E) :
    Formalism.UG.hform σ J x (c • y) = RingHom.id E c • Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
variable [StarRing E]
def hSes (J : Matrix (Fin M) (Fin M) E) : (Fin M → E) →ₗ⋆[E] (Fin M → E) →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => Formalism.UG.hform (starRingEnd E) J x y)
    (hform_add_left' _ J) (hform_smul_left' _ J) (hform_add_right' _ J) (hform_smul_right' _ J)
variable [CharZero E]
end General
end PI.VolStabW


