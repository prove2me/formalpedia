-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_TiltMap
-- name    : GroundTheory_PAdicHodge_TiltMap
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T09:28:04.39983+00:00
-- url     : https://prove2.me/theorems/9066b6ba-0176-45ab-b75b-a07bc81bd143
-- title:
--   Tilt Map
-- statement:
--   Definitions and structural lemmas for Tilt Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltMap.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_coeff_ofCompatible
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_mk_untilt_iterate
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_preTilt_ext
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_eq_zero_iff
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_iterate_succ_pow
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_ofCompatible
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_untilt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
section Integers
variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
def integerMap (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : normInteger K →+* normInteger L :=
  φ.restrict (normInteger K) (normInteger L) fun x hx =>
    mem_normInteger.2 ((hφ x).trans_le (mem_normInteger.1 hx))
@[simp]
theorem coe_integerMap (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : normInteger K) :
    (integerMap φ hφ x : L) = φ x :=
  rfl
end Integers
section Tilt
variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪L♭" => PreTilt (normInteger L) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "L♭" => Tilt L NormedField.valuation (normInteger L) normInteger_integers p
def modPMap : ModP (normInteger K) p →+* ModP (normInteger L) p :=
  Ideal.quotientMap _ (integerMap φ hφ) (Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _)))
omit [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p] in
theorem modPMap_mk (a : normInteger K) :
    modPMap φ hφ (Ideal.Quotient.mk (Ideal.span {(p : normInteger K)}) a) =
      Ideal.Quotient.mk (Ideal.span {(p : normInteger L)}) (integerMap φ hφ a) :=
  Ideal.quotientMap_mk
variable (p) in

def preTiltMap : 𝒪K♭ →+* 𝒪L♭ :=
  Perfection.map p (modPMap φ hφ)
theorem coeff_preTiltMap (x : 𝒪K♭) (n : ℕ) :
    Perfection.coeff (ModP (normInteger L) p) p n (preTiltMap p φ hφ x) =
      modPMap φ hφ (Perfection.coeff (ModP (normInteger K) p) p n x) :=
  Perfection.coeff_map _ _ _ _
theorem untilt_preTiltMap (x : 𝒪K♭) :
    PreTilt.untilt (preTiltMap p φ hφ x) = integerMap φ hφ (PreTilt.untilt x) := by
  let y : ℕ → normInteger K :=
    fun n => PreTilt.untilt ((frobeniusEquiv 𝒪K♭ p).symm^[n] x)
  have hy : ∀ n, y (n + 1) ^ p = y n := IsPerfectoidField.untilt_iterate_succ_pow p x
  have hx : x = IsPerfectoidField.ofCompatible p y hy :=
    IsPerfectoidField.preTilt_ext p fun n => by
      rw [IsPerfectoidField.coeff_ofCompatible, IsPerfectoidField.mk_untilt_iterate]
  have hy' : ∀ n, (integerMap φ hφ ∘ y) (n + 1) ^ p = (integerMap φ hφ ∘ y) n := fun n => by
    simp only [Function.comp_apply, ← map_pow, hy]
  have key : preTiltMap p φ hφ x = IsPerfectoidField.ofCompatible p _ hy' := by
    refine IsPerfectoidField.preTilt_ext p fun n => ?_
    rw [IsPerfectoidField.coeff_ofCompatible]
    change Perfection.coeff (ModP (normInteger L) p) p n (preTiltMap p φ hφ x) = _
    rw [coeff_preTiltMap]
    change modPMap φ hφ (PreTilt.coeff n x) = _
    rw [← IsPerfectoidField.mk_untilt_iterate, modPMap_mk]
    rfl
  rw [key, IsPerfectoidField.untilt_ofCompatible]
  rfl
theorem coe_untilt_preTiltMap (x : 𝒪K♭) :
    ((PreTilt.untilt (preTiltMap p φ hφ x) : normInteger L) : L) =
      φ ((PreTilt.untilt x : normInteger K) : K) := by
  rw [untilt_preTiltMap, coe_integerMap]
theorem preTiltMap_injective : Function.Injective (preTiltMap p φ hφ) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have h1 := coe_untilt_preTiltMap φ hφ x
  rw [hx, IsPerfectoidField.untilt_zero, ZeroMemClass.coe_zero, eq_comm,
    map_eq_zero_iff φ φ.injective] at h1
  exact (IsPerfectoidField.untilt_eq_zero_iff p).1 (Subtype.ext h1)
variable (p) in

def tiltMap : K♭ →+* L♭ :=
  IsFractionRing.map (preTiltMap_injective (p := p) φ hφ)
end Tilt
end GroundTheory.PAdicHodge


