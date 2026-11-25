-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
-- name    : GroundTheory_PAdicHodge_BCrisNewtonLift
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T11:28:23.539194+00:00
-- url     : https://prove2.me/theorems/ff5f13cc-dd88-4f79-9c38-7b70a708ce0a
-- title:
--   BCris Newton Lift
-- statement:
--   Definitions and structural lemmas for BCris Newton Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonLift.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
namespace WittTilt
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
variable (K p) in

def incl : AInf K p →+* WittVector p K♭ := WittVector.map (algebraMap 𝒪♭ K♭)
theorem incl_coeff (x : AInf K p) (n : ℕ) :
    (incl K p x).coeff n = algebraMap 𝒪♭ K♭ (x.coeff n) :=
  map_coeff _ _ _
theorem natCast_p_ne_zero : (p : WittVector p K♭) ≠ 0 := by
  intro h
  have := coeff_p_pow (p := p) (R := K♭) 1
  rw [pow_one, h] at this
  simp at this
theorem p_mem_nonZeroDivisors : (p : WittVector p K♭) ∈ nonZeroDivisors (WittVector p K♭) :=
  mem_nonZeroDivisors_of_ne_zero natCast_p_ne_zero
variable (K p) in

def intSubring : Subring (WittVector p K♭) := (incl K p).range
variable (K p) in

def teichLift : TeichLift p K♭ (WittVector p K♭) where
  π := p
  red := WittVector.constantCoeff
  red_surjective := constantCoeff_surjective p
  ker_red := ker_constantCoeff
  π_mem_nonZeroDivisors := p_mem_nonZeroDivisors
  isAdicComplete := inferInstance
  int := intSubring K p
  π_mem_int := ⟨p, map_natCast _ _⟩
  norm_red_le_one := by
    rintro _ ⟨y, rfl⟩
    show ‖(incl K p y).coeff 0‖ ≤ 1
    rw [incl_coeff, norm_algebraMap_preTilt]
    exact preTilt_norm_le_one _
  exists_mem_int := by
    intro a ha
    obtain ⟨b, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 ha
    refine ⟨incl K p (teichmuller p b), ⟨_, rfl⟩, ?_⟩
    show (incl K p (teichmuller p b)).coeff 0 = _
    rw [incl_coeff, teichmuller_coeff_zero]
  exists_eq_π_mul := by
    rintro _ ⟨y, rfl⟩ h0
    have h1 : y.coeff 0 = 0 := by
      have : (incl K p y).coeff 0 = 0 := h0
      rw [incl_coeff] at this
      exact (map_eq_zero_iff _ (IsFractionRing.injective 𝒪♭ K♭)).1 this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero y).2 h1)
    exact ⟨incl K p z, ⟨z, rfl⟩, by rw [← hz, map_mul, map_natCast, mul_comm]⟩
  mem_int_of_approx := by
    intro x hx
    have hc : ∀ n, ∃ b : 𝒪♭, algebraMap 𝒪♭ K♭ b = x.coeff n := by
      intro n
      obtain ⟨y, ⟨z, rfl⟩, hy⟩ := hx (n + 1)
      have h := (mem_span_p_pow_iff_le_coeff_eq_zero _ _).1 hy
      have := (le_coeff_eq_iff_le_sub_coeff_eq_zero.2 h) n (Nat.lt_succ_self n)
      exact ⟨z.coeff n, by rw [this, incl_coeff]⟩
    choose b hb using hc
    refine ⟨WittVector.mk p b, ?_⟩
    ext n
    rw [incl_coeff, ← hb n]
    rfl
def tcoeff (x : AInf K p) (n : ℕ) : 𝒪♭ := ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) (x.coeff n)
theorem isUnit_incl_p : IsUnit (algebraMap (WittVector p K♭) (teichLift K p).B
    (incl K p (p : AInf K p))) := by
  rw [map_natCast]
  exact IsLocalization.Away.algebraMap_isUnit (teichLift K p).π
variable (K p) in

def toB : 𝔸 →+* (teichLift K p).B :=
  Localization.awayLift ((algebraMap (WittVector p K♭) (teichLift K p).B).comp (incl K p))
    (p : AInf K p) isUnit_incl_p
end WittTilt
end GroundTheory.PAdicHodge


