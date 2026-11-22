-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:05:55.572864+00:00
-- url     : https://prove2.me/theorems/e0c68266-d401-4b7b-bf89-a4d011f3782e
-- title:
--   Kernel
-- statement:
--   Definitions and structural lemmas for Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Kernel.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


set_option autoImplicit false
noncomputable section
open Ideal
namespace Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
theorem exists_pow_eq_of_isAlgClosed {R : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsAlgClosed (FractionRing R)] (a : R) {n : ℕ} (hn : 0 < n) : ∃ b : R, b ^ n = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap R (FractionRing R) a) hn
  have hi : IsIntegral R z := IsIntegral.of_pow hn (hz ▸ isIntegral_algebraMap)
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨b, IsFractionRing.injective R (FractionRing R) (by rw [map_pow, hz])⟩
namespace Tilt
variable (p R) in

def sharpEquiv : Tilt p R ≃* Perfection R p :=
  (Perfection.quotientMulEquiv p (span {(p : R)})).symm
theorem coeff_zero_sharpEquiv (x : Tilt p R) :
    Perfection.coeffMonoidHom R p 0 (sharpEquiv p R x) = PreTilt.untilt x :=
  Perfection.coeff_zero_symm_quotientMulEquiv x
theorem untilt_sharpEquiv_symm (y : Perfection R p) :
    PreTilt.untilt ((sharpEquiv p R).symm y) = Perfection.coeffMonoidHom R p 0 y := by
  rw [← coeff_zero_sharpEquiv, MulEquiv.apply_symm_apply]
theorem coeff_sharpEquiv_pow (x : Tilt p R) (n : ℕ) :
    Perfection.coeffMonoidHom R p n (sharpEquiv p R x) ^ p ^ n = PreTilt.untilt x := by
  rw [Perfection.coeffMonoidHom_pow_p_pow_self, coeff_zero_sharpEquiv]
@[simp] theorem untilt_zero : PreTilt.untilt (0 : Tilt p R) = 0 := Perfection.teichmuller_zero
variable [IsDomain R]
theorem untilt_eq_zero_iff (x : Tilt p R) : PreTilt.untilt x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ untilt_zero⟩
  apply (sharpEquiv p R).injective
  refine Perfection.extMonoid fun n => ?_
  have h1 := coeff_sharpEquiv_pow x n
  have h2 := coeff_sharpEquiv_pow (0 : Tilt p R) n
  rw [h] at h1
  rw [untilt_zero] at h2
  rw [pow_eq_zero_iff (pow_pos (Fact.out : p.Prime).pos n).ne'] at h1 h2
  rw [h1, h2]
instance isDomain : IsDomain (Tilt p R) := by
  have : Nontrivial (Tilt p R) :=
    ⟨(CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one).1⟩
  have : NoZeroDivisors (Tilt p R) := ⟨fun {a b} h => by
    rw [← untilt_eq_zero_iff, map_mul, mul_eq_zero, untilt_eq_zero_iff, untilt_eq_zero_iff] at h
    exact h⟩
  exact NoZeroDivisors.to_isDomain _
theorem dvd_iff_untilt_dvd [IsIntegrallyClosed R] (x y : Tilt p R) :
    x ∣ y ↔ PreTilt.untilt x ∣ PreTilt.untilt y := by
  refine ⟨fun h => map_dvd _ h, fun h => ?_⟩
  by_cases hx : x = 0
  · subst hx
    rw [untilt_zero, zero_dvd_iff, untilt_eq_zero_iff] at h
    rw [h]
  have hp := (Fact.out : p.Prime).pos
  have hne : ∀ n, Perfection.coeffMonoidHom R p n (sharpEquiv p R x) ≠ 0 := by
    intro n hn
    have h1 := coeff_sharpEquiv_pow x n
    rw [hn, zero_pow (pow_pos hp n).ne', eq_comm, untilt_eq_zero_iff] at h1
    exact hx h1
  have hd : ∀ n, Perfection.coeffMonoidHom R p n (sharpEquiv p R x) ∣
      Perfection.coeffMonoidHom R p n (sharpEquiv p R y) := by
    intro n
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff (pow_pos hp n).ne', coeff_sharpEquiv_pow,
      coeff_sharpEquiv_pow]
    exact h
  choose c hc using hd
  have hcp : ∀ n, c (n + 1) ^ p = c n := by
    intro n
    apply mul_left_cancel₀ (hne n)
    rw [← hc, ← Perfection.coeffMonoidHom_pow_p' (sharpEquiv p R x) n, ← mul_pow, ← hc,
      Perfection.coeffMonoidHom_pow_p']
  obtain ⟨z, hz⟩ : ∃ z : Perfection R p, ∀ n, Perfection.coeffMonoidHom R p n z = c n :=
    ⟨⟨c, hcp⟩, fun _ => rfl⟩
  refine ⟨(sharpEquiv p R).symm z, (sharpEquiv p R).injective ?_⟩
  rw [map_mul, MulEquiv.apply_symm_apply]
  refine Perfection.extMonoid fun n => ?_
  rw [map_mul, hc, hz]
variable [ValuationRing R]
instance valuationRing : ValuationRing (Tilt p R) :=
  { cond' := fun a b => by
      rcases ValuationRing.dvd_total (PreTilt.untilt a) (PreTilt.untilt b) with h | h
      · obtain ⟨c, hc⟩ := (dvd_iff_untilt_dvd a b).2 h
        exact ⟨c, Or.inl hc.symm⟩
      · obtain ⟨c, hc⟩ := (dvd_iff_untilt_dvd b a).2 h
        exact ⟨c, Or.inr hc.symm⟩ }
theorem untilt_surjective [IsAlgClosed (FractionRing R)] :
    Function.Surjective (PreTilt.untilt : Tilt p R → R) := by
  intro a
  choose r hr using fun b : R => exists_pow_eq_of_isAlgClosed b (Fact.out : p.Prime).pos
  refine ⟨(sharpEquiv p R).symm ⟨fun n => r^[n] a, fun n => ?_⟩, ?_⟩
  · beta_reduce
    rw [Function.iterate_succ_apply', hr]
  · exact (untilt_sharpEquiv_symm _).trans rfl
end Tilt
instance PFlat.nonempty_of_isAlgClosed [IsDomain R] [ValuationRing R]
    [IsAlgClosed (FractionRing R)] : Nonempty (PFlat p R) :=
  let ⟨x, hx⟩ := Tilt.untilt_surjective (p := p) (p : R)
  ⟨⟨x, hx⟩⟩
namespace Ainf
def xi (ϖ : PFlat p R) : Ainf p R := (p : Ainf p R) - teich p ϖ.1
variable [IsDomain R]
instance isDomain : IsDomain (Ainf p R) := inferInstanceAs (IsDomain (WittVector p (Tilt p R)))
instance charZero_of_charZero [CharZero R] : CharZero (Ainf p R) := (theta p R).charZero
theorem p_ne_zero : (p : Ainf p R) ≠ 0 := WittVector.p_nonzero p _
variable [ValuationRing R]
variable [CharZero R]
end Ainf
def tateRoot (η : tateModule p R) : Tilt p R := (frobeniusEquiv (Tilt p R) p).symm η.1
namespace Ainf
def omega (ε : tateModule p R) : Ainf p R := ∑ i ∈ Finset.range p, teich p (tateRoot ε) ^ i
variable [IsDomain R]
variable [ValuationRing R] [CharZero R]
end Ainf
namespace AinfInv
variable [IsDomain R]
instance isDomain : IsDomain (AinfInv p R) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Ainf.p_ne_zero (p := p) (R := R)))
variable [ValuationRing R]
variable [CharZero R]
end AinfInv
end Reformulated.AutPerF


