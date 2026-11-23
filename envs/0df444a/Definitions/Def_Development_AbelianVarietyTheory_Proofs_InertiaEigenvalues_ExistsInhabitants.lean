-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInhabitants
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInhabitants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:04.871141+00:00
-- url     : https://prove2.me/theorems/794f2a82-8ccb-4ba6-aee7-f133b99f8879
-- title:
--   Exists Inhabitants
-- statement:
--   Definitions and structural lemmas for Exists Inhabitants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsInhabitants.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma
open Polynomial IsLocalRing
section
variable (p : ℕ) [hp : Fact p.Prime]
theorem frob_algebraMap (x : WittVector p (GaloisField p 2)) :
    WittVector.FractionRing.frobenius p (GaloisField p 2) (algebraMap _ _ x) =
      algebraMap _ (FractionRing (WittVector p (GaloisField p 2))) (WittVector.frobenius x) := by
  simp [WittVector.FractionRing.frobenius]
theorem witt_max : maximalIdeal (WittVector p (GaloisField p 2)) = Ideal.span {(p : WittVector p (GaloisField p 2))} :=
  (WittVector.irreducible p).maximalIdeal_eq
def wittResEquiv : ResidueField (WittVector p (GaloisField p 2)) ≃+* GaloisField p 2 :=
  (Ideal.quotEquivOfEq (witt_max p)).trans WittVector.quotientPEquiv
theorem galois_pow (x : GaloisField p 2) : (x ^ p) ^ p = x := by
  letI := Fintype.ofFinite (GaloisField p 2)
  have hc : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p _ two_ne_zero]
  rw [← pow_mul, ← pow_two, ← hc, FiniteField.pow_card]
theorem galois_exists : ∃ x : GaloisField p 2, x ^ p ≠ x := by
  by_contra h
  push_neg at h
  letI := Fintype.ofFinite (GaloisField p 2)
  have hc : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p _ two_ne_zero]
  have h1 := hp.out.one_lt
  have hz : (X ^ p - X : (GaloisField p 2)[X]) = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (f := id) _ Function.injective_id
    · intro i; simp [h i]
    · rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ h1, hc]; nlinarith
  exact FiniteField.X_pow_card_sub_X_ne_zero _ h1 hz
def wittUQ : UQ where
  O := WittVector p (GaloisField p 2)
  E := FractionRing (WittVector p (GaloisField p 2))
  cpl := by rw [witt_max]; infer_instance
  fin := Finite.of_equiv _ (wittResEquiv p).toEquiv.symm
  c0 := by
    haveI : CharZero (WittVector p (GaloisField p 2)) := by
      obtain ⟨r, hr⟩ := CharP.exists (WittVector p (GaloisField p 2))
      rcases CharP.char_is_prime_or_zero (WittVector p (GaloisField p 2)) r with h | h
      · exfalso
        have h0 : ((r : ℕ) : WittVector p (GaloisField p 2)) = 0 := CharP.cast_eq_zero _ r
        have h1 : ((r : ℕ) : GaloisField p 2) = 0 := by
          rw [← map_natCast (WittVector.constantCoeff (p := p) (R := GaloisField p 2)), h0, map_zero]
        have h2 := (CharP.cast_eq_zero_iff (GaloisField p 2) p r).1 h1
        have h3 := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h2
        exact WittVector.p_nonzero p (GaloisField p 2) (by rw [← h3] at h0; exact h0)
      · subst h; exact CharP.charP_to_charZero _
    exact charZero_of_injective_algebraMap (IsFractionRing.injective (WittVector p (GaloisField p 2)) _)
  c := WittVector.FractionRing.frobenius p (GaloisField p 2)
  c_c := by
    intro x
    have : ((WittVector.FractionRing.frobenius p (GaloisField p 2)).toRingHom.comp
        (WittVector.FractionRing.frobenius p (GaloisField p 2)).toRingHom) = RingHom.id _ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p (GaloisField p 2))) (RingHom.ext fun y => ?_)
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, frob_algebraMap, RingHom.id_apply]
      congr 1
      ext i
      rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, galois_pow]
    exact RingHom.congr_fun this x
  c_int := fun x => ⟨_, frob_algebraMap p x⟩
  c_res := by
    obtain ⟨t, ht⟩ := galois_exists p
    refine ⟨WittVector.teichmuller p t, _, frob_algebraMap p _, ?_⟩
    rw [witt_max, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP, WittVector.teichmuller_coeff_zero, sub_eq_zero]
    exact ht.symm
  q := p
  card_res := by rw [Nat.card_congr (wittResEquiv p).toEquiv, GaloisField.card p _ two_ne_zero]
end
abbrev InvAlg.line (K : UQ) (g : K.E) : InvAlg K where
  A := K.E
  σ := K.c
  σ_σ := K.c_c
  σ_alg := fun _ => rfl
  g := g
def InvAlg.split (K : UQ) (t : K.E) : InvAlg K where
  A := K.E × K.E
  σ := (RingEquiv.prodCongr K.c K.c).trans RingEquiv.prodComm
  σ_σ := fun y => Prod.ext (K.c_c y.1) (K.c_c y.2)
  σ_alg := fun _ => rfl
  g := (t, K.c t)
end GlobalTheory.UnitLemma


