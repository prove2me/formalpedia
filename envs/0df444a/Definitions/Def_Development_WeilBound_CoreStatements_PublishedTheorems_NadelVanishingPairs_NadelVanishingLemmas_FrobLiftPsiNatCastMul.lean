-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobLiftPsiNatCastMul
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_FrobLiftPsiNatCastMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:48.588529+00:00
-- url     : https://prove2.me/theorems/7687ebe4-3ba1-469b-b1ca-2c6561d0b19d
-- title:
--   Frob Lift Psi Nat Cast Mul
-- statement:
--   Definitions and structural lemmas for Frob Lift Psi Nat Cast Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/FrobLiftPsiNatCastMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehlerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.DI
section FrobDiff
variable {K : Type} [CommRing K]
theorem kaehlerD_aeval_fin_two (x : Fin 2 → K) (P : MvPolynomial (Fin 2) ℤ) :
    KaehlerDifferential.D ℤ K (aeval x P) =
      ∑ i, aeval x (pderiv i P) • KaehlerDifferential.D ℤ K (x i) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hP, Finset.smul_sum, smul_smul,
      Derivation.leibniz, pderiv_X, Fin.sum_univ_two]
    fin_cases i <;> simp [add_smul, mul_comm, smul_smul, Pi.single_apply] <;> abel
theorem ringHom_aeval_fin_two {Kt : Type} [CommRing Kt] (π : Kt →+* K) (x : Fin 2 → Kt)
    (P : MvPolynomial (Fin 2) ℤ) : π (aeval x P) = aeval (fun i => π (x i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP => simp [hP]
variable {Kt : Type} [CommRing Kt] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (π : Kt →+* K) (F : Kt →+* Kt)
theorem frobLift_exists_w (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    ∃ w, F z = z ^ p + p * w := by
  obtain ⟨w, hw⟩ := (hL.ker (F z - z ^ p)).1 (by rw [map_sub, hF, map_pow, sub_self])
  exact ⟨w, by rw [← hw]; ring⟩
theorem frobLift_w_unique (hL : IsFlatLift p π) {z w w' : Kt} (h : F z = z ^ p + p * w)
    (h' : F z = z ^ p + p * w') : π w = π w' := by
  have e : (p : Kt) * (w - w') = 0 := by
    have := h.symm.trans h'
    rw [mul_sub, sub_eq_zero]
    exact add_left_cancel this
  have e2 := (hL.ann _).mp e
  rwa [map_sub, sub_eq_zero] at e2
theorem kaehlerD_pow_char (x : K) : KaehlerDifferential.D ℤ K (x ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
def frobLiftPsi (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) : Ω[K⁄ℤ] :=
  π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
    KaehlerDifferential.D ℤ K (π (frobLift_exists_w p π F hL hF z).choose)
variable {p π F}
theorem frobLiftPsi_spec (hL : IsFlatLift p π) (hF : IsFrob p π F) {z w : Kt}
    (h : F z = z ^ p + p * w) :
    frobLiftPsi p π F hL hF z = π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
      KaehlerDifferential.D ℤ K (π w) := by
  unfold frobLiftPsi
  rw [frobLift_w_unique p π F hL (frobLift_exists_w p π F hL hF z).choose_spec h]
theorem frobLiftPsi_add (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z + z') = frobLiftPsi p π F hL hF z + frobLiftPsi p π F hL hF z' := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (X 0 : MvPolynomial (Fin 2) ℤ) (X 1)
  have hp0 : (p : MvPolynomial (Fin 2) ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨C, hC0⟩ : ∃ C : MvPolynomial (Fin 2) ℤ,
      (p : MvPolynomial (Fin 2) ℤ) * C = (X 0 + X 1) ^ p - X 0 ^ p - X 1 ^ p :=
    ⟨X 0 * X 1 * r, by rw [hr]; ring⟩
  have hpd0 : pderiv 0 C = (X 0 + X 1) ^ (p - 1) - X 0 ^ (p - 1) := by
    have := congrArg (pderiv 0) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hpd1 : pderiv 1 C = (X 0 + X 1) ^ (p - 1) - X 1 ^ (p - 1) := by
    have := congrArg (pderiv 1) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hc : (z + z') ^ p = z ^ p + z' ^ p + p * aeval ![z, z'] C := by
    have := congrArg (aeval ![z, z']) hC0
    simp at this
    rw [this]
    ring
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w + w' - aeval ![z, z'] C) (by rw [map_add, hw, hw', hc]; ring)]
  have hD : KaehlerDifferential.D ℤ K (π (aeval ![z, z'] C)) =
      ((π z + π z') ^ (p - 1) - π z ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z) +
      ((π z + π z') ^ (p - 1) - π z' ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z') := by
    rw [ringHom_aeval_fin_two, kaehlerD_aeval_fin_two, Fin.sum_univ_two, hpd0, hpd1]
    simp
  simp only [map_add, map_sub, hD, smul_add, sub_smul]
  abel
theorem frobLiftPsi_natCast_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (y : Kt) :
    frobLiftPsi p π F hL hF ((p : Kt) * y) = 0 := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hp2 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have e : (p : Kt) * (p : Kt) ^ (p - 1) = (p : Kt) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp1]
  rw [frobLiftPsi_spec hL hF (w := F y - (p : Kt) ^ (p - 1) * y ^ p)
    (by rw [map_mul, map_natCast, mul_pow]; linear_combination (y ^ p) * e)]
  simp [hpK, hF y, kaehlerD_pow_char p, zero_pow hp2]
theorem frobLiftPsi_congr (hL : IsFlatLift p π) (hF : IsFrob p π F) {z z' : Kt} (h : π z = π z') :
    frobLiftPsi p π F hL hF z = frobLiftPsi p π F hL hF z' := by
  obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, h, sub_self])
  rw [show z = z' + (p : Kt) * y by rw [← hy]; ring, frobLiftPsi_add, frobLiftPsi_natCast_mul, add_zero]
def frobLiftPhi (hL : IsFlatLift p π) (hF : IsFrob p π F) : K →+ Ω[K⁄ℤ] where
  toFun a := frobLiftPsi p π F hL hF (Function.surjInv hL.surj a)
  map_zero' := by
    have h0 : frobLiftPsi p π F hL hF 0 = 0 := by
      have := frobLiftPsi_add hL hF (0 : Kt) 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    rw [frobLiftPsi_congr hL hF (z' := 0) (by rw [Function.surjInv_eq hL.surj, map_zero]), h0]
  map_add' a b := by
    rw [← frobLiftPsi_add, frobLiftPsi_congr hL hF (z' := Function.surjInv hL.surj a + Function.surjInv hL.surj b)
      (by rw [map_add, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])]
end FrobDiff
end GlobalTheory.DI


