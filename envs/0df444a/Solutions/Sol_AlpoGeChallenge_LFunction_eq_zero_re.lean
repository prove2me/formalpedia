-- Prove2me | solution 1 for AlpoGeChallenge.LFunction_eq_zero_re
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T22:36:30.628748+00:00
-- url     : https://prove2.me/submissions/1f11a779-0493-483f-950c-a9311f1c9afd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive

open DirichletCharacter Complex

namespace HubA

/-- An Euler factor `1 - χ(p) p^{-s}` is nonzero for `Re s > 0`. -/
lemma euler_factor_ne_zero {M : ℕ} (χ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0 < s.re) : (1 : ℂ) - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : χ p * (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hlt : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos]
    have hχ : ‖χ (p : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hpow : (p : ℝ) ^ (-s).re < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simp; linarith)
    calc ‖χ (p : ZMod M)‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re := by gcongr
      _ < 1 := by simpa using hpow
  rw [h1, norm_one] at hlt
  exact lt_irrefl _ hlt

end HubA

theorem solution :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2 := by
  intro N _ χ s h0 h1 hL
  have hs1 : s ≠ 1 := fun h => by simp [h] at h1
  have hc0 : χ.conductor ≠ 0 := fun h =>
    (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))
  have : NeZero χ.conductor := ⟨hc0⟩
  have hfac := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (s := s) (Or.inr hs1)
  rw [changeLevel_primitiveCharacter, hL] at hfac
  have hprod : ∏ p ∈ N.primeFactors,
      ((1 : ℂ) - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      HubA.euler_factor_ne_zero _ (Nat.prime_of_mem_primeFactors hp) h0
  rcases mul_eq_zero.mp hfac.symm with h | h
  · exact AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive χ.conductor χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive s h0 h1 h
  · exact absurd h hprod
