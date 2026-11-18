-- Prove2me | solution 1 for AC02Frege.fact_2_5_multiplication_rule
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-17T06:05:06.454291+00:00
-- url     : https://prove2.me/submissions/7b42c1a4-ee35-48e0-93ea-e044515ac2c8

import Theorems.Thm_AC02Frege_pcDerivable_mul_of_totalDegree_le
import Theorems.Thm_AC02Frege_pcDerivable_multilinearization

open MvPolynomial AC02Frege

private theorem ml_monomial {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl]
  rw [h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

private theorem ml_multilinear {V : Type*} (p : MvPolynomial V (ZMod 2)) :
    IsMultilinear (ML p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [ml_monomial]
    intro t ht v
    have ht' : t = sqfree s := (Finset.mem_singleton.mp (support_monomial_subset ht))
    subst t
    simp [sqfree, Finsupp.mapRange_apply]
  | add p q hp hq =>
    rw [map_add]
    intro s hs v
    rcases Finset.mem_union.mp (support_add hs) with hs | hs
    · exact hp s hs v
    · exact hq s hs v


theorem solution {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : u ∈ CD F D) (hv : IsMultilinear v)
    (hdeg : u.totalDegree + v.totalDegree ≤ D) : ML (u * v) ∈ CD F D := by
  exact ⟨ml_multilinear (u * v),
    AC02Frege.pcDerivable_multilinearization F D (u * v)
      (AC02Frege.pcDerivable_mul_of_totalDegree_le F D u v hu.2 hdeg)⟩
