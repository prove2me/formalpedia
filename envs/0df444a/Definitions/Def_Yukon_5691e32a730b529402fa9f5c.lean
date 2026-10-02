-- Prove2me | Definitions.Def_Yukon_5691e32a730b529402fa9f5c
-- name    : Yukon_5691e32a730b529402fa9f5c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:28:55.427641+00:00
-- url     : https://prove2.me/theorems/15e018cc-c905-47d2-b349-cae2015f604e
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberLeadingCoefficient6814.lean
--
--   yukon-proof-operation:foundation-direct-0073e1e6bc6e40438b00b315a840a7098636f450d1eb8381dde1ff6da5e3a4e8
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMWM2NjY4MmFjMTc3MTJmZjg2MGJiYjlhNzdhZmNlODMxYmQ5N2EzZWIzMTg3YTc3YmIxYjFjYmVhOTkwMzc1YSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTAwNzNlMWU2YmM2ZTQwNDM4YjAwYjMxNWE4NDBhNzA5ODYzNmY0NTBkMWViODM4MWRkZTFmZjZkYTVlM2E0ZTgiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81NjkxZTMyYTczMGI1Mjk0MDJmYTlmNWMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_63a16e90b7724a1f71186e13








































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6814
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetDifferentiation
open SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N : Type*} [Field K]

theorem coefficient_monomial_degree (f : Polynomial K) (z : K) (w : ℕ)
    (hf : f.natDegree ≤ w) (e : Fin 4 →₀ ℕ) (c : K) :
    (coefficientSpecialize f z (MvPolynomial.monomial e c)).natDegree ≤
      e 0+w*e 1+(w-1)*e 2 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow]
    have hc : (coefficientSpecialize f z (MvPolynomial.C c)).natDegree ≤ 0 := by
      simp [coefficientSpecialize]
    have h0 : (coefficientSpecialize f z (MvPolynomial.X 0)^e 0).natDegree ≤ e 0 := by
      simp [coefficientSpecialize]
    have h1 : (coefficientSpecialize f z (MvPolynomial.X 1)^e 1).natDegree ≤ e 1*w := by
      simpa [coefficientSpecialize] using Polynomial.natDegree_pow_le_of_le (e 1) hf
    have h2 : (coefficientSpecialize f z (MvPolynomial.X 2)^e 2).natDegree ≤ e 2*(w-1) := by
      simpa [coefficientSpecialize] using Polynomial.natDegree_pow_le_of_le (e 2)
        ((Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1))
    have h3 : (coefficientSpecialize f z (MvPolynomial.X 3)^e 3).natDegree ≤ 0 := by
      simp [coefficientSpecialize]
    have hh := Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2 h3)))
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Nat.mul_comm] using hh
  · intro i
    simp

theorem coefficient_degree (P : MvPolynomial (Fin 4) K) (f : Polynomial K)
    (z : K) (w D : ℕ) (hf : f.natDegree ≤ w) (hD : 0 < D)
    (hP : ∀ e ∈ P.support, e 0+w*e 1+(w-1)*e 2 < D) :
    (coefficientSpecialize f z P).natDegree < D := by
  classical
  have ht : ∀ e ∈ P.support,
      (coefficientSpecialize f z (MvPolynomial.monomial e (MvPolynomial.coeff e P))).natDegree ≤ D-1 := by
    intro e he
    have hh := coefficient_monomial_degree f z w hf e (MvPolynomial.coeff e P)
    have hb := hP e he
    omega
  rw [MvPolynomial.as_sum P, map_sum]
  have hh := Polynomial.natDegree_sum_le_of_forall_le P.support
    (fun e => coefficientSpecialize f z (MvPolynomial.monomial e (MvPolynomial.coeff e P))) ht
  omega

theorem iterate_derivative_top {R : Type*} [CommRing R] (P : Polynomial R) (d : ℕ)
    (hh : ∀ j, d < j → P.coeff j = 0) :
    (Polynomial.derivative)^[d] P = Polynomial.C (d.factorial • P.coeff d) := by
  ext j
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hj : j = 0
  · subst j
    simp [Nat.descFactorial_self]
  · rw [hh (j+d) (by omega)]
    simp [hj]

theorem specialize_top (P : Poly (K := K)) (f : Polynomial K) (z : K) (d : ℕ)
    (hh : ∀ j, d < j → coefficientSpecialize f z ((asS P).coeff j) = 0) :
    specialize f z ((pderiv 1)^[d] P) =
      d.factorial • coefficientSpecialize f z ((asS P).coeff d) := by
  rw [specialize_eq, asS_iterate, ← Polynomial.eval_map, ← Polynomial.iterate_derivative_map]
  rw [iterate_derivative_top _ d (by intro j hj; simpa using hh j hj)]
  simp

theorem low_coefficient_vanish (P : Poly (K := K)) (m k n0 d : ℕ)
    (hdm : d < m) (hdn : d < n0) (hfact : (d.factorial : K) ≠ 0)
    (hP : ∀ e ∈ P.support,
      e 0+131071*e 2+131070*e 3+131069*e 1+
        reserve k n0 (e 1)*50186 < m*181255)
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hcontact : ∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (f : Polynomial K) (hf : f.natDegree ≤ 131071) (z : K) (S : Finset N)
    (hS : 181255 ≤ S.card) (hvalues : ∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z)
    (hh : ∀ j, d < j → coefficientSpecialize f z ((asS P).coeff j) = 0) :
    coefficientSpecialize f z ((asS P).coeff d) = 0 := by
  have hweight : ∀ e ∈ ((asS P).coeff d).support,
      e 0+131071*e 1+131070*e 2 < (m-d)*181255 := by
    intro e he
    have hb := hP _ (coefficient_support P d e he)
    obtain ⟨h0,h1,h2,h3,h4⟩ := lift_coordinates d e
    rw [h0,h1,h2,h3] at hb
    simp only [reserve,if_pos hdn] at hb
    omega
  have hdeg := coefficient_degree ((asS P).coeff d) f z 131071 ((m-d)*181255)
    hf (by omega) hweight
  have htop := specialize_top P f z d hh
  have hv : specialize f z ((pderiv 1)^[d] P) = 0 := by
    refine SecondJetVanish.eq_zero_of_contact_degree _ f z nodes u0 u1 S (m-d) ?_ hvalues ?_
    · intro i _
      apply SecondJetGlobalDifferentiation.local_derivative_contact
      simpa only [Nat.sub_add_cancel (Nat.le_of_lt hdm)] using hcontact i
    · rw [htop]
      have hs := Polynomial.natDegree_smul_le d.factorial
        (coefficientSpecialize f z ((asS P).coeff d))
      exact (hs.trans_lt hdeg).trans_le (Nat.mul_le_mul_left (m-d) hS)
  rw [htop,nsmul_eq_mul] at hv
  apply (mul_eq_zero.mp hv).resolve_left
  simpa only [map_natCast] using (Polynomial.C_ne_zero.mpr hfact)

end
end ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6814


