-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_ord_eq_one_of_ord_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/a0643e3a-c931-52a4-aeed-ac0382abecf1

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one.AlgebraicCurve Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_zero"
namespace Place
p2m_export "AlgebraicCurve.Place" "adicValuation adicValuation_ne_zero adicValuation_coe ord ord_zero algebraMap_mem' toValuationSubring"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.c3a_adicValuation_le_exp_neg_iff (f : F) (n : ℤ) :
    v.adicValuation f ≤ WithZero.exp (-n) ↔ f = 0 ∨ n ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have hne := v.adicValuation_ne_zero hf
    rw [← WithZero.log_le_iff_le_exp hne]
    simp only [hf, false_or, ord]
    omega

p2m_export "AlgebraicCurve.Place" "c3a_adicValuation_le_exp_neg_iff"

private theorem _root_.AlgebraicCurve.Place.c3a_adicValuation_algebraMap_le_one (c : K) : v.adicValuation (algebraMap K F c) ≤ 1 := by
  have h : algebraMap K F c = ((⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) : F) := rfl
  rw [h, v.adicValuation_coe]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

p2m_export "AlgebraicCurve.Place" "c3a_adicValuation_algebraMap_le_one"
end AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (c : ι → K) (f : ι → F)
    (hf : ∀ i ∈ s, f i = 0 ∨ 1 ≤ v.ord (f i))
    (h : v.ord (∑ i ∈ s, algebraMap K F (c i) * f i) = 1) :
    ∃ i ∈ s, v.ord (f i) = 1 := by
  classical
  by_contra hcon
  push Not at hcon

  have hterm : ∀ i ∈ s,
      v.adicValuation (algebraMap K F (c i) * f i) ≤ WithZero.exp (-(2 : ℤ)) := by
    intro i hi
    rcases hf i hi with h0 | h1
    · simp [h0]
    · have h2 : (2 : ℤ) ≤ v.ord (f i) := by
        have := hcon i hi
        omega
      rw [map_mul]
      calc v.adicValuation (algebraMap K F (c i)) * v.adicValuation (f i)
          ≤ 1 * WithZero.exp (-(2 : ℤ)) :=
            mul_le_mul' (v.c3a_adicValuation_algebraMap_le_one (c i))
              ((v.c3a_adicValuation_le_exp_neg_iff (f i) 2).mpr (Or.inr h2))
        _ = WithZero.exp (-(2 : ℤ)) := one_mul _

  have hsum := (v.c3a_adicValuation_le_exp_neg_iff _ 2).mp (v.adicValuation.map_sum_le hterm)
  rcases hsum with h0 | h2
  · rw [h0, AlgebraicCurve.Place.ord_zero] at h
    exact zero_ne_one h
  · omega

#print axioms solution

end S_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_ord_eq_one_of_ord_sum_eq_one (solution)
