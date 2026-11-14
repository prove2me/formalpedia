-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendrePositiveZeroTail
-- name    : row23_rh_supp_RHLegendrePositiveZeroTail
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:01:57.588378+00:00
-- url     : https://prove2.me/theorems/6968f5fe-1f31-41e7-afd9-e91bd0cdeb87
-- title:
--   Row 23 RH support: RHLegendrePositiveZeroTail
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreFiniteZeroMoments
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
open DusartSmoothing Set
lemma zeroCountSlope_nonneg (a : ℝ) (ha : 1000 ≤ a) : 0 ≤ zeroCountSlope a := by
  have ha0 : 0 < a := by linarith
  have hlog : 0 < Real.log (a/(2*Real.pi)) := by
    apply Real.log_pos
    apply (lt_div_iff₀ (by positivity : 0 < 2*Real.pi)).2
    linarith [Real.pi_lt_four]
  unfold zeroCountSlope
  positivity
 theorem finite_positive_zero_moment_tail (k : ℕ) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a : ℝ) (ha : 1000 ≤ a) (hγ : ∀ ρ ∈ Z, a < ρ.im) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ:ℝ)*(1/ρ.im^(k+2))) ≤
      2*(9*Real.log (a+5)+79)/a^(k+2)+zeroCountSlope a*
      ((1+((k:ℝ)+1)*Real.log (a/(2*Real.pi)))/(((k:ℝ)+1)^2*a^(k+1))) := by
  classical
  have ha0 : 0 < a := by linarith
  let b : ℝ := a+∑ ρ ∈ Z, |ρ.im|
  have hab : a ≤ b := by
    dsimp only [b]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun ρ _ => abs_nonneg _))
  have hb0 : 0 < b := ha0.trans_le hab
  have hγb (ρ : ℂ) (hρ : ρ ∈ Z) : ρ.im ≤ b := by
    have hs : |ρ.im| ≤ ∑ τ ∈ Z, |τ.im| :=
      Finset.single_le_sum (fun τ _ => abs_nonneg τ.im) hρ
    dsimp only [b]
    linarith [le_abs_self ρ.im]
  have h := finite_positive_zero_moment_band k Z hZ a b ha hab
    (fun ρ hρ => ⟨hγ ρ hρ,hγb ρ hρ⟩)
  have hbLog : 0 ≤ Real.log (b/(2*Real.pi)) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).2
    linarith [Real.pi_lt_four]
  have he : 0 ≤ (1+((k:ℝ)+1)*Real.log (b/(2*Real.pi)))/(((k:ℝ)+1)^2*b^(k+1)) := by positivity
  have hh : zeroCountSlope a*
      ((1+((k:ℝ)+1)*Real.log (a/(2*Real.pi)))/(((k:ℝ)+1)^2*a^(k+1))-
       (1+((k:ℝ)+1)*Real.log (b/(2*Real.pi)))/(((k:ℝ)+1)^2*b^(k+1))) ≤
      zeroCountSlope a*((1+((k:ℝ)+1)*Real.log (a/(2*Real.pi)))/(((k:ℝ)+1)^2*a^(k+1))) :=
    mul_le_mul_of_nonneg_left (sub_le_self _ he) (zeroCountSlope_nonneg a ha)
  exact h.trans (add_le_add le_rfl hh)
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.finite_positive_zero_moment_tail


