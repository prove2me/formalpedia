-- Prove2me | Definitions.Def_row23_rh_supp_RHLegendreSmoothCountEnvelope
-- name    : row23_rh_supp_RHLegendreSmoothCountEnvelope
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T21:59:02.387722+00:00
-- url     : https://prove2.me/theorems/b74a3011-9c52-4698-bcf3-f0726dfbc73d
-- title:
--   Row 23 RH support: RHLegendreSmoothCountEnvelope
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreZeroCountIncrement
import Mathlib.Analysis.Calculus.Deriv.MeanValue
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing
open DusartSmoothing Set
noncomputable def zeroCountSlope (a : ℝ) : ℝ :=
  1/(2*Real.pi)+9/(a*Real.log (a/(2*Real.pi)))
noncomputable def smoothCountEnvelope (a t : ℝ) : ℝ :=
  2*Real.pi*zeroCountSlope a*(RvM.countingMain t-RvM.countingMain a)+
    2*(9*Real.log (a+5)+79)
 theorem counting_error_increment_le_density (a t : ℝ) (ha : 1000 ≤ a) (hat : a ≤ t) :
    9*(Real.log (t+5)-Real.log (a+5)) ≤
      (9/(a*Real.log (a/(2*Real.pi))))*(2*Real.pi)*
        (RvM.countingMain t-RvM.countingMain a) := by
  have ha0 : 0 < a := by linarith
  have hπ : 0 < 2*Real.pi := by positivity
  have hla : 0 < Real.log (a/(2*Real.pi)) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hπ).2
    linarith [Real.pi_lt_four]
  let q : ℝ := 9/(a*Real.log (a/(2*Real.pi)))
  have hq : 0 < q := by dsimp [q]; positivity
  let f : ℝ → ℝ := fun u => q*(2*Real.pi)*(RvM.countingMain u-RvM.countingMain a)-
    9*(Real.log (u+5)-Real.log (a+5))
  have hD (u : ℝ) (hu : u ∈ Icc a t) :
      HasDerivAt f (q*Real.log (u/(2*Real.pi))-9/(u+5)) u := by
    have hu0 : 0 < u := ha0.trans_le hu.1
    have hL := (Real.hasDerivAt_log (by linarith : u+5 ≠ 0)).comp u
      ((hasDerivAt_id u).add_const 5)
    have hC := ((RvM.hasDerivAt_countingMain u hu0).sub_const (RvM.countingMain a)).const_mul (q*(2*Real.pi))
    have h := hC.sub ((hL.sub_const (Real.log (a+5))).const_mul 9)
    change HasDerivAt f _ u at h
    apply h.congr_deriv
    field_simp [Real.pi_ne_zero,show u+5 ≠ 0 by linarith]
    <;> ring
  have hnonneg (u : ℝ) (hu : u ∈ Icc a t) :
      0 ≤ q*Real.log (u/(2*Real.pi))-9/(u+5) := by
    have hl : Real.log (a/(2*Real.pi)) ≤ Real.log (u/(2*Real.pi)) :=
      Real.log_le_log (div_pos ha0 hπ) (div_le_div_of_nonneg_right hu.1 hπ.le)
    have hbase : q*Real.log (a/(2*Real.pi))=9/a := by
      dsimp [q]
      field_simp [ha0.ne',hla.ne']
    have hmul := mul_le_mul_of_nonneg_left hl hq.le
    rw [hbase] at hmul
    have hi : (9:ℝ)/(u+5) ≤ 9/a :=
      div_le_div_of_nonneg_left (by norm_num) ha0 (by linarith [hu.1])
    linarith
  have hmono : MonotoneOn f (Icc a t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a t)
    · intro u hu
      exact (hD u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hD u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hD u (interior_subset hu)).deriv]
      exact hnonneg u (interior_subset hu)
  have hh := hmono ⟨le_rfl,hat⟩ ⟨hat,le_rfl⟩ hat
  dsimp only [f] at hh
  simp only [sub_self,mul_zero,sub_zero] at hh
  dsimp only [q] at hh
  linarith only [hh]
 theorem finite_zero_count_smooth_envelope (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a t : ℝ) (ha : 1000 ≤ a) (hat : a ≤ t) (hγ : ∀ ρ ∈ Z, a < ρ.im) :
    finiteZeroCount Z RvM.zeroMult Complex.im t ≤ smoothCountEnvelope a t := by
  have hi := finite_zero_count_increment_bound Z hZ a t (by linarith) hat hγ
  have he := counting_error_increment_le_density a t ha hat
  have hEq : smoothCountEnvelope a t =
      (RvM.countingMain t-RvM.countingMain a)+
      (9/(a*Real.log (a/(2*Real.pi))))*(2*Real.pi)*
        (RvM.countingMain t-RvM.countingMain a)+2*(9*Real.log (a+5)+79) := by
    unfold smoothCountEnvelope zeroCountSlope
    have hpi : (2*Real.pi)*(1/(2*Real.pi))=1 := by field_simp [Real.pi_ne_zero]
    rw [mul_add,hpi]
    ring
  rw [hEq]
  nlinarith only [hi,he]
end DusartLegendreSmoothing
#print axioms DusartLegendreSmoothing.finite_zero_count_smooth_envelope


