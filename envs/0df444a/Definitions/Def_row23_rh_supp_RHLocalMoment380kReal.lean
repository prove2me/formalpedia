-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMoment380kReal
-- name    : row23_rh_supp_RHLocalMoment380kReal
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:17:34.00842+00:00
-- url     : https://prove2.me/theorems/f26efebb-d219-4e99-b3de-13d7f4ebca47
-- title:
--   Row 23 RH support: RHLocalMoment380kReal
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreMomentFormulaIntervals
import Definitions.Def_row23_rh_supp_RHLocalMoment380kModel
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace DusartLegendreSmoothing.Moment380k
open RationalRows
 def logBounds (p : Parameters) (d : Data) : Prop :=
  (d.L0:ℝ) ≤ Real.log ((lowHeight:ℝ)/(2*Real.pi)) ∧
  Real.log ((lowHeight:ℝ)/(2*Real.pi)) ≤ (d.U0:ℝ) ∧
  Real.log ((lowHeight:ℝ)+5) ≤ (d.V0:ℝ) ∧
  (d.LT:ℝ) ≤ Real.log ((p.T:ℝ)/(2*Real.pi)) ∧
  Real.log ((p.T:ℝ)/(2*Real.pi)) ≤ (d.UT:ℝ) ∧
  Real.log ((p.T:ℝ)+5) ≤ (d.VT:ℝ) ∧
  (d.LH:ℝ) ≤ Real.log ((highHeight:ℝ)/(2*Real.pi)) ∧
  Real.log ((highHeight:ℝ)/(2*Real.pi)) ≤ (d.UH:ℝ) ∧
  Real.log ((highHeight:ℝ)+5) ≤ (d.VH:ℝ)
 theorem real_moment_caps (p : Parameters) (d : Data) (hc : checks p d) (hl : logBounds p d) :
    2*positiveLowMomentBound (lowHeight:ℝ) (p.T:ℝ) (d.S:ℝ) ≤ (p.B₁:ℝ) ∧
    2*positiveMomentBandBound (p.m-1) (p.T:ℝ) (highHeight:ℝ) ≤ (p.B₂:ℝ) ∧
    2*positiveMomentTailBound (p.m-1) (highHeight:ℝ) ≤ (p.B₃:ℝ) := by
  rcases hc with ⟨hm,hTa,hTH,hL0,hLU0,hLT,hLUT,hLH,hLUH,hc1,hc2,hc3⟩
  rcases hl with ⟨h0L,h0U,h0V,hTL,hTU,hTV,hHL,hHU,hHV⟩
  have ha0 : (0:ℝ) < lowHeight := by norm_num [lowHeight]
  have hH0 : (0:ℝ) < highHeight := by norm_num [highHeight]
  have hTaR : (lowHeight:ℝ) ≤ (p.T:ℝ) := by exact_mod_cast hTa
  have hT0 : (0:ℝ) < p.T := ha0.trans_le hTaR
  have hL0R : (0:ℝ) < d.L0 := by exact_mod_cast hL0
  have hLTR : (0:ℝ) < d.LT := by exact_mod_cast hLT
  have hLHR : (0:ℝ) < d.LH := by exact_mod_cast hLH
  have hPL0 : (0:ℝ) < piLower := by norm_num [piLower]
  have hPlo : (piLower:ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d20.le
    norm_num [piLower] at h ⊢
    exact h
  have hPhi : Real.pi ≤ (piUpper:ℝ) := by
    have h := Real.pi_lt_d20.le
    norm_num [piUpper] at h ⊢
    exact h
  have hn : p.m-1+1=p.m := by omega
  have hn2 : p.m-1+2=p.m+1 := by omega
  have hr : ((p.m-1:ℕ):ℝ)+1=(p.m:ℝ) := by exact_mod_cast hn
  have h1 : 2*positiveLowMomentBound (lowHeight:ℝ) (p.T:ℝ) (d.S:ℝ) ≤ (lowUpper p d:ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (low_moment_interval (lowHeight:ℝ) (p.T:ℝ) (d.S:ℝ) (piLower:ℝ) (piUpper:ℝ)
        (d.L0:ℝ) (d.U0:ℝ) (d.LT:ℝ) (d.UT:ℝ) (d.V0:ℝ)
        ha0 hPL0 hPlo hPhi hL0R h0L h0U hLTR hTL hTU h0V) (by norm_num : (0:ℝ) ≤ 2)
    unfold lowUpper slopeUpper slopeLower
    push_cast
    norm_num [piLower,piUpper,lowHeight] at h ⊢
    exact h
  have h2 : 2*positiveMomentBandBound (p.m-1) (p.T:ℝ) (highHeight:ℝ) ≤ (bandUpper p d:ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (moment_band_interval (p.m-1) (p.T:ℝ) (highHeight:ℝ) (piLower:ℝ) (piUpper:ℝ)
        (d.LT:ℝ) (d.UT:ℝ) (d.LH:ℝ) (d.UH:ℝ) (d.VT:ℝ)
        hT0 hH0 hPL0 hPlo hPhi hLTR hTL hTU hLHR hHL hHU hTV) (by norm_num : (0:ℝ) ≤ 2)
    norm_num only [hn,hn2,hr] at h
    unfold bandUpper slopeUpper slopeLower primitive
    push_cast
    norm_num [piLower,piUpper,highHeight] at h ⊢
    exact h
  have h3 : 2*positiveMomentTailBound (p.m-1) (highHeight:ℝ) ≤ (tailUpper p d:ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (moment_tail_interval (p.m-1) (highHeight:ℝ) (piLower:ℝ) (piUpper:ℝ)
        (d.LH:ℝ) (d.UH:ℝ) (d.VH:ℝ) hH0 hPL0 hPlo hPhi hLHR hHL hHU hHV)
      (by norm_num : (0:ℝ) ≤ 2)
    norm_num only [hn,hn2,hr] at h
    unfold tailUpper slopeUpper primitive
    push_cast
    norm_num [piLower,highHeight] at h ⊢
    exact h
  exact ⟨h1.trans (Rat.cast_mono (K:=ℝ) hc1),h2.trans (Rat.cast_mono (K:=ℝ) hc2),
    h3.trans (Rat.cast_mono (K:=ℝ) hc3)⟩
end DusartLegendreSmoothing.Moment380k
#print axioms DusartLegendreSmoothing.Moment380k.real_moment_caps


