-- Prove2me | Definitions.Def_Yukon_987f95a0aff41d97f83b5198
-- name    : Yukon_987f95a0aff41d97f83b5198
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T20:09:41.602889+00:00
-- url     : https://prove2.me/theorems/eca6af17-0dd1-4f04-8ccc-7bc708d5e074
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceReducedTailWeights6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-84ce212b3dfb158cff9ba42023ad5b4b7e5be5ae0a714544b8d2b67b9efc5882
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMmM0ZDA2M2ExOTM2ZDYxOTYxZGY0NmM3MDAwNDk3YzRlNjY5ZDNkNjQ1NzBhMzI4OTFhNzMxNDRjYWMyNDc2ZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtODRjZTIxMmIzZGZiMTU4Y2ZmOWJhNDIwMjNhZDViNGI3ZTViZTVhZTBhNzE0NTQ0YjhkMmI2N2I5ZWZjNTg4MiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzk4N2Y5NWEwYWZmNDFkOTdmODNiNTE5OCIsInYiOjJ9]

import Definitions.Def_Yukon_18c42113a620563a44636057
















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Degree bounds for the actual replacement tails, proved by the
recurrence. No expansion of the 131072nd polynomial is performed. -/
namespace ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial RCN234 RCN156
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814

variable {K : Type} [Field K]
local notation "Poly" => MvPolynomial (Fin 4) K

theorem product_derivative_weight
    (w : Fin 4 → ℕ) (A P : Poly) (i : Fin 4) (c d : ℕ)
    (hA : wt w A≤d+w i) (hP : wt w P≤c) :
    wt w (A*pderiv i P)≤c+d := by
  by_cases hi : w i≤c
  · have hp := wt_pderiv_le w P i c hP
    have hm := wt_mul_le w A (pderiv i P)
    omega
  · have hz : pderiv i P=0 := RCN262.pderiv_eq_zero_of_wt_lt w P i (hP.trans_lt (by omega))
    rw [hz,mul_zero]
    simp [wt,MvPolynomial.weightedTotalDegree]

theorem flow_weight
    (w : Fin 4 → ℕ) (H G P : Poly) (c h d : ℕ)
    (hH : wt w H≤h) (hG : wt w G≤d+w 2)
    (hx : h≤d+w 0) (hy : w 2+h≤d+w 1) (hP : wt w P≤c) :
    wt w (flow H G P)≤c+d := by
  have hRH : wt w (MvPolynomial.X 2*H)≤d+w 1 := by
    have hh := wt_mul_le w (MvPolynomial.X 2) H
    rw [wt_X] at hh
    omega
  have h0 := product_derivative_weight w H P 0 c d (hH.trans hx) hP
  have h1 := product_derivative_weight w (MvPolynomial.X 2*H) P 1 c d hRH hP
  have h2 := product_derivative_weight w G P 2 c d hG hP
  have he : flow H G P=H*pderiv 0 P+(MvPolynomial.X 2*H)*pderiv 1 P+G*pderiv 2 P := by
    rw [flow_apply]
    ring
  rw [he]
  exact (wt_add_le w _ _).trans (max_le
    ((wt_add_le w _ _).trans (max_le h0 h1)) h2)

theorem step_weight
    (w : Fin 4 → ℕ) (H G P : Poly) (c h d n : ℕ)
    (hH : wt w H≤h) (hG : wt w G≤d+w 2)
    (hx : h≤d+w 0) (hy : w 2+h≤d+w 1) (hP : wt w P≤c) :
    wt w (step H G n P)≤c+(h+d) := by
  have hDP := flow_weight w H G P c h d hH hG hx hy hP
  have hDH := flow_weight w H G H h h d hH hG hx hy hH
  have hleft := wt_mul_le w H (flow H G P)
  have hscale := wt_mul_le w ((2*n : ℕ) : Poly) P
  rw [wt_natCast,zero_add] at hscale
  have hright := wt_mul_le w (((2*n : ℕ) : Poly)*P) (flow H G H)
  rw [step_eq]
  exact (wt_sub_le w _ _).trans (max_le (by omega) (by omega))

theorem numerator_weight
    (w : Fin 4 → ℕ) (H G : Poly) (h d : ℕ)
    (hH : wt w H≤h) (hG : wt w G≤d+w 2)
    (hx : h≤d+w 0) (hy : w 2+h≤d+w 1) (n : ℕ) :
    wt w (numerators H G n)≤w 1+n*(h+d) := by
  induction n with
  | zero => simp [numerators,wt_X]
  | succ n ih =>
    have hh := step_weight w H G (numerators H G n) (w 1+n*(h+d)) h d n hH hG hx hy ih
    change wt w (step H G n (numerators H G n))≤_
    convert hh using 1; ring

theorem linear_tail_weights
    (J : WholeSpaceCube6814.Poly (K:=K))
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤7 ∧ e 1+e 2+e 3≤25 ∧ e 1+e 2+e 3+e 4≤331)
    (n : ℕ) :
    wt residualSWeights (numerators (linearH J) (linearG J) n)≤11*n ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) n)≤1+48*n ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) n)≤1+660*n := by
  have hh := linear_coefficient_weights J 7 25 331 hshape
  have hR := numerator_weight residualSWeights (linearH J) (linearG J) 5 6
    hh.1.1 hh.2.1 (by decide) (by decide) n
  have hY := numerator_weight residualYSWeights (linearH J) (linearG J) 24 24
    hh.1.2.1 hh.2.2.1 (by decide) (by decide) n
  have hT := numerator_weight residualTotalWeights (linearH J) (linearG J) 330 330
    hh.1.2.2 hh.2.2.2 (by decide) (by decide) n
  refine ⟨?_,?_,?_⟩
  · simpa only [show residualSWeights 1=0 from rfl,zero_add,Nat.reduceAdd,Nat.mul_comm] using hR
  · simpa only [show residualYSWeights 1=1 from rfl,Nat.reduceAdd,Nat.mul_comm] using hY
  · simpa only [show residualTotalWeights 1=1 from rfl,Nat.reduceAdd,Nat.mul_comm] using hT








end
end ProximityPrize.SubmissionLower.MovingSourceReducedTailWeights6814


