-- Prove2me | Definitions.Def_Yukon_20e9cbe0f908e5fcbffc0920
-- name    : Yukon_20e9cbe0f908e5fcbffc0920
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T08:39:53.195529+00:00
-- url     : https://prove2.me/theorems/04e4c9d3-5ac5-45c1-8056-80a07d3e1aa4
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeTwoResidueCounts6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeTwoResidueCounts6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeTwoResidueCounts6814.lean
--
--   yukon-proof-operation:foundation-direct-13730135f1425ec1edee54a99578882913085822dbe896e94b9821bfa922bf1c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNmYwOTUwNjQ0NDI1YjU1MDAxZTc5MDJjYTkxY2M5YTViNzJlNjA5ZjcxMDdmODgyODFiZmQyOTA2NzhhOTEzNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTEzNzMwMTM1ZjE0MjVlYzFlZGVlNTRhOTk1Nzg4ODI5MTMwODU4MjJkYmU4OTZlOTRiOTgyMWJmYTkyMmJmMWMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yMGU5Y2JlMGY5MDhlNWZjYmZmYzA5MjAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_f60f8771f49612b2e4c0149e

import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561








































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Extend the existing closed coefficient formula across the one residue
boundary occurring in the saved relative certificates. No large source
coefficient space is enumerated. -/
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open scoped BigOperators
open RCN100 LocatorFastKernelArithmetic
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 20000

theorem coefficientCount_split_slope (D w L s h : ℕ)
    (hh : 0<h) (hs : h≤s) (hL : h≤L) :
    coefficientCount D w L s=
      coefficientCount D w L (h-1)+coefficientCount (D-(w-1)*h) w (L-h) (s-h) := by
  have hc (D L s : ℕ) : coefficientCount D w L s=
      ∑ j∈Finset.range (s+1), ∑ i∈Finset.range (L+1), (L+1-i-j)*(D-w*i-(w-1)*j) := by
    unfold coefficientCount
    exact Finset.sum_comm
  rw [hc D L s,hc D L (h-1),hc (D-(w-1)*h) (L-h) (s-h)]
  have he : s+1=h+(s-h+1) := by omega
  conv_lhs => rw [he,Finset.sum_range_add]
  rw [show h-1+1=h by omega]
  apply congrArg₂ (fun a b : ℕ => a+b)
  · rfl
  · apply Finset.sum_congr rfl
    intro j hj
    have htrim :
        (∑ i∈Finset.range (L-h+1), (L+1-i-(h+j))*(D-w*i-(w-1)*(h+j)))=
        ∑ i∈Finset.range (L+1), (L+1-i-(h+j))*(D-w*i-(w-1)*(h+j)) := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i hi hn
      have hi' := Finset.mem_range.mp hi
      have hn' : L-h+1 ≤ i := by simpa using hn
      have hz : L+1-i-(h+j)=0 := by omega
      simp only [hz,zero_mul]
    rw [←htrim]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    · omega
    · rw [Nat.mul_add]
      omega

def twoResidueCoefficientCount (q r w L s : ℕ) : ℕ :=
  if r+s≤w then oneResidueCoefficientCount q r w L s else
    oneResidueCoefficientCount q r w L (w-r-1)+
    oneResidueCoefficientCount (q+1-(w-r)) 0 w (L-(w-r)) (s-(w-r))

theorem coefficientCount_eq_twoResidue (q r w L s : ℕ)
    (hw : 2≤w) (hr : r<w) (hs : s<w) (hsq : s≤q) (hL : q+1≤L) :
    coefficientCount (q*w+r) w L s=twoResidueCoefficientCount q r w L s := by
  unfold twoResidueCoefficientCount
  split_ifs with hfirst
  · exact coefficientCount_eq_oneResidueCoefficientCount q r w L s hw hsq (by omega) hfirst
  · have hh : 0<w-r := by omega
    have hhs : w-r≤s := by omega
    have hhq : w-r≤q := by omega
    have hprod : (w-1)*(w-r)≤q*w+r := by
      have h := Nat.mul_le_mul (show w-1≤w by omega) hhq
      nlinarith
    have hcut : q*w+r-(w-1)*(w-r)=(q+1-(w-r))*w := by
      have h1 := Nat.sub_add_cancel hprod
      have h2 := Nat.sub_add_cancel (show w-r≤q+1 by omega)
      have h3 := Nat.sub_add_cancel (show r≤w by omega)
      have h4 : w-1+1=w := by omega
      nlinarith
    rw [coefficientCount_split_slope (q*w+r) w L s (w-r) hh hhs (by omega),hcut]
    rw [coefficientCount_eq_oneResidueCoefficientCount q r w L (w-r-1) hw (by omega) (by omega) (by omega)]
    simpa only [Nat.add_zero] using congrArg
      (fun x => oneResidueCoefficientCount q r w L (w-r-1)+x)
      (coefficientCount_eq_oneResidueCoefficientCount (q+1-(w-r)) 0 w (L-(w-r)) (s-(w-r))
        hw (by omega) (by omega) (by omega))



end ProximityPrize.SubmissionLower.RelativeCertificate6814


