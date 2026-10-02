-- Prove2me | Definitions.Def_Yukon_692ed2187892c979cf600940
-- name    : Yukon_692ed2187892c979cf600940
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T08:54:24.148963+00:00
-- url     : https://prove2.me/theorems/5af0cb6e-2eb5-4c7f-a355-ff570a35036c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeCoefficientAffine6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCoefficientAffine6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCoefficientAffine6814.lean
--
--   yukon-proof-operation:foundation-direct-a3636ea92837985c8199eb3f5bf9c6be8cdd6980d3be85ae981eb77f7a7628a5
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZWU0ZmM2MDdmZDAzMWM0MDMzNDYyOTUxMzgwYmMzYjA3ZmFkOTJjNDRiMGUzZmRhMGU2NWNiMmJjZDc4ZGIzYiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWEzNjM2ZWE5MjgzNzk4NWM4MTk5ZWIzZjViZjljNmJlOGNkZDY5ODBkM2JlODVhZTk4MWViNzdmN2E3NjI4YTUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl82OTJlZDIxODc4OTJjOTc5Y2Y2MDA5NDAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_20e9cbe0f908e5fcbffc0920









































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeCertificate6814
open LocatorFastKernelArithmetic RCN100
set_option autoImplicit false
set_option maxHeartbeats 700000

def oneSlope (q r w s : ℕ) : ℕ :=
  (r+q)*(smallChoose (q+2) 2-smallChoose (q+1-s) 2)+
    (w-2)*(smallChoose (q+2) 3-smallChoose (q+1-s) 3)

def oneIntercept (q r w s : ℕ) : ℤ :=
  (oneResidueCoefficientCount q r w q s : ℤ)-(oneSlope q r w s : ℤ)*q

theorem oneResidue_affine_nat (q r w L s : ℕ) (hL : q≤L) :
    oneResidueCoefficientCount q r w L s+oneSlope q r w s*q=
      oneResidueCoefficientCount q r w q s+oneSlope q r w s*L := by
  have hU := Nat.sub_add_cancel (show q≤L+1 by omega)
  have hh := congrArg (fun x : ℕ => oneSlope q r w s*x) hU
  unfold oneResidueCoefficientCount oneSlope at *
  simp only [show q+1-q=1 by omega,one_mul] at *
  nlinarith only [hh]

theorem oneResidue_affine (q r w L s : ℕ) (hL : q≤L) :
    (oneResidueCoefficientCount q r w L s : ℤ)=
      (oneSlope q r w s : ℤ)*L+oneIntercept q r w s := by
  have hh : (oneResidueCoefficientCount q r w L s : ℤ)+(oneSlope q r w s : ℤ)*q=
      (oneResidueCoefficientCount q r w q s : ℤ)+(oneSlope q r w s : ℤ)*L := by
    exact_mod_cast oneResidue_affine_nat q r w L s hL
  unfold oneIntercept
  omega

def coefficientSlope (q r w s : ℕ) : ℕ :=
  if r+s≤w then oneSlope q r w s else
    oneSlope q r w (w-r-1)+oneSlope (q+1-(w-r)) 0 w (s-(w-r))

def coefficientIntercept (q r w s : ℕ) : ℤ :=
  if r+s≤w then oneIntercept q r w s else
    oneIntercept q r w (w-r-1)+oneIntercept (q+1-(w-r)) 0 w (s-(w-r))-
      (oneSlope (q+1-(w-r)) 0 w (s-(w-r)) : ℤ)*(w-r)

theorem coefficientCount_affine (q r w L s : ℕ)
    (hw : 2≤w) (hr : r<w) (hs : s<w) (hsq : s≤q) (hL : q+1≤L) :
    (coefficientCount (q*w+r) w L s : ℤ)=
      (coefficientSlope q r w s : ℤ)*L+coefficientIntercept q r w s := by
  rw [coefficientCount_eq_twoResidue q r w L s hw hr hs hsq hL]
  unfold twoResidueCoefficientCount coefficientSlope coefficientIntercept
  split_ifs with hfirst
  · exact oneResidue_affine q r w L s (by omega)
  · rw [Nat.cast_add,oneResidue_affine q r w L (w-r-1) (by omega),
      oneResidue_affine (q+1-(w-r)) 0 w (L-(w-r)) (s-(w-r)) (by omega),
      Nat.cast_sub (show w-r≤L by omega),Nat.cast_sub (show r≤w by omega),Nat.cast_add]
    ring



end ProximityPrize.SubmissionLower.RelativeCertificate6814


