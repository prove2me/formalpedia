-- Prove2me | Definitions.Def_Yukon_be6ea3475ffb6078ec93f154
-- name    : Yukon_be6ea3475ffb6078ec93f154
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T16:30:53.526355+00:00
-- url     : https://prove2.me/theorems/b282ce3d-3123-4c1c-83a1-0905288453e9
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberPackingSemantics6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberPackingSemantics6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberPackingSemantics6814.lean
--
--   yukon-proof-operation:certificate-split-20993f5f4d287263572e2a2c9ddb7c2f1d74153097a97dc464cec8e28dc957d3
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNzIzNDgyMDRmYzI3NzRjMWIxMDRhZmEyNzI4ZDVmNzAwZTVjZjc4YzhmMDM0MmQ1OTA1ODU3MGVlNmJkNGMzNCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTIwOTkzZjVmNGQyODcyNjM1NzJlMmEyYzlkZGI3YzJmMWQ3NDE1MzA5N2E5N2RjNDY0Y2VjOGUyOGRjOTU3ZDMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9iZTZlYTM0NzVmZmI2MDc4ZWM5M2YxNTQiLCJ2IjoyfQ]

import Definitions.Def_Yukon_223642192d853991eed59b0f

import Definitions.Def_Yukon_a9cebfaf25c2bf4c44008ec1










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberPackingSemantics6814
open MovingFiberPackingCheck6814
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def lookup (rows : Nat → Array Nat) (r v : Nat) : Nat := ((rows r)[v]?).getD 0




theorem symmetric_bellman (own packed : Nat → Array Nat)
    (hown : ∀ r, 1≤r → r≤37 → (own r).size=176-r)
    (hpacked : ∀ r, r≤37 → (packed r).size=176-r)
    (hunder : ∀ r, 1≤r → r≤37 → shifted 0 (own r).toList (packed r).toList=true)
    (hchecks : ∀ R r, 2*r≤R → R≤37 →
      convolution (packed r).toList (packed (R-r)).toList (packed R).toList=true) :
    AffineFactorAggregate6808.BellmanRows 37 175 (lookup own) (lookup packed) := by
  intro r v R V hr hR hV
  have hu := shifted_sound 0 (own r).toList (packed r).toList (hunder r hr (by omega)) v
    (by rw [Array.length_toList,hown r hr (by omega)]; omega)
    (by rw [Array.length_toList,hpacked r (by omega)]; omega)
  have hle : lookup own r v ≤ lookup packed r v := by
    simpa only [Array.getElem?_toList,lookup,Nat.zero_add] using hu
  apply (Nat.add_le_add_right hle _).trans
  by_cases hsplit : r≤R
  · have he : r+R-r=R := by omega
    have hc := hchecks (r+R) r (by omega) hR
    rw [he] at hc
    have h := convolution_sound (packed r).toList (packed R).toList (packed (r+R)).toList hc v V
      (by rw [Array.length_toList,hpacked r (by omega)]; omega)
      (by rw [Array.length_toList,hpacked R (by omega)]; omega)
      (by rw [Array.length_toList,hpacked (r+R) hR]; omega)
    simpa only [Array.getElem?_toList,lookup] using h
  · have he : r+R-R=r := by omega
    have hc := hchecks (r+R) R (by omega) hR
    rw [he] at hc
    have h := convolution_sound (packed R).toList (packed r).toList (packed (r+R)).toList hc V v
      (by rw [Array.length_toList,hpacked R (by omega)]; omega)
      (by rw [Array.length_toList,hpacked r (by omega)]; omega)
      (by rw [Array.length_toList,hpacked (r+R) hR]; omega)
    simpa only [Array.getElem?_toList,lookup,Nat.add_comm] using h





end ProximityPrize.SubmissionLower.MovingFiberPackingSemantics6814


