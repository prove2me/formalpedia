-- Prove2me | Definitions.Def_Yukon_b9264d25766439028c5b06aa
-- name    : Yukon_b9264d25766439028c5b06aa
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T21:01:50.496507+00:00
-- url     : https://prove2.me/theorems/6ece8009-8bb8-47e0-a4a0-bf96f77fbf47
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceLinearTailTransport6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-281091873955443cb5f343ad4e4904f3fd5ea7798233ded68e0194f0fbe5d529
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNTI0MzY5MDk1ZDFjN2NjMjJhYzVlZTIyN2RmZTViMjU1MTU4NGE5MDAwOTlhMWI2OGMxMjM0NmRjYzY2NWU3ZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtMjgxMDkxODczOTU1NDQzY2I1ZjM0M2FkNGU0OTA0ZjNmZDVlYTc3OTgyMzNkZWQ2OGUwMTk0ZjBmYmU1ZDUyOSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2I5MjY0ZDI1NzY2NDM5MDI4YzViMDZhYSIsInYiOjJ9]

import Definitions.Def_Yukon_6fa19eb79d6770597b78bb32















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Transport the actual global tail cuts, their DVR orders, and their
first proper delays. The code-coordinate scalar in globalTailCut is
handled explicitly; it is a unit at the generic code coordinate. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN086 RCN136 RCN313
open MovingSourceFlowNumerator6814 MovingSourceDenominatorChange6814

variable {K Ω R : Type} [Field K] [Field Ω] [CommRing R] [IsDomain R]
local notation "Poly" => MvPolynomial (Fin 4) K




theorem global_tails_associated
    (phi : Polynomial K →+* Ω) (hphi : Function.Injective phi)
    (ev : MvPolynomial (Fin 3) Ω →+* R) (F H G : Poly) (n : ℕ)
    (hF : ev (surfaceMap phi F)=0)
    (hOld : IsUnit (ev (surfaceMap phi (polyH K F)))) (hNew : IsUnit (ev (surfaceMap phi H)))
    (hdiv : F∣H^(2*n)*numerator K F n-(polyH K F)^(2*n)*numerators H G n) :
    Associated (ev (globalTailCut phi F n)) (ev (surfaceMap phi (numerators H G n))) := by
  have hh := tails_associated (ev.comp (surfaceMap phi)) F H G n hF hOld hNew hdiv
  have hu : IsUnit ((-phi Polynomial.X)^n) :=
    isUnit_iff_ne_zero.mpr (tail_scalar_ne_zero phi hphi n)
  have hu' : IsUnit (ev (MvPolynomial.C ((-phi Polynomial.X)^n))) :=
    (hu.map (MvPolynomial.C : Ω →+* MvPolynomial (Fin 3) Ω)).map ev
  rw [globalTailCut_eq,map_mul]
  exact (associated_mul_unit_left _ _ hu').trans hh
















end
end ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814


