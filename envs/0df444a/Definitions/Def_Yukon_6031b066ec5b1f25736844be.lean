-- Prove2me | Definitions.Def_Yukon_6031b066ec5b1f25736844be
-- name    : Yukon_6031b066ec5b1f25736844be
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T01:15:47.971494+00:00
-- url     : https://prove2.me/theorems/c6df181a-5472-416c-98dc-b069c0b46593
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceCarrierZeros6814.lean
--
--   yukon-proof-operation:certificate-tail-0b3c201ad79516bcceed52fccc4ca297ffdda461797bbbb9ac019fe6ed0bcfc7
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzlkNWY1MGIxNzJiZjRlYWQ5MjdhYjY4N2U3ZTc0ZjQ1ZjA5YzBhNjdlNTA5NmNlNjMxN2MwNDBkNjU3NGM2ZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXRhaWwtMGIzYzIwMWFkNzk1MTZiY2NlZWQ1MmZjY2M0Y2EyOTdmZmRkYTQ2MTc5N2JiYmI5YWMwMTlmZTZlZDBiY2ZjNyIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzYwMzFiMDY2ZWM1YjFmMjU3MzY4NDRiZSIsInYiOjJ9]

import Definitions.Def_Yukon_cab3e47590aea7a2fd8756f8














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Lift a root in the faithful generic carrier field to a polynomial
identity on the carrier, then transfer it to every regular moving point.
A root in an arbitrary closed-point field is not substituted for this. -/
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
open MvPolynomial RCN136 RCN207 SecondJetCoefficients SecondJetClearedHelper
open SecondJetCarrierDichotomy MovingSourceClearing6814

variable {K E : Type*} [Field K] [Field E]

theorem helper_dvd_of_generic_root
    (P : WholeSpaceCube6814.Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (phi : MvPolynomial (Fin 4) K →+* E)
    (hker : ∀ A, phi A=0 ↔ F ∣ A)
    (s : ℕ) (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hH : phi (2*RCN313.polyH K F)≠0)
    (hroot : ((asS P).map phi).eval (ratio phi F)=0) : F ∣ helper P F s 0 := by
  apply (hker _).mp
  have hh := mapped_helper P F phi s 0 hS hH
  simpa only [Nat.sub_zero,Function.iterate_zero,id_eq,hroot,mul_zero] using hh

theorem simple_root_vanishes (P : Polynomial E) (x : E)
    (h : P.rootMultiplicity x=1) : P.eval x=0 := by
  by_contra hn
  have hz := Polynomial.rootMultiplicity_eq_zero hn
  rw [h] at hz
  omega








end
end ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814


