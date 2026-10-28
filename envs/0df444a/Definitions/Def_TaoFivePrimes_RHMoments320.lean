-- Prove2me | Definitions.Def_TaoFivePrimes_RHMoments320
-- name    : TaoFivePrimes_RHMoments320
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:30:08.377428+00:00
-- url     : https://prove2.me/theorems/c90ff153-fd07-4a94-a4b3-a50230c0a1c8
-- title:
--   Candidate scaled Mellin moments through index 319
-- statement:
--   For $j<304$, the function selects the previously published moment candidate; for $304\le j<320$ it selects the newly stored numerator divided by $10^{64}$. This definition records candidate data, and its error relative to the true moments is a separate theorem.
-- source:
--   Derived from the proved all-index Mellin rule and cached integer identity. The theta-jet and Mellin framework is due to sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The higher moment numerators are new.

/- Candidate scaled even Mellin moments through index 319.
The earlier moment candidates and theta-jet data are due to the cited prior
certificates; the 16 additional candidates require independent checking. -/
import Definitions.Def_TaoFivePrimes_RHMoments304
import Definitions.Def_TaoFivePrimes_RHExtendedMomentData304to319
set_option autoImplicit false

noncomputable def TaoFivePrimes_RHMoments320 (j : ℕ) : ℝ :=
  if j<304 then TaoFivePrimes_RHMoments304 j
  else (TaoFivePrimes_RHExtendedMomentData304to319.getD (j-304) 0:ℝ)/(10^64:ℝ)


