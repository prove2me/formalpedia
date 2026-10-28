-- Prove2me | Definitions.Def_TaoFivePrimes_RHMoments336
-- name    : TaoFivePrimes_RHMoments336
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:05:22.050042+00:00
-- url     : https://prove2.me/theorems/64897a7f-e9e5-40f4-b041-e091bee3c542
-- title:
--   Candidate scaled Mellin moments through index 335
-- statement:
--   For $j<320$, the function selects the previously published moment candidate; for $320\le j<336$ it selects the newly stored numerator divided by $10^{64}$. This definition records candidate data, not an enclosure.
-- source:
--   Derived from the proved all-index Mellin rule and cached integer identity. The theta-jet and Mellin framework is due to sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The higher moment numerators are new.

/- Candidate scaled even Mellin moments through index 335. -/
import Definitions.Def_TaoFivePrimes_RHMoments320
import Definitions.Def_TaoFivePrimes_RHExtendedMomentData320to335
set_option autoImplicit false
noncomputable def TaoFivePrimes_RHMoments336 (j : ℕ) : ℝ :=
  if j<320 then TaoFivePrimes_RHMoments320 j
  else (TaoFivePrimes_RHExtendedMomentData320to335.getD (j-320) 0:ℝ)/(10^64:ℝ)


