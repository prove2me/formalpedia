-- Prove2me | Definitions.Def_TaoFivePrimes_RHMoments304
-- name    : TaoFivePrimes_RHMoments304
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:47:35.877469+00:00
-- url     : https://prove2.me/theorems/5fcf875a-1fe1-4315-995e-8a0d205a1a92
-- title:
--   Candidate scaled even Mellin moments through index 303
-- statement:
--   For each nonnegative index $j$, this function selects the previously published candidate for $j<272$ and the newly stored rational candidate for $272\le j<304$:
--
--   $$
--   \widetilde M_j=\begin{cases}\widetilde M_j^{\mathrm{old}},&j<272,\\C_j/10^{64},&272\le j<304.\end{cases}
--   $$
--
--   This is a candidate data interface; an error bound relative to the true Mellin moments is a separate theorem.
-- source:
--   Derived from the proved all-index Mellin rule and cached integer identity. The theta-jet and Mellin framework is due to sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The higher moment numerators are new.

/- Candidate scaled even Mellin moments through index 303.
The first 272 candidates and the theta-jet data are due to the cited
prior certificates; the remaining 32 candidates require separate proofs. -/
import Definitions.Def_TaoFivePrimes_RHMoments272
import Definitions.Def_TaoFivePrimes_RHExtendedMomentData272to303
set_option autoImplicit false

noncomputable def TaoFivePrimes_RHMoments304 (j : ℕ) : ℝ :=
  if j<272 then TaoFivePrimes_RHMoments272 j
  else (TaoFivePrimes_RHExtendedMomentData272to303.getD (j-272) 0:ℝ)/(10^64:ℝ)


