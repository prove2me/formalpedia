-- Prove2me | Definitions.Def_TaoFivePrimes_RHMoments272
-- name    : TaoFivePrimes_RHMoments272
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:13:27.45365+00:00
-- url     : https://prove2.me/theorems/de9baab5-2ce1-4879-87b1-22c9aba42981
-- title:
--   Candidate scaled even Mellin moments through index 271
-- statement:
--   For each nonnegative integer $j$, this function selects the published candidate moment for $j<256$ and selects the new stored rational candidate for $256\le j<272$.
--
--   $$
--   \widetilde M_j=\begin{cases}C_j/10^{64},&0\le j<272,\end{cases}
--   $$
--
--   The function combines two sets of finite data. Its numerical relationship to the actual moments is a separate theorem.
-- source:
--   Derived here from the exact theta-jet and Mellin quadrature framework of sometik179, Prove2Me c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham.

/- Candidate list of 272 scaled even Mellin moments. The original first 256
entries come from sometik179's certificate (theta/Mellin: Gabewhigham); the
last 16 are separately generated candidate numerators. This definition asserts
no analytic enclosure by itself. -/
import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Definitions.Def_TaoFivePrimes_RHExtendedMomentData256to271
set_option autoImplicit false

noncomputable def TaoFivePrimes_RHMoments272 (j : ℕ) : ℝ :=
  if j<256 then CertifiedGlobalMomentEnclosure.candidateMoment j
  else (TaoFivePrimes_RHExtendedMomentData256to271.getD (j-256) 0:ℝ)/(10^64:ℝ)


