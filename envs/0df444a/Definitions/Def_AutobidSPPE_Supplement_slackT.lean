-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_slackT
-- name    : AutobidSPPE_Supplement_slackT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:43:13.55809+00:00
-- url     : https://prove2.me/theorems/b5859c95-d7a5-4280-b66e-f45c1e6ea2a5
-- title:
--   Coefficient slack $\Delta_i(S)$
-- statement:
--   The **coefficient slack** of bidder $i$ against the rival set $S$ is
--   $$
--   \Delta_i(S)=c_i(S)-\sum_{j\in S}\big|c_i(S)-c_i(S\setminus\{j\})\big|.
--   $$
--   Theorem 3.17 assumes it is nonnegative for every rival set and positive for the full rival set.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §3.12, p.38

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_coefT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The coefficient slack `Δᵢ(S) = cᵢ(S) − Σ_{j∈S} |cᵢ(S) − cᵢ(S∖{j})|` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §3.12,
p.38). -/
noncomputable def slackT {n : ℕ} (vbar : Fin n → ℝ) (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  coefT vbar i S - ∑ j ∈ S, |coefT vbar i S - coefT vbar i (S.erase j)|

end AutobidSPPE.Supplement


