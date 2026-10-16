-- Prove2me | Definitions.Def_LPCommunity_SBMLog_RandomGraphs
-- name    : LPCommunity_SBMLog_RandomGraphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:30.314684+00:00
-- url     : https://prove2.me/theorems/4936163c-557f-48ba-a5bd-cf6b2773646c
-- title:
--   §4, p. 14 — logarithmic-degree edge-probability scaling (21)
-- statement:
--   In the logarithmic-degree regime (21), the edge probabilities of the stochastic block model on $n$ vertices are
--   $$
--   p_n=\alpha\frac{\log n}{n},\qquad q_n=\beta\frac{\log n}{n}.
--   $$
--   This definition provides the common function $\operatorname{logRegime}(\alpha,n)=\alpha\log n/n$. The Erdős–Rényi and stochastic block model laws used by the theorems are imported from the already reviewed shared module LPCommunity.SBMRecovery.Setting; this file does not redefine them.
--
--   **Formalization Note** Real.log is the natural logarithm. At $n=0$ Lean's division convention gives zero, and the finitely many small-$n$ values do not affect any limit statement. The imported random-graph laws clamp edge probabilities to $[0,1]$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, pp. 13–14, §4, (21), §4.1

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Setting

namespace LPCommunity.SBMLog

open Finset
open scoped Classical

/-- The logarithmic-degree scaling (21): the edge probability `α log n / n` on `n` nodes
(natural logarithm). -/
noncomputable def logRegime (α : ℝ) (n : ℕ) : ℝ := α * Real.log n / n

end LPCommunity.SBMLog


