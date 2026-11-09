-- Prove2me | Definitions.Def_NAMatchEst_smallTrial
-- name    : NAMatchEst_smallTrial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:54:39.076855+00:00
-- url     : https://prove2.me/theorems/3e1be64c-d511-426c-b237-b2ece49bf1dc
-- title:
--   One small-scale trial (untruncated)
-- statement:
--   One **small-scale trial** (§3.8), before truncation: run the first-layer degree test and the small-scale edge test with independent randomness and output Yes exactly when at least one of them accepts.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.8, p.29 (PDF 33)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_par
import Definitions.Def_NAMatchEst_degTest
import Definitions.Def_NAMatchEst_smallEdgeTest

namespace NAMatchEst

/-- One **small-scale trial** (§3.8), before truncation: run the first-layer degree test and the
small-scale edge test with independent randomness, and output Yes (`true`) iff at least one of them
accepts.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.8, p.29 (PDF 33): "The trial outputs Yes if this test or the first-layer degree test
accepts, and No otherwise." -/
noncomputable def smallTrial (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) : RandAlg n Bool :=
  (degTest n α k).par (smallEdgeTest n α k) fun a b => a || b

end NAMatchEst


