-- Prove2me | Definitions.Def_NAMatchEst_largeTrial
-- name    : NAMatchEst_largeTrial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:56:11.074692+00:00
-- url     : https://prove2.me/theorems/dee1a2dd-14d2-4ed3-bfec-9c566cd2a307
-- title:
--   One large-scale trial (untruncated)
-- statement:
--   One **large-scale trial** (§3.7), before truncation: run the pilot, the first-layer degree test, the residual-total test and the certified-edge test with independent randomness and all queries fixed in advance; construct $H$ from the pilot; output Yes exactly when at least one of the tests (12), (13), (19) accepts with this $H$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.7, p.28 (PDF 32)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_par
import Definitions.Def_NAMatchEst_cc
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_EdgeStats
import Definitions.Def_NAMatchEst_degTest
import Definitions.Def_NAMatchEst_resTest
import Definitions.Def_NAMatchEst_edgeTest
import Definitions.Def_NAMatchEst_pilot

namespace NAMatchEst

/-- One **large-scale trial** (§3.7), before truncation: run the pilot, the first-layer degree
test, the residual-total test and the certified-edge test with independent randomness, construct
`H` from the pilot, and output Yes (`true`) iff at least one of the three tests (12), (13), (19)
accepts with this `H`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.7, p.28 (PDF 32): "For k > α², generate the pilot sample, the first-layer degree sample,
the residual-total sample, and SL, SR, together with all right-sample indices. All these random
choices are independent and are made before receiving any answers. Once the answers are available,
construct H from the pilot and evaluate the three tests in Eq (12), Eq (13), Eq (19). The trial
outputs Yes if at least one test accepts, and outputs No otherwise."

**Formalization Note** The certified-edge test accepts when `Z_E ⩾ cL/4` (19). -/
noncomputable def largeTrial (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) : RandAlg n Bool :=
  open Classical in
  (pilot n α k).par ((degTest n α k).par ((resTest n α k).par (edgeTest n α k) Prod.mk) Prod.mk)
    fun H t => t.1 || t.2.1 H || decide (cc * L n / 4 ≤ ((t.2.2 H).ZE : ℝ))

end NAMatchEst


