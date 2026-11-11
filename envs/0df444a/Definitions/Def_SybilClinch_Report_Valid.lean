-- Prove2me | Definitions.Def_SybilClinch_Report_Valid
-- name    : SybilClinch_Report_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:02.618421+00:00
-- url     : https://prove2.me/theorems/89756067-8fd7-4108-b0dd-ad9994d21723
-- title:
--   Valid report: finite nonnegative value and budget
-- statement:
--   A report $(v,q)$ (or $(u,r)$) is valid if it lies in $\mathbb R^2_{\ge0}$: the value and the budget are finite and nonnegative. Mechanisms are required to behave well on every profile of valid reports, and strategies use valid reports only.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, p.5 (PDF p.7); Definition 2.4, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_SybilClinch_Report

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, printed p.5 (PDF p.7): reports lie in `ℝ²_{≥0}`, i.e. value and budget are finite and
nonnegative. -/
def Report.Valid (r : Report) : Prop := 0 ≤ r.val ∧ 0 ≤ r.bud

end SybilClinch


