-- Prove2me | Definitions.Def_GrothendieckLB_beta
-- name    : GrothendieckLB_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:42.908948+00:00
-- url     : https://prove2.me/theorems/c4f64f44-6034-4a8f-9d0d-db19979d8401
-- title:
--   Weighted support budget $\beta(u)$
-- statement:
--   For a one-dimensional function $u$, the weighted support budget is $\beta(u):=\mathbb E[|Z|\,u(Z)^2]$ with $Z\sim N(0,1)$. For ternary $u$ this is the $|Z|$-weighted Gaussian size of the support of $u$.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.4, p.36

import Mathlib
import Definitions.Def_GrothendieckLB_stdExp

namespace GrothendieckLB

/-- The weighted support budget `β(u) := E[|Z| u(Z)²]` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.4, p.36). -/
noncomputable def beta (u : ℝ → ℝ) : ℝ :=
  stdExp fun z => |z| * u z ^ 2

end GrothendieckLB


