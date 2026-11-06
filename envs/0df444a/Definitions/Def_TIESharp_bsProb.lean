-- Prove2me | Definitions.Def_TIESharp_bsProb
-- name    : TIESharp_bsProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:00.660192+00:00
-- url     : https://prove2.me/theorems/18230410-441e-4673-b7ea-4473a35f1ecf
-- title:
--   Bounded-Square assignment probability $q_{ij}(t)$
-- statement:
--   The Bounded-Square assignment probability of job $j$ on machine $i$ at profile $t$ is the Bounded-Square rule applied to the column $t_{\cdot j}$:
--   $$q_{ij}(t)=q_i(t_{\cdot j}).$$
--   It depends on the profile only through job $j$'s own column (column-locality).
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §3.2, p.10

import Mathlib
import Definitions.Def_TIESharp_bsCol

set_option autoImplicit false

namespace TIESharp

/-- The **Bounded-Square assignment probability** `q_ij(t)` of job `j` on machine `i` (Li,
*Sharp Bounds for Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §3.2, p.10): the
Bounded-Square rule `bsCol` applied to column `t_{·j}`. It depends on the profile only through that
column. -/
noncomputable def bsProb {n m : ℕ} (t : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) : ℝ :=
  bsCol (fun k => t k j) i

end TIESharp


