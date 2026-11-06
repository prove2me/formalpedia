-- Prove2me | Definitions.Def_MemQueryFeas_eVec
-- name    : MemQueryFeas_eVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:55.32274+00:00
-- url     : https://prove2.me/theorems/e9a64d97-467c-491c-81cc-582741fd1617
-- title:
--   The vector $e=(1,0,\dots,0)$
-- statement:
--   $e=(1,0,\dots,0)\in\mathbb R^d$ is the first standard basis vector. The constraint $e^\top x\le-1/2$ of the hard feasible region excludes small-norm queries.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §2, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_MemQueryFeas_Vec

namespace MemQueryFeas

/-- **The first basis vector `e = (1, 0, …, 0)`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §2, p.3 (PDF p.4): "Let
`e := (1, 0, ..., 0) ∈ ℝ^d`."

**Formalization Note.** The coordinate with index `0` is `1`, all others `0`; for `d = 0` this is the
zero vector of `ℝ^0`. -/
noncomputable def eVec (d : ℕ) : Vec d :=
  WithLp.toLp 2 (fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else 0)

end MemQueryFeas


