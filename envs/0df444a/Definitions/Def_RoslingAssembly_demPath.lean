-- Prove2me | Definitions.Def_RoslingAssembly_demPath
-- name    : RoslingAssembly_demPath
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:35:44.570084+00:00
-- url     : https://prove2.me/theorems/068421f3-91ad-4922-9db0-4e23333fc9c6
-- title:
--   Demand of period $t$, $\xi_t$
-- statement:
--   $\xi_t\ge0$ is the demand for the end item in period $t$. For $t\ge1$ it is the $t$-th coordinate of the random demand path; for $t\le0$ it is part of the given pre-horizon history.
--
--   **Formalization Note** Periods are integers with the paper's numbering; coordinate $j$ of the demand path is $\xi_{j+1}$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 566

import Mathlib

namespace RoslingAssembly

/-- **Demand of period t**, ξ_t (§1, p. 566). Rosling, *Optimal Inventory Policies for Assembly
Systems under Random Demands*, Operations Research 37(4), 1989, p. 566 (unnumbered):
"ξ_t = demands in period t for the end item; demands of different periods are identically and
independently distributed, ξ_t ≥ 0;".

`demPath ξh ω t` is ξ_t for every period `t : ℤ`: the given pre-horizon demand `ξh t` for
`t ≤ 0`, and `ω (t − 1)` for `t ≥ 1`, where `ω : ℕ → ℝ` is the random demand path.

**Formalization Note.** Periods are integers with the paper's numbering; `ω j` is the demand of
paper period `j + 1`. The demands of periods `t ≤ 0` are part of the fixed pre-horizon history. -/
def demPath (ξh : ℤ → ℝ) (ω : ℕ → ℝ) (t : ℤ) : ℝ :=
  if t ≤ 0 then ξh t else ω (t - 1).toNat

end RoslingAssembly


