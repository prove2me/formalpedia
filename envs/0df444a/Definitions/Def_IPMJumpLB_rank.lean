-- Prove2me | Definitions.Def_IPMJumpLB_rank
-- name    : IPMJumpLB_rank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:59.444183+00:00
-- url     : https://prove2.me/theorems/9bd6932e-7591-4774-98b8-54e40929b5c9
-- title:
--   Rank $r(f)$ of a flow on the unit-demand instance
-- statement:
--   For a flow $f$ on the Section 4 instance, the **rank** is
--   $$
--   r(f) = \bigl|\{\, i \in \{0, \dots, k-1\} : 2k^2 - ki \le F_{S,\mathrm{out}}(f) \,\}\bigr| .
--   $$
--   By the cut identity it counts the gadgets with nonpositive net forward flow. The rank is $k$ at the first iterate and $0$ at the last, and it drops by at most $2\lceil 12bk^2/\eta\rceil$ per jump, which gives the lower bound of Theorem 4.1.
-- source:
--   Adil–Dadush–Kyng–Vladu, An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths, STOC 2027 submission (manuscript sha256 87ad352e…), proof of Theorem 4.1, p.13

import Mathlib
import Definitions.Def_IPMJumpLB_ArcU
import Definitions.Def_IPMJumpLB_shortcutOutFlow

namespace IPMJumpLB

/-- The rank of a flow on the Section 4 instance (Adil–Dadush–Kyng–Vladu, *An Ω(√N) Lower Bound for Path Following Interior Point Methods on Single-Source Shortest Paths*, STOC 2027 submission manuscript (sha256 87ad352e…d6e70), proof of Theorem 4.1, p.13):
`r(f) = |{i ∈ {0, …, k − 1} : 2k² − ki ≤ F_S,out(f)}|`. -/
noncomputable def rank (b k : ℕ) (f : ArcU b k → ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin k =>
    2 * (k : ℝ) ^ 2 - (k : ℝ) * (i : ℕ) ≤ shortcutOutFlow b k f)).card

end IPMJumpLB


