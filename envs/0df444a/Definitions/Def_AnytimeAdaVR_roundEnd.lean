-- Prove2me | Definitions.Def_AnytimeAdaVR_roundEnd
-- name    : AnytimeAdaVR_roundEnd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:26:59.922896+00:00
-- url     : https://prove2.me/theorems/92b24c31-3dc3-4d95-b29b-3a88cab4877d
-- title:
--   Global query count at the end of round $r$
-- statement:
--   Round $r$ of Algorithm 4 makes one optimization query on each path, and, if a checkpoint $n=2^k$ is active ($n<r\le 2n$), one validation query at each frozen point. The **global query count** at the end of round $r$ is obtained by adding $3$ or $6$ per round. The paper's closed form $D^{\mathrm{lin}}_r=6r-3$ for $r\ge1$ (eq. (57)) is a consequence.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), Algorithm 4, p.9; §5.3, p.9; eq. (57), p.27

import Mathlib

namespace AnytimeAdaVR

/-- **The global query count at the end of round `r`.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), Algorithm 4, lines 2–6, p.9, and
§5.3, p.9: "One global round executes one individual query on each path. … During rounds n + 1, …, 2n,
query each frozen point once per round", for the checkpoints `n = 1, 2, 4, …`.

`roundEnd r` counts the schedule: round `r` makes three optimization queries, plus three validation
queries when some checkpoint `n = 2^k` is active, i.e. `n < r ≤ 2n`. (The closed form `6r − 3`,
eq. (57), p.27, is a consequence, not the definition.) -/
def roundEnd : ℕ → ℕ
  | 0 => 0
  | r + 1 => roundEnd r + 3 +
      (if ∃ k < r + 1, 2 ^ k < r + 1 ∧ r + 1 ≤ 2 ^ (k + 1) then 3 else 0)

end AnytimeAdaVR


