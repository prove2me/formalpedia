-- Prove2me | Definitions.Def_ChoicePAC_MidPoint_GF
-- name    : ChoicePAC_MidPoint_GF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:43.767451+00:00
-- url     : https://prove2.me/theorems/469dc892-0739-46e2-8961-d6b21eae4ab8
-- title:
--   Theorem 5.3's $G(k,t)$ and $F(k,t)$ for a re-solving schedule
-- statement:
--   Let $0 = t_0 < t_1 < \dots < t_M < t_{M+1} = 1$ be the re-solving times $\Gamma^k$ of the $k$-th system. For $t \in [0,1]$ let $i$ be the index with $t_{i-1} \le t < t_i$, $1 \le i \le M+1$ (and $i = M+1$ at $t = 1$). Theorem 5.3 (p. 327) uses
--   $$G(k,t) = (t - t_{i-1}) + \sum_{j=1}^{i-1}(t_j - t_{j-1})\frac{(1-t)^2}{(1-t_j)^2},$$
--   $$F(k,t) = \exp\big(k v(k,t)^2 G(k,t) - k v(k,t)(1-t)\big),$$
--   for a function $v(k,t) > 0$.
--
--   $G$ measures the accumulated variance of the re-solving error at time $t$, and $F$ is the resulting exponential tail bound in the general loss bound (8).
--
--   **Formalization Note** The index $i$ is $1 + \#\{l \le M : t_l \le t\}$. The page defines $G$ for $t_{i-1} \le t < t_i$, $0 \le t \le 1$, which leaves $t = 1$ without an $i$; Lean takes $i = M+1$ there, a single point that does not affect the integral in (8). $F$ takes the value $v = v(k,t)$ as an argument.
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, Theorem 5.3, p. 327

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model

namespace ChoicePAC.MidPoint

namespace Schedule

/-- The index `i` with `t_{i−1} ≤ t < t_i` (`1 ≤ i ≤ M + 1`), namely `1 + #{l ≤ M : t_l ≤ t}`;
for `t = 1` it is `M + 1`. -/
noncomputable def idx (s : Schedule) (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun l : Fin s.M => s.t l ≤ t)).card + 1

/-- `G(k, t)` of Theorem 5.3 (p. 327), for the schedule `s = Γ^k`:
`G = (t − t_{i−1}) + Σ_{j=1}^{i−1} (t_j − t_{j−1}) (1 − t)² / (1 − t_j)²`, where
`t_{i−1} ≤ t < t_i` (and `i = M + 1` at `t = 1`). -/
noncomputable def G (s : Schedule) (t : ℝ) : ℝ :=
  (t - s.time (s.idx t - 1)) +
    ∑ j ∈ Finset.Icc 1 (s.idx t - 1),
      (s.time j - s.time (j - 1)) * (1 - t) ^ 2 / (1 - s.time j) ^ 2

/-- `F(k, t) = exp(k v² G(k, t) − k v (1 − t))` of Theorem 5.3 (p. 327), with `v = v(k, t)`. -/
noncomputable def F (s : Schedule) (k : ℕ) (v : ℝ) (t : ℝ) : ℝ :=
  Real.exp ((k : ℝ) * v ^ 2 * s.G t - (k : ℝ) * v * (1 - t))

end Schedule

end ChoicePAC.MidPoint


