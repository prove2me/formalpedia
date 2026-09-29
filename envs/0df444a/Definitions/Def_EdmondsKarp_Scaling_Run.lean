-- Prove2me | Definitions.Def_EdmondsKarp_Scaling_Run
-- name    : EdmondsKarp_Scaling_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:23:27.418742+00:00
-- url     : https://prove2.me/theorems/ceaa0161-c385-469e-bc65-5909ef536fad
-- title:
--   Problem $p$ and runs of the scaling method for the Hitchcock problem
-- statement:
--   Let $a_1,\dots,a_m$ and $b_1,\dots,b_n$ be natural numbers and $d_{ij}$ real costs. For a nonnegative integer $p$, **Problem $p$** is the problem on the network of Figure 1 with the same costs and capacities
--   $$\left\lfloor a_i / 2^p \right\rfloor \text{ on } (s, s_i), \qquad \left\lfloor b_j / 2^p \right\rfloor \text{ on } (t_j, t).$$
--   Problem $0$ is the original problem.
--
--   Fix $l$. A **run of the scaling method** with $l$ phases consists of numbers $K_p$ and flows $f^{p,0}, f^{p,1}, \dots, f^{p,K_p}$ of Problem $p$ for each $p < l$ such that
--
--   1. the initial flow of Problem $l-1$ is $f^{l-1,0} = 0$;
--   2. for $1 \le p < l$, the initial flow of Problem $p-1$ is $f^{p-1,0} = 2 f^{p,K_p}$;
--   3. each $f^{p,k+1}$ is obtained from $f^{p,k}$ by one flow augmentation in Problem $p$;
--   4. every $f^{p,k}$ is pseudo-extreme in Problem $p$;
--   5. no augmenting path exists relative to $f^{p,K_p}$ in Problem $p$.
--
--   The number of flow augmentations of the run is $\sum_{p<l} K_p$. This is the object Theorem 9 counts.
--
--   **Formalization Note** `problem a b d p` uses natural-number division, which is the floor $\lfloor a_i/2^p\rfloor$. The run is a predicate `IsScalingRun a b d l K F` on `K : ℕ → ℕ` and `F : ℕ → ℕ → Flow m n`; only the values with $p < l$ and $k \le K_p$ matter. The paper's method chooses each augmenting path as a minimum-weight path for the modified reduced costs $\bar\Delta$; this definition abstracts that rule to the invariant the paper states for it (condition 4, every flow pseudo-extreme), so every run of the paper's method is a run in this sense.
-- source:
--   Edmonds, Karp, Theoretical Improvements in Algorithmic Efficiency for Network Flow Problems, J. ACM 19(2), 1972, p. 259 (Problem p, footnote 3, the invariant (5a)–(5b)); p. 260 (the scaling method; proof of Theorem 9, initial flows)

import Mathlib
import Definitions.Def_EdmondsKarp_Scaling_Transport
import Definitions.Def_EdmondsKarp_Scaling_Augmentation

namespace EdmondsKarp.Scaling

variable {m n : ℕ}

/-- Problem `p` of the scaling method (§2.2, p. 259): the same nodes, arcs and costs `d` as the
given transportation problem with integral capacities `a`, `b`, but with capacity `[a_i / 2^p]` on
`(s, s_i)` and `[b_j / 2^p]` on `(t_j, t)` (`[x]` = greatest integer `≤ x`, footnote 3; for natural
numbers this is `ℕ` division). Problem `0` is the original problem. -/
def problem (a : Fin m → ℕ) (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (p : ℕ) : Transport m n where
  a i := ((a i / 2 ^ p : ℕ) : ℝ)
  b j := ((b j / 2 ^ p : ℕ) : ℝ)
  d := d

/-- A run of the scaling method (§2.2, pp. 259–260) with `l` phases, for Problems `l-1, l-2, …, 0`.
Phase `p < l` is the sequence of flows `F p 0, …, F p (K p)` of Problem `p`, with `K p` flow
augmentations:
* the initial flow in Problem `l - 1` is `0`;
* for `1 ≤ p < l`, the initial flow in Problem `p - 1` is `2 • F p (K p)`;
* each `F p (k+1)` is obtained from `F p k` by one augmentation in Problem `p`;
* every flow of phase `p` is pseudo-extreme in Problem `p` (the invariant the paper states for the
  method's choice of augmenting paths);
* the phase ends at a flow admitting no augmenting path in Problem `p`. -/
structure IsScalingRun (a : Fin m → ℕ) (b : Fin n → ℕ) (d : Fin m → Fin n → ℝ) (l : ℕ)
    (K : ℕ → ℕ) (F : ℕ → ℕ → Flow m n) : Prop where
  start : F (l - 1) 0 = 0
  restart : ∀ p, 1 ≤ p → p < l → F (p - 1) 0 = (2 : ℝ) • F p (K p)
  step : ∀ p, p < l → ∀ k, k < K p → AugStep (problem a b d p) (F p k) (F p (k + 1))
  pseudo : ∀ p, p < l → ∀ k, k ≤ K p → IsPseudoExtreme (problem a b d p) (F p k)
  stop : ∀ p, p < l → ¬ ∃ L, IsAugPath (problem a b d p) (F p (K p)) L

end EdmondsKarp.Scaling


