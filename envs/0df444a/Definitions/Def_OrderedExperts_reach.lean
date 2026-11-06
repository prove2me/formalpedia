-- Prove2me | Definitions.Def_OrderedExperts_reach
-- name    : OrderedExperts_reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:38.457593+00:00
-- url     : https://prove2.me/theorems/23431514-bb0e-4fdd-99ac-8bc27fc283d4
-- title:
--   Reach probability of the random increasing path
-- statement:
--   Fix a target rank $j$ and a vector $\pi$ on ranks. A particle starts at the anchor (rank $0$) and, from a node $a<j$, jumps to $b\in\{a+1,\dots,j\}$ with probability
--   $$
--   P(b\mid a,j)=\frac{\pi(b)}{\Pi(a,j]}.
--   $$
--   The **reach probability** $r_j(b)$ is the probability that this path visits rank $b$: $r_j(0)=1$, and for $1\le b\le j$
--   $$
--   r_j(b)=\sum_{a=0}^{b-1} r_j(a)\,\frac{\pi(b)}{\Pi(a,j]} ,
--   $$
--   since the path is strictly increasing and the events "the path jumps from $a$ to $b$" are disjoint for different $a$. Ranks above $j$ are never reached ($r_j(b)=0$).
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 3.3, p.8; Appendix A.3, p.18

import Definitions.Def_OrderedExperts_massOC

namespace OrderedExperts

/-- **Reach probability of the random increasing path.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 3.3, p.8:
"For a target rank `j`, the particle of the overview starts at the anchor `0`, and from a node `a < j`
it jumps to `b ∈ {a + 1, . . . , j}` with probability proportional to `π(b)`:
`P(b | a, j) = π(b)/Π(a, j]`." (also Appendix A.3, p.18).

`reach π j b` is the probability that the path towards the target `j` visits rank `b`: it is `1` at
the anchor `b = 0`, and for `1 ≤ b ≤ j` it is `Σ_{a<b} reach π j a · π(b)/Π(a, j]` (the path is
strictly increasing, so the events "the path jumps from `a` to `b`" for different `a` are
disjoint). Ranks above `j` are never reached (`0`).

**Formalization Note.** Defined by well-founded recursion on `b`; the predecessor `a` ranges over
`Fin (b+1)`, i.e. `a ∈ {0, …, b}` for the node `b+1`. -/
noncomputable def reach (π : ℕ → ℝ) (j : ℕ) : ℕ → ℝ
  | 0 => 1
  | b + 1 =>
      if b + 1 ≤ j then
        ∑ a : Fin (b + 1), reach π j a * (π (b + 1) / massOC π a j)
      else 0
termination_by b => b
decreasing_by exact a.isLt

end OrderedExperts


