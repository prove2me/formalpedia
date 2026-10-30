-- Prove2me | Definitions.Def_TwoAgentSched_IsDeadline
-- name    : TwoAgentSched_IsDeadline
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:45:53.534792+00:00
-- url     : https://prove2.me/theorems/5f2d1170-3430-4d03-bef8-5ff15f4a14f7
-- title:
--   Deadlines $D^B_k$ as cuts of the time axis
-- statement:
--   For a B-job with cost function $f$ and bound $Q$, the paper defines a **deadline** $D$ such that
--   $$
--   f(C) \le Q \ \text{ for } C \le D, \qquad f(C) > Q \ \text{ for } C > D .
--   $$
--   Such a real $D$ need not exist when the set of acceptable times is right-open, e.g. $f=0$ on $[0,1)$, $f=1$ on $[1,\infty)$ and $Q=0$. The definition therefore uses a **cut**: an element $D$ of the lexicographically ordered set $(\mathbb R\times\{\mathrm{false}<\mathrm{true}\})\cup\{+\infty\}$. A cut $D$ **represents** $f$ and $Q$ if
--   $$
--   f(t)\le Q \iff (t,\mathrm{true}) \le D \qquad \text{for every } t \ge 0 .
--   $$
--   The cut $(d,\mathrm{true})$ is the paper's deadline $d$; $(d,\mathrm{false})$ means $f(t)\le Q$ exactly for $t<d$; $+\infty$ means $f(t)\le Q$ for all $t\ge0$; and $(-1,\mathrm{true})$ means never.
--
--   The algorithm of §4 receives the deadlines as input and reads agent $B$ only through them.
--
--   **Formalization Note** The cut type is `WithTop (ℝ ×ₗ Bool)`; `IsDeadline f Q D` is the displayed equivalence for all `t ≥ 0`.
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), p. 233 ("For each B-job J^B_k, let us define a deadline D^B_k, such that f^B_k(C^B_k) ⩽ Q for C^B_k ⩽ D^B_k and f^B_k(C^B_k) > Q for C^B_k > D^B_k")

import Mathlib

namespace TwoAgentSched

/-- **Deadline as a cut** (Agnetis–Mirchandani–Pacciarelli–Pacifici, Oper. Res. 52(2) (2004),
p. 233: "a deadline `D^B_k` such that `f^B_k(C^B_k) ⩽ Q` for `C^B_k ⩽ D^B_k` and
`f^B_k(C^B_k) > Q` for `C^B_k > D^B_k`").

`D : WithTop (ℝ ×ₗ Bool)` represents `f` and `Q` if for every time `t ≥ 0`,
`f t ≤ Q ↔ (t, true) ≤ D` in the lexicographic order (`false < true`). Thus
`D = toLex (d, true)` is the paper's deadline `d` (`f t ≤ Q ↔ t ≤ d`), `D = toLex (d, false)`
means `f t ≤ Q ↔ t < d`, and `D = ⊤` means `f t ≤ Q` for every `t ≥ 0`. -/
def IsDeadline (f : ℝ → ℝ) (Q : ℝ) (D : WithTop (ℝ ×ₗ Bool)) : Prop :=
  ∀ t : ℝ, 0 ≤ t → (f t ≤ Q ↔ ((toLex (t, true) : ℝ ×ₗ Bool) : WithTop (ℝ ×ₗ Bool)) ≤ D)

end TwoAgentSched


