-- Prove2me | Definitions.Def_SambaPG_visitTime
-- name    : SambaPG_visitTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:00.921169+00:00
-- url     : https://prove2.me/theorems/44dbd2e8-c469-49e7-958c-e2eb056ea373
-- title:
--   The embedded times $t_s$ and the embedded process $\hat q(s)$
-- statement:
--   For a path $q(t)=q_{a^\star}(t)$, the **embedded time** $t_s$ is the $s$-th time (counting from $0$) at which $q(t)<1/2$, and $t_s=\infty$ if there are at most $s$ such times. The **embedded process** is
--
--   $$
--   \hat q(s):=q(t_s),
--   $$
--
--   the process that follows $q_{a^\star}$ while it is below $1/2$ and skips the excursions $[\sigma^{(k)},\tau^{(k+1)})$. This is the paper's $t_s=s+\sum_{i=0}^{k}(\tau^{(i+1)}-\sigma^{(i)})$ for $s$ in the $k$-th block.
--
--   **Formalization Note** $t_s$ is written with the $s$-th element of the set $\{t:q(t)<1/2\}$ instead of the sum formula; the two agree. When $t_s=\infty$, which under condition (2) has probability $0$, $\hat q(s)$ is set to $0$.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, §4.2, pp.9–10

import Mathlib

namespace SambaPG

/-- **The embedded times `t_s` and the embedded process `q̂(s)` of §4.2.**
Denisov & Walton, arXiv:2007.10229v3, §4.2, p.9: "`q̂(s) := q_{a⋆}(t_s)` where
`t_s = s + Σ_{i=0}^{k} (τ^{(i+1)} − σ^{(i)})` for `s ∈ [Σ_{i=0}^{k}(σ^{(i)} − τ^{(i)}) : Σ_{i=0}^{k+1}(σ^{(i)} − τ^{(i)}))`",
with `τ^{(k)}, σ^{(k)}` of (11).

The times in `[τ^{(k)}, σ^{(k)})` are exactly the times at which `q_{a⋆}(t) < 1/2`, so `t_s` is the
`s`-th time (counting from `0`) at which `q_{a⋆}(t) < 1/2`. `visitTime q s` is that time, and `∞`
if there are at most `s` such times.

**Formalization Note.** `t_s` is written with `Nat.nth` on the set `{t : q t < 1/2}` instead of the
sum formula of p.9; the two agree. The value lies in `WithTop ℕ`, so that `t_s` is a stopping time
in Mathlib's sense. -/
noncomputable def visitTime (q : ℕ → ℝ) (s : ℕ) : WithTop ℕ :=
  if (s : ℕ∞) < {t : ℕ | q t < 1 / 2}.encard then (Nat.nth (fun t => q t < 1 / 2) s : WithTop ℕ)
  else ⊤

/-- The embedded process `q̂(s) = q_{a⋆}(t_s)` of §4.2, p.9. When `t_s = ∞` (which, under condition
(2), happens with probability `0`) the value is set to `0`. -/
noncomputable def embedded (q : ℕ → ℝ) (s : ℕ) : ℝ :=
  match visitTime q s with
  | (t : ℕ) => q t
  | ⊤ => 0

end SambaPG


