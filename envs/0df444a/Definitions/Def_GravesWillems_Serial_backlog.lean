-- Prove2me | Definitions.Def_GravesWillems_Serial_backlog
-- name    : GravesWillems_Serial_backlog
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:16:06.708176+00:00
-- url     : https://prove2.me/theorems/1c58562f-895f-49ce-8bd2-47d8233e66a0
-- title:
--   Window demand and the backlog $Q_i(t)$ of a serial base-stock system, defined by the recursion (A1)
-- statement:
--   Consider a serial supply chain with $N$ stages, where stage $1$ is the demand node and stage $i$ supplies stage $i-1$ for $i = 2, \dots, N$. Stage $i$ has a deterministic lead time of $T_i$ periods ($T_i \in \mathbb{N}$) and a base stock $B_i \in \mathbb{R}$. Time is discrete, $t \in \mathbb{Z}$, and $d(t)$ is the end-item demand in period $t$.
--
--   **Window demand.** For integers $a, b$ the demand over the interval $(a, b]$ is
--   $$d(a, b] = \sum_{a < \tau \le b} d(\tau) = d(a+1) + \dots + d(b),$$
--   which is $0$ when $a \ge b$.
--
--   **Backlog.** The shortfall or backlog $Q_i(t)$ of stage $i$ at time $t$ (the amount ordered by the stage's customer but not yet delivered) is defined by the downward recursion
--   $$Q_i(t) = \bigl[\, d(t - T_i, t] + Q_{i+1}(t - T_i) - B_i \,\bigr]^+ , \qquad i = N, N-1, \dots, 1,$$
--   where $[x]^+ = \max(0, x)$ and $Q_{N+1}(t) = 0$ for all $t$.
--
--   This is the backlog process of the appendix model of Graves and Willems; it is the basic random quantity whose expectations enter the objective of the base-stock placement program $\mathbf P^*$.
--
--   **Formalization Note** The paper derives (A1) from the stage dynamics ("We can show …"); here (A1) is taken as the definition. Lean computes $Q_i(t)$ through $N + 1 - i$ applications of the recursion, so $Q_i \equiv 0$ for every $i > N$; the value at the index $i = 0$ has no meaning in the paper and no statement of the mission reads it. Lead times are natural numbers cast to $\mathbb{Z}$; base stocks are indexed by $\mathbb{N}$ and only $B_1, \dots, B_N$ are read.
-- source:
--   Graves and Willems, Optimizing Strategic Safety Stock Placement in Supply Chains, Manufacturing & Service Operations Management 2(1), 2000, p. 81, Appendix, Eq. (A1); window demand d(a, b]: p. 80 and §3 p. 72

import Mathlib

namespace GravesWillems.Serial

/-- Window demand `d(a, b] = d(a + 1) + ⋯ + d(b)` of a demand path `d : ℤ → ℝ`
(Graves–Willems 2000, §3 p. 72 and Appendix p. 80). It is `0` when `a ≥ b`, as on p. 72. -/
noncomputable def windowDemand (d : ℤ → ℝ) (a b : ℤ) : ℝ :=
  ∑ τ ∈ Finset.Ioc a b, d τ

/-- Auxiliary recursion for the backlog: `backlogAux N T B d r i t` is the backlog at stage `i`
at time `t` computed through `r` further stages; with `r = 0` it is `0` (this is `Q_{N+1} ≡ 0`). -/
noncomputable def backlogAux (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) : ℕ → ℕ → ℤ → ℝ
  | 0, _, _ => 0
  | r + 1, i, t =>
      max 0 (windowDemand d (t - (T i : ℤ)) t + backlogAux T B d r (i + 1) (t - (T i : ℤ)) - B i)

/-- The backlog `Qᵢ(t)` of stage `i` at time `t` in the `N`-stage serial base-stock system with
lead times `T`, base stocks `B` and end-item demand path `d`, defined by the recursion (A1) of
Graves–Willems 2000 (Appendix, p. 81):
`Qᵢ(t) = [d(t − Tᵢ, t] + Q_{i+1}(t − Tᵢ) − Bᵢ]⁺`, with `Q_{N+1}(t) = 0`.
Stages `i ∈ {1, …, N}` are the paper's; `Qᵢ ≡ 0` for `i > N`. The value at `i = 0` is not used. -/
noncomputable def backlog (N : ℕ) (T : ℕ → ℕ) (B : ℕ → ℝ) (d : ℤ → ℝ) (i : ℕ) (t : ℤ) : ℝ :=
  backlogAux T B d (N + 1 - i) i t

end GravesWillems.Serial


