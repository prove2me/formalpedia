-- Prove2me | Definitions.Def_StochIneqPO_Monotone_Regular17
-- name    : StochIneqPO_Monotone_Regular17
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:10:11.693783+00:00
-- url     : https://prove2.me/theorems/0511a20b-0e04-4a9d-9dc6-91d4f6306c43
-- title:
--   Theorem 6, condition (17), p. 908 — sandwiched sequences share the limit
-- statement:
--   Let $E$ be a topological space carrying a partial order $\le$. We say that $E$ satisfies **condition (17)** if for all sequences $(x_n)_{n\ge 1}$ and $(y_n)_{n\ge 1}$ of elements of $E$ with
--
--   $$
--   x_n \le y_n \le x_{n+1}\qquad (n\ge 1),
--   $$
--
--   convergence $x_n\to z\in E$ implies $y_n\to z$.
--
--   Condition (17) is the regularity property of the ordered space under which, in Kamae, Krengel and O'Brien's Theorem 6, almost sure convergence of every nondecreasing sequence of random elements of $E$ becomes equivalent to its convergence in probability. It holds, for instance, in $\mathbb R^d$ with the coordinatewise order, and it can fail in a Polish space with a closed partial order (Remarks, p. 909).
--
--   **Formalization Note** Sequences are indexed by $\mathbb N=\{0,1,\dots\}$ instead of $\{1,2,\dots\}$; the condition is required for every index. Only the topology of $E$ and the order enter.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Theorem 6, display (17), p. 908 (PDF p. 10)

import Mathlib

namespace StochIneqPO.Monotone

open Filter Topology

/-- **Condition (17)** (Kamae–Krengel–O'Brien 1977, Theorem 6, p. 908). A topological space `E`
with a partial order satisfies (17) if for all sequences `(xₙ)`, `(yₙ)` in `E` with
`xₙ ≤ yₙ ≤ xₙ₊₁` for every `n`, convergence `xₙ → z` implies `yₙ → z`.
The paper indexes from `n = 1`; here sequences are indexed by `ℕ` from `0`. -/
def Regular17 (E : Type*) [TopologicalSpace E] [PartialOrder E] : Prop :=
  ∀ (x y : ℕ → E) (z : E), (∀ n, x n ≤ y n ∧ y n ≤ x (n + 1)) →
    Tendsto x atTop (𝓝 z) → Tendsto y atTop (𝓝 z)

end StochIneqPO.Monotone


