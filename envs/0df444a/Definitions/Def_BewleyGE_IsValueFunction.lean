-- Prove2me | Definitions.Def_BewleyGE_IsValueFunction
-- name    : BewleyGE_IsValueFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:35.491997+00:00
-- url     : https://prove2.me/theorems/db99d028-1591-46ca-8c25-5f6be5571a3b
-- title:
--   Value function $V$ — the bounded fixed point $TV=V$
-- statement:
--   At prices $(p,r)$ with demand function $x$, a function $V$ is the **value function** if it is bounded on $A(p,r)$ and, for every $a\in A(p,r)$,
--   $$
--   V(a)=\max_{b\in C(a,p)}\Big[U\big(x(a-b)\big)+\beta\sum_{y\in\mathcal Y}e(y)V\big((1+r)b+p\cdot y\big)\Big],
--   $$
--   with the maximum attained. This is $TV=V$ for the Bellman operator $T$ on bounded functions on $A(p,r)$, whose unique fixed point the paper identifies with the value function.
--
--   **Formalization Note** The paper first defines $V$ as a supremum over strategies and then states that it is the unique bounded fixed point of $T$; the fixed-point characterization is used here.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2.1, p.7 and footnote 10

import Mathlib
import Definitions.Def_BewleyGE_bellmanObjective
import Definitions.Def_BewleyGE_savingsSet
import Definitions.Def_BewleyGE_wealthSet

namespace BewleyGE

/-- **Value function** at prices `(p, r)`: `V ∈ B(A(p, r))` with `TV = V`.
Light, arXiv:1906.06810v2, §2.1, p.7: "The value function V is the unique fixed point of T, i.e.,
there is a unique function V ∈ B(A(p, r)) such that TV = V", where
`Tf(a) = max_{b ∈ C(a,p)} max_{x ∈ X(a−b,p)} U(x) + β ∑_{y} e(y) f((1 + r) b + p · y)`.

`V` is bounded on `A(p, r)`, and for every `a ∈ A(p, r)` the value `V a` is the greatest value
of the Bellman objective over `b ∈ C(a, p)` (the maximum is attained).

**Formalization Note.** The page defines `V` on p.6 as a supremum over strategies and states on
p.7 that it is the unique bounded fixed point of `T`; the bounded fixed point is used here
(reading R4). The maximum is stated with `IsGreatest`, never a real `sSup`. Values of `V` off
`A(p, r)` are irrelevant. -/
def IsValueFunction {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ)
    (x : ℝ → Fin n → ℝ) (V : ℝ → ℝ) : Prop :=
  (∃ M : ℝ, ∀ a ∈ wealthSet E p r, |V a| ≤ M) ∧
  ∀ a ∈ wealthSet E p r,
    IsGreatest (bellmanObjective E p r x V a '' savingsSet E p r a) (V a)

end BewleyGE


