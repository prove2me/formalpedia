-- Prove2me | Definitions.Def_StochIneqPO_Comparison_IsUpward
-- name    : StochIneqPO_Comparison_IsUpward
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:58:19.015936+00:00
-- url     : https://prove2.me/theorems/e166b3bd-b5ec-40c4-b36a-e379ee5989d7
-- title:
--   p. 900 — upward stochastic kernels on $E \times E$
-- statement:
--   Let $E$ be a measurable space with a preorder $\le$, and let $k$ be a stochastic kernel from $E$ to $E$, i.e. $x \mapsto k(x,\cdot)$ is a measurable family of measures on $E$. The kernel $k$ is **upward** if for every $x \in E$ the measure $k(x,\cdot)$ has support in $\{y \in E : y \ge x\}$:
--   $$k\big(x,\ \{y \in E : x \le y\}^{\mathrm c}\big) = 0 \qquad \text{for all } x \in E.$$
--
--   Upward kernels appear in condition (v) of Theorem 1: $P_1 \prec P_2$ iff $P_2$ is obtained from $P_1$ by moving mass upward through such a kernel.
--
--   **Formalization Note** "Support in $\{y \ge x\}$" is encoded as the complement having measure zero. For a closed partial order the set $\{y : y \ge x\}$ is closed, so this agrees with the topological support. Being a Markov (probability) kernel is a separate hypothesis where the kernel is used.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Sec. 1, p. 900 (PDF p. 2)

import Mathlib

namespace StochIneqPO.Comparison

open MeasureTheory ProbabilityTheory

/-- An "upward" stochastic kernel on `E × E` (Kamae–Krengel–O'Brien 1977, p. 900): for every `x`,
the measure `k x` has support in `{y ∈ E : y ≥ x}`, i.e. gives zero mass to the complement of
that (closed) set. -/
def IsUpward {E : Type*} [MeasurableSpace E] [Preorder E] (k : Kernel E E) : Prop :=
  ∀ x : E, k x {y | x ≤ y}ᶜ = 0

end StochIneqPO.Comparison


