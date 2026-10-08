-- Prove2me | Definitions.Def_KalaiVempala_Additive_Setting
-- name    : KalaiVempala_Additive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:31.741183+00:00
-- url     : https://prove2.me/theorems/16cc29d8-65df-4d53-bd98-781294dff511
-- title:
--   §1.1, p. 293 — the argmin oracle M(s) = argmin_{d∈𝒟} d·s
-- statement:
--   **The offline optimisation oracle.** In the linear online decision problem of Kalai and Vempala, a decision maker repeatedly picks a decision $d_t$ from a possibly infinite set $\mathcal D \subset \mathbb R^n$, then observes a state $s_t \in \mathcal S \subset \mathbb R^n$ and pays the cost $d_t \cdot s_t$. The only access to $\mathcal D$ is an offline oracle that returns a best single decision for a given total state vector:
--
--   $$M : \mathbb R^n \to \mathcal D, \qquad M(s) = \operatorname*{arg\,min}_{d \in \mathcal D} d \cdot s .$$
--
--   A function $M : \mathbb R^n \to \mathbb R^n$ is called an **argmin oracle for $\mathcal D$** when, for every $x \in \mathbb R^n$,
--
--   1. $M(x) \in \mathcal D$, and
--   2. $M(x) \cdot x \le d \cdot x$ for every $d \in \mathcal D$.
--
--   Ties may be broken in any way. Because costs are additive, the best fixed decision in hindsight after $T$ periods is $M(s_1 + \dots + s_T)$, and the benchmark $\text{min-cost}_T = \min_{d \in \mathcal D} \sum_{t=1}^T d \cdot s_t$ equals $M(s_{1:T}) \cdot s_{1:T}$.
--
--   This oracle is the one object shared by all three missions on the paper (FPL, FPL\* and the lazy variants FLL, FLL\*). Every theorem of those missions is stated for an arbitrary argmin oracle, so no result depends on a particular tie-breaking rule.
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ` and $d \cdot s$ is `dotProduct`. The oracle is a predicate on a function, not a chosen minimiser (no `Classical.epsilon`). An argmin oracle exists only when $\mathcal D$ is nonempty and every linear function $d \mapsto d\cdot x$ attains its minimum on $\mathcal D$, which the paper presupposes when it writes $M(s) = \arg\min$. The module imports the published definition `OracleRO.ApproxFPL.FPL` (prefix sums $s_{1:t}$, the uniform perturbation law, the expected cost of FPL), so the missions that build on this item see both.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 293, §1.1 (definition of M and min-cost_T)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL

namespace KalaiVempala.Additive

/-- The offline oracle of Kalai–Vempala (2005, p. 293): `M : ℝⁿ → 𝒟` with
`M(s) = argmin_{d ∈ 𝒟} d · s`. A function `M` is such an oracle for the decision set `Dset`
when, for every total state vector `x`, `M x` lies in `Dset` and minimises `d ⬝ᵥ x` over
`Dset`. Ties may be broken arbitrarily; theorems quantify over every such `M`. -/
def IsArgminOracle {n : ℕ} (Dset : Set (Fin n → ℝ)) (M : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ x, M x ∈ Dset ∧ ∀ d ∈ Dset, M x ⬝ᵥ x ≤ d ⬝ᵥ x

end KalaiVempala.Additive


