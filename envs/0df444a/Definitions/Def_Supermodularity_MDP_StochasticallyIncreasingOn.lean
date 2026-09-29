-- Prove2me | Definitions.Def_Supermodularity_MDP_StochasticallyIncreasingOn
-- name    : Supermodularity_MDP_StochasticallyIncreasingOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:25:25.275993+00:00
-- url     : https://prove2.me/theorems/714e3d53-4029-4d06-90f9-a7787dd3d0f3
-- title:
--   Stochastically increasing family of distributions
-- statement:
--   Let $\alpha$ be a preordered set and let $\{F(a,\cdot) : a \in D\}$, $D \subseteq \alpha$, be
--   a family of distribution functions on $\mathbb{R}^n$, represented here by a family of
--   measures $\mu_a$ (one probability measure per $a \in D$). A set $S \subseteq \mathbb{R}^n$ is
--   **increasing** if it is upward closed: $w \in S$ and $w \le w'$ imply $w' \in S$.
--
--   The family $\{F(a,\cdot) : a \in D\}$ is **stochastically increasing** on $D$ if, for every
--   increasing set $S \subseteq \mathbb{R}^n$, the probability $\mu_a(S) = \int_S dF(a,w)$ is a
--   monotone (non-decreasing) function of $a$ on $D$.
--
--   This is Topkis's definition preceding Theorem 3.9.1: raising the parameter $a$ can only move
--   probability mass upward. It is the hypothesis under which the optimal-value function of a
--   Markov decision process inherits monotonicity in the state from monotonicity of the one-period
--   return and of the transition law (Lemma 3.9.4).
--
--   **Formalization Note.** The probability $\mu_a(S)$ is represented as `(μ a S).toReal`, the
--   real number underlying the extended-nonnegative-real measure of `S`; this is a faithful
--   reading of $\int_S dF(a,w)$ whenever `μ a` is a probability measure (supplied as a hypothesis
--   wherever this definition is used, since `.toReal` would otherwise silently collapse an
--   infinite measure to $0$).
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 159, Subsection 3.9.1

import Mathlib

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 159, Subsection 3.9.1 (the definition preceding Theorem 3.9.1).

"If `∫_S dF(t,w)` is an increasing ... function of `t` on `T` for each increasing set
`S` in `Rⁿ`, then `{F(t,w) : t ∈ T}` is stochastically increasing ... in `t` on `T`."
The probability that a random draw from `F(t,·)` lands in an (upward-closed) increasing
set `S` is represented here as a measure `μ a` of `S`, converted to a real number with
`ENNReal.toReal`; this is a faithful reading of "the probability measure of `S` with
respect to the distribution function `F(t,·)`" whenever `μ a` is a probability measure
(so `μ a S ≤ 1 < ⊤` and `.toReal` never collapses an infinite value to `0`) — callers
supply `IsProbabilityMeasure (μ a)` as a hypothesis where they use this definition.
-/

namespace Supermodularity.MDP

/-- `StochasticallyIncreasingOn D μ` says the family of measures `μ a` on `ℝⁿ`
(`n`-dimensional Euclidean coordinate space, represented as `Fin n → ℝ`), indexed by `a`
ranging over `D`, is stochastically increasing on `D`: for every increasing (upward-closed)
set `S ⊆ ℝⁿ`, the probability `μ a S` is a monotone function of `a` on `D`. -/
def StochasticallyIncreasingOn {α : Type*} [Preorder α] {n : ℕ}
    (D : Set α) (μ : α → MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  ∀ ⦃S : Set (Fin n → ℝ)⦄, IsUpperSet S → MonotoneOn (fun a => (μ a S).toReal) D

end Supermodularity.MDP


