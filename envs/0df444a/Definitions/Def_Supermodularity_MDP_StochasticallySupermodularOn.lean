-- Prove2me | Definitions.Def_Supermodularity_MDP_StochasticallySupermodularOn
-- name    : Supermodularity_MDP_StochasticallySupermodularOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:25:54.928913+00:00
-- url     : https://prove2.me/theorems/5d473934-52e8-4321-bba0-16e2970d389b
-- title:
--   Stochastically supermodular family of distributions
-- statement:
--   Let $\alpha$ be a lattice and let $\{F(a,\cdot) : a \in D\}$, $D \subseteq \alpha$, be a family
--   of distribution functions on $\mathbb{R}^n$, represented by measures $\mu_a$.
--
--   The family $\{F(a,\cdot) : a \in D\}$ is **stochastically supermodular** on $D$ if, for every
--   increasing set $S \subseteq \mathbb{R}^n$, the probability $\mu_a(S) = \int_S dF(a,w)$ is a
--   supermodular function of $a$ on $D$: $\mu_{a_1}(S) + \mu_{a_2}(S) \le \mu_{a_1 \vee a_2}(S) +
--   \mu_{a_1 \wedge a_2}(S)$ for all $a_1, a_2 \in D$.
--
--   This is Topkis's definition preceding Theorem 3.9.1, used (with $D$ a sublattice of the
--   parameter lattice) as the joint hypothesis on the transition law in Theorem 3.9.2: the
--   property that raising either coordinate of the pair $(x,t)$ complements raising the other in
--   how probability mass moves upward.
--
--   **Formalization Note.** As in `StochasticallyIncreasingOn`, $\mu_a(S)$ is represented as
--   `(μ a S).toReal`, and callers supply `IsProbabilityMeasure (μ a)`. Supermodularity of
--   $a \mapsto \mu_a(S)$ reuses the mission series' shared `SupermodularOn` definition (chunk
--   `02-monotonicity`).
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 159, Subsection 3.9.1

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

/-!
Topkis, *Supermodularity and Complementarity*, Princeton University Press, 2011,
p. 159, Subsection 3.9.1 (the definition preceding Theorem 3.9.1).

"If `T` is a sublattice of `Rᵐ` and `∫_S dF(t,w)` is a supermodular ... function of `t`
on `T` for each increasing set `S` in `Rⁿ`, then `Ftw` is stochastically supermodular
... in `t` on `T`." As in `StochasticallyIncreasingOn`, `μ a S` (converted with
`ENNReal.toReal`) stands for `∫_S dF(a,w)`; callers supply `IsProbabilityMeasure (μ a)`.
-/

namespace Supermodularity.MDP

/-- `StochasticallySupermodularOn D μ` says the family of measures `μ a` on `ℝⁿ`, indexed
by `a` ranging over the domain `D` of a lattice `α`, is stochastically supermodular on
`D`: for every increasing (upward-closed) set `S ⊆ ℝⁿ`, the probability `μ a S` is a
supermodular function of `a` on `D`. -/
def StochasticallySupermodularOn {α : Type*} [Lattice α] {n : ℕ}
    (D : Set α) (μ : α → MeasureTheory.Measure (Fin n → ℝ)) : Prop :=
  ∀ ⦃S : Set (Fin n → ℝ)⦄, IsUpperSet S →
    Supermodularity.Monotonicity.SupermodularOn (fun a => (μ a S).toReal) D

end Supermodularity.MDP


