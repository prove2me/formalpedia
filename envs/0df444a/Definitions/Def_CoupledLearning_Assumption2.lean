-- Prove2me | Definitions.Def_CoupledLearning_Assumption2
-- name    : CoupledLearning_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:49.571177+00:00
-- url     : https://prove2.me/theorems/51b8981b-4aff-4b81-b5bf-5395ec2b981c
-- title:
--   Assumption 2 (convergence in static information environment)
-- statement:
--   For every belief $\theta\in\Delta(S)$:
--
--   1. $EQ(\theta)$ is nonempty;
--   2. every sequence with $q^1\in Q$ and $q^{n+1}\in F(\theta,q^n)$ for all $n$ converges to a point of $EQ(\theta)$.
--
--   It says that the strategy dynamics converges when the belief is held fixed.
--
--   **Formalization Note** "Given any initial strategy, the strategy update with static belief $\theta$ converges to an equilibrium" is read as convergence of every selection, as the proof of Lemma 3 uses it. Sequences are indexed from $0$.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Assumption 2, p.9

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_EQ
import Definitions.Def_CoupledLearning_Fprod

open Filter Topology

namespace CoupledLearning

/-- Assumption 2 (convergence in static information environment), arXiv:2206.05637v2, p.9: for
any belief `θ`, the equilibrium set `EQ(θ)` of `G(θ)` is non-empty, and, given any initial
strategy, the strategy update (q-update) with static belief `θ` converges to an equilibrium of
`G(θ)`.

**Formalization Note.** "The strategy update with static belief `θ` converges" is read as: every
sequence `q^1 ∈ Q`, `q^{n+1} ∈ F(θ, q^n)` converges to a point of `EQ(θ)`. The proof (p.23,
construction (9)) applies the assumption to arbitrary selections of `F(θ, ·)`. Sequences are
indexed from `0`. -/
def Assumption2 {I S : Type*} [Fintype S] [DecidableEq I] {d : I → ℕ}
    (Q : (i : I) → Set (EuclideanSpace ℝ (Fin (d i))))
    (u : S → I → Prof d → ℝ)
    (F : (i : I) → (S → ℝ) → Prof d → Set (EuclideanSpace ℝ (Fin (d i)))) : Prop :=
  ∀ θ ∈ stdSimplex ℝ S, (EQ Q u θ).Nonempty ∧
    ∀ x : ℕ → Prof d, x 0 ∈ Qset Q → (∀ n, x (n + 1) ∈ Fprod F θ (x n)) →
      ∃ qbar ∈ EQ Q u θ, Tendsto x atTop (𝓝 qbar)

end CoupledLearning


