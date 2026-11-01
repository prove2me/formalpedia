-- Prove2me | Definitions.Def_CoupledLearning_Assumption3
-- name    : CoupledLearning_Assumption3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:37.52061+00:00
-- url     : https://prove2.me/theorems/88cca30d-fbb1-43c9-b966-92f2a9688c7f
-- title:
--   Assumption 3 (isolated equilibria, locally unique updates)
-- statement:
--   For every belief $\theta\in\Delta(S)$, either
--
--   1. $EQ(\theta)$ is a singleton, or
--   2. there is $\delta>0$ such that any two different $q^\dagger,q^\ddagger\in EQ(\theta)$ satisfy $\|q^\dagger-q^\ddagger\|>\delta$, and for every $q^\dagger\in EQ(\theta)$ there are $\xi_a,\xi_b>0$ such that $F(\theta',q)$ is a singleton for every $q\in Q$ with $\|q-q^\dagger\|<\xi_a$ and every belief $\theta'$ with $\|\theta'-\theta\|<\xi_b$.
--
--   It makes equilibria isolated and the update single-valued near each of them.
--
--   **Formalization Note** The page writes $\|\theta-\bar\theta\|<\xi_b$ with $\bar\theta$ undefined in the assumption; $\bar\theta$ is read as the $\theta$ of the preamble. Distances are Lean's sup-type distances, equivalent to the Euclidean ones; every condition asks only for some radius.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, Assumption 3, p.9

import Mathlib
import Definitions.Def_CoupledLearning_Prof
import Definitions.Def_CoupledLearning_EQ
import Definitions.Def_CoupledLearning_Fprod

namespace CoupledLearning

/-- Assumption 3, arXiv:2206.05637v2, p.9: for any `θ ∈ Δ(S)`, either
(i) `EQ(θ)` is a singleton set, or
(ii) there is `δ > 0` such that any two different equilibria `q†, q‡ ∈ EQ(θ)` satisfy
`‖q† − q‡‖ > δ`, and for any `q† ∈ EQ(θ)` there are `ξ_a, ξ_b > 0` such that for any `q` with
`‖q − q†‖ < ξ_a` and any belief `θ'` with `‖θ' − θ‖ < ξ_b`, the strategy update
`F(θ', q) = (F_i(θ', q))_{i ∈ I}` is unique.

**Formalization Note.** (a) The page writes `‖θ − θ̄‖ < ξ_b` with `θ̄` undefined in the assumption;
it is read as the `θ` of the preamble, with the varying belief renamed `θ'`. (b) "Unique" means
that `F(θ', q)` is a singleton. (c) `q` and `θ'` range over the domain `Q × Δ(S)` of `F`.
(d) Distances are Lean's: the maximum over players of Euclidean distances for profiles and the sup
distance for beliefs; both are equivalent to the Euclidean ones, and every condition here asks
only for some radius. -/
def Assumption3 {I S : Type*} [Fintype I] [Fintype S] [DecidableEq I] {d : I → ℕ}
    (Q : (i : I) → Set (EuclideanSpace ℝ (Fin (d i))))
    (u : S → I → Prof d → ℝ)
    (F : (i : I) → (S → ℝ) → Prof d → Set (EuclideanSpace ℝ (Fin (d i)))) : Prop :=
  ∀ θ ∈ stdSimplex ℝ S,
    (∃ q₀, EQ Q u θ = {q₀}) ∨
    ((∃ δ > 0, ∀ q₁ ∈ EQ Q u θ, ∀ q₂ ∈ EQ Q u θ, q₁ ≠ q₂ → δ < dist q₁ q₂) ∧
      ∀ qd ∈ EQ Q u θ, ∃ ξa > 0, ∃ ξb > 0, ∀ q ∈ Qset Q, dist q qd < ξa →
        ∀ θ' ∈ stdSimplex ℝ S, dist θ' θ < ξb → ∃ p, Fprod F θ' q = {p})

end CoupledLearning


