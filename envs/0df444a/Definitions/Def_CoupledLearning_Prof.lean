-- Prove2me | Definitions.Def_CoupledLearning_Prof
-- name    : CoupledLearning_Prof
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:27.258886+00:00
-- url     : https://prove2.me/theorems/cc7aec6e-1fb6-4e14-aae3-4704fcc1f35f
-- title:
--   Strategy profiles $q=(q_i)_{i\in I}$ and the feasible set $Q=\prod_i Q_i$
-- statement:
--   Player $i$ of a finite set $I$ chooses a finite-dimensional strategy vector $q_i\in\mathbb R^{d_i}$. A **strategy profile** is $q=(q_i)_{i\in I}$, and for strategy sets $Q_i\subseteq\mathbb R^{d_i}$ the **feasible profiles** form the product
--
--   $$Q=\prod_{i\in I}Q_i .$$
--
--   These are the state variables of the strategy part of the learning dynamics.
--
--   **Formalization Note** $\mathbb R^{d_i}$ is `EuclideanSpace ℝ (Fin (d i))` and a profile is a dependent function. Lean's distance on profiles is the maximum of the players' Euclidean distances, which is equivalent to the Euclidean distance on the product.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, §2, p.7

import Mathlib

namespace CoupledLearning

/-- Strategy profiles of the game `G` (Wu, Amin, Ozdaglar, *Convergence and Stability of Coupled
Belief–Strategy Learning Dynamics in Continuous Games*, arXiv:2206.05637v2, §2, p.7): player
`i ∈ I` chooses a finite-dimensional vector `q_i ∈ ℝ^{d i}`, and a profile is `q = (q_i)_{i ∈ I}`.

**Formalization Note.** `ℝ^{d i}` is `EuclideanSpace ℝ (Fin (d i))`. A profile is a dependent
function `(i : I) → ℝ^{d i}`; Lean's distance on it is the maximum of the players' Euclidean
distances (equivalent to the Euclidean norm on the product, so every "there is a radius"
statement is unchanged). -/
abbrev Prof {I : Type*} (d : I → ℕ) : Type _ := (i : I) → EuclideanSpace ℝ (Fin (d i))

/-- The set of feasible profiles `Q = ∏_{i ∈ I} Q_i` (arXiv:2206.05637v2, §2, p.7), for strategy
sets `Q i ⊆ ℝ^{d i}`. -/
def Qset {I : Type*} {d : I → ℕ} (Q : (i : I) → Set (EuclideanSpace ℝ (Fin (d i)))) :
    Set (Prof d) :=
  Set.univ.pi Q

end CoupledLearning


