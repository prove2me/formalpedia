-- Prove2me | Definitions.Def_CoupledLearning_Fprod
-- name    : CoupledLearning_Fprod
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:09.836305+00:00
-- url     : https://prove2.me/theorems/9b3dfd3f-2aee-476d-a379-d3884c9fa90b
-- title:
--   Joint strategy update $F(\theta,q)=(F_i(\theta,q))_{i\in I}$
-- statement:
--   Given player $i$'s strategy-update correspondence $F_i(\theta,q)\subseteq\mathbb R^{d_i}$, the joint update is the product
--
--   $$F(\theta,q)=\prod_{i\in I}F_i(\theta,q),$$
--
--   so $q'\in F(\theta,q)$ means $q'_i\in F_i(\theta,q)$ for every $i$. The strategy update (q-update) is $q^{k+1}\in F(\theta^{k+1},q^k)$.
-- source:
--   Wu, Amin, Ozdaglar, Convergence and Stability of Coupled Belief–Strategy Learning Dynamics in Continuous Games, arXiv:2206.05637v2, (q-update), p.8; p.9

import Mathlib
import Definitions.Def_CoupledLearning_Prof

namespace CoupledLearning

/-- The joint strategy update `F(θ, q) = (F_i(θ, q))_{i ∈ I}` (arXiv:2206.05637v2, (q-update),
p.8, and p.9): the product of the players' update sets, so `q' ∈ F(θ, q)` means
`q'_i ∈ F_i(θ, q)` for every `i`. Here `F i θ q ⊆ ℝ^{d i}` is player `i`'s set of updated
strategies given the belief `θ` and the current profile `q`. -/
def Fprod {I S : Type*} {d : I → ℕ}
    (F : (i : I) → (S → ℝ) → Prof d → Set (EuclideanSpace ℝ (Fin (d i))))
    (θ : S → ℝ) (q : Prof d) : Set (Prof d) :=
  Set.univ.pi (fun i => F i θ q)

end CoupledLearning


