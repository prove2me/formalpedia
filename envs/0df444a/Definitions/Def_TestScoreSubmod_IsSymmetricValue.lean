-- Prove2me | Definitions.Def_TestScoreSubmod_IsSymmetricValue
-- name    : TestScoreSubmod_IsSymmetricValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:01.770064+00:00
-- url     : https://prove2.me/theorems/99be1974-e4b0-4da9-a252-175ffc85dba9
-- title:
--   Symmetric value function
-- statement:
--   A value function $g:\mathbb R_+^{\iota}\to\mathbb R$ is **symmetric** if its value does not depend on the order of its arguments: for every vector $x$ and every permutation $\sigma$ of the coordinates,
--
--   $$
--   g(x\circ\sigma)=g(x).
--   $$
--
--   The group value of a set of items then depends only on the multiset of their performances, not on which items produced them.
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, §2.2, p.12

import Mathlib

open scoped NNReal

namespace TestScoreSubmod

/-- **Symmetric value function** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, §2.2, p.12:
"its value is invariant to permutations of its input arguments, i.e. for every x ∈ ℝⁿ,
g(x) = g(π(x)) for any permutation π(x) of the elements {x₁, …, xₙ}").

`g` is symmetric if `g (x ∘ σ) = g x` for every performance vector `x` and every permutation
`σ` of the coordinates. -/
def IsSymmetricValue {ι : Type*} (g : (ι → ℝ≥0) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm ι) (x : ι → ℝ≥0), g (x ∘ σ) = g x

end TestScoreSubmod


