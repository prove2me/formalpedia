-- Prove2me | Definitions.Def_TestScoreSubmod_IsSubmodularValue
-- name    : TestScoreSubmod_IsSubmodularValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:45.762831+00:00
-- url     : https://prove2.me/theorems/8da31019-2678-4930-9a7e-8b684d0eb70d
-- title:
--   Submodular value function, eq. (3)
-- statement:
--   Let $\iota$ be a finite set of items and $\mathbb R_+^{\iota}$ the set of nonnegative performance vectors. A **value function** $g:\mathbb R_+^{\iota}\to\mathbb R$ is **submodular** if for all $x,y\in\mathbb R_+^{\iota}$
--
--   $$
--   g(x\vee y)+g(x\wedge y)\le g(x)+g(y),
--   $$
--
--   where $x\vee y$ and $x\wedge y$ are the component-wise maximum and minimum.
--
--   On Boolean vectors this is the submodularity of a set function; on $\mathbb R_+^\iota$ it is the lattice form used by the paper for the value of a group of items with given performances.
--
--   **Formalization Note** Vectors are functions `ι → ℝ≥0` with the pointwise lattice operations. The nonnegativity of $g$ (the paper's codomain $\mathbb R_+$) is a separate hypothesis wherever it is used.
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, §2.1, eq. (3), p.10

import Mathlib

open scoped NNReal

namespace TestScoreSubmod

/-- **Submodular value function** (Sekar, Vojnovic, Yun, *A Test Score Based Approach to
Stochastic Submodular Optimization*, arXiv:1605.07172v4, §2.1, eq. (3), p.10).

A value function `g : ℝ₊^ι → ℝ` is submodular if for all performance vectors `x, y`,
`g (x ∨ y) + g (x ∧ y) ≤ g x + g y`, where `∨` and `∧` are the component-wise maximum and
minimum.

**Formalization Note** Performance vectors are functions `ι → ℝ≥0`; `x ⊔ y` and `x ⊓ y` are the
component-wise maximum and minimum of the `Pi` lattice. Nonnegativity of the values of `g`
(the paper's codomain `ℝ₊`) is a separate hypothesis wherever it is used. -/
def IsSubmodularValue {ι : Type*} (g : (ι → ℝ≥0) → ℝ) : Prop :=
  ∀ x y : ι → ℝ≥0, g (x ⊔ y) + g (x ⊓ y) ≤ g x + g y

end TestScoreSubmod


