-- Prove2me | Definitions.Def_StochFictPlay_DiscreteChoice_Simplex
-- name    : StochFictPlay_DiscreteChoice_Simplex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:24:35.853986+00:00
-- url     : https://prove2.me/theorems/e725cb5a-8753-4dda-8167-92c15b4e7bea
-- title:
--   Interior of the probability simplex and its tangent space
-- statement:
--   Let $A = \{1, \dots, n\}$ be a finite set of alternatives. The **probability simplex** over $A$ is $\Delta A = \{x \in \mathbb{R}^n_+ : \sum_j x_j = 1\}$. This file defines its relative interior
--
--   $$
--   \operatorname{int}(\Delta A) = \Big\{ y \in \mathbb{R}^n : y_i > 0 \text{ for all } i,\ \sum_{i} y_i = 1 \Big\},
--   $$
--
--   the set of mixed choices that put positive probability on every alternative, and the **tangent space** of $\Delta A$,
--
--   $$
--   \mathbb{R}^n_0 = \Big\{ z \in \mathbb{R}^n : \sum_{i} z_i = 0 \Big\},
--   $$
--
--   a linear subspace of $\mathbb{R}^n$ of dimension $n-1$. Displacements within the simplex are exactly vectors of $\mathbb{R}^n_0$.
--
--   These two sets carry the whole discrete choice theorem: the deterministic perturbation $V$ lives on $\operatorname{int}(\Delta A)$, its derivatives are taken along $\mathbb{R}^n_0$, and the choice probability function is one-to-one on payoff vectors in $\mathbb{R}^n_0$.
--
--   **Formalization Note** Alternatives are indexed by `Fin n`, i.e. $\{0, \dots, n-1\}$ instead of the paper's $\{1, \dots, n\}$. The open simplex is `openSimplex n`, a subset of `Fin n → ℝ`, and the tangent space is `tangentSpace n`, a `Submodule ℝ (Fin n → ℝ)`; a trivial membership lemma `mem_tangentSpace` unfolds it.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, pp. 4-5, §2 (definitions of ΔA and of R0n)

import Mathlib

namespace StochFictPlay.DiscreteChoice

/-- The relative interior `int(ΔA)` of the probability simplex over the alternatives
`A = {1, …, n}` (indexed here by `Fin n`): the vectors with strictly positive entries that
sum to one. Hofbauer–Sandholm (2002), p. 4. -/
def openSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 < y i) ∧ ∑ i, y i = 1}

/-- The tangent space `R₀ⁿ = {z ∈ ℝⁿ : ∑ⱼ zⱼ = 0}` of the simplex `ΔA`, as a linear
subspace of `ℝⁿ`. Hofbauer–Sandholm (2002), p. 5. -/
def tangentSpace (n : ℕ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {z | ∑ i, z i = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c z hz
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at *
    rw [← Finset.mul_sum, hz, mul_zero]

theorem mem_tangentSpace {n : ℕ} {z : Fin n → ℝ} : z ∈ tangentSpace n ↔ ∑ i, z i = 0 :=
  Iff.rfl

end StochFictPlay.DiscreteChoice


