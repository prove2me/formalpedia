-- Prove2me | Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
-- name    : PolicyGradTheory_ProjGA_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T10:19:31.909194+00:00
-- url     : https://prove2.me/theorems/82d2d6d0-5801-4c65-b767-340b02aa13c0
-- title:
--   Direct parameterization (2), the product simplex Δ(A)^{|S|}, π ↦ V^π(μ), and projected gradient ascent (9)
-- statement:
--   This module sets up the direct policy parameterization and the projected gradient ascent algorithm of §4.
--
--   1. **Direct parameterization** (2). A parameter is a vector $\pi\in\mathbb R^{\mathcal S\times\mathcal A}$, read as the table $\pi(a\mid s)=\pi_{s,a}$.
--   2. **Product simplex.** $\Delta(\mathcal A)^{|\mathcal S|}$ is the set of parameters with $\pi_{s,a}\ge0$ and $\sum_{a\in\mathcal A}\pi_{s,a}=1$ for every $s\in\mathcal S$, i.e. the set of all (stochastic) policies.
--   3. **Objective.** For a start distribution $\mu$, the map $\pi\mapsto V^\pi(\mu)$, whose Euclidean gradient $\nabla_\pi V^\pi(\mu)$ has the coordinates $\partial V^\pi(\mu)/\partial\pi(a\mid s)$.
--   4. **Projected gradient ascent** (9). A sequence $(\pi^{(t)})_{t\ge0}$ is a run with step size $\eta$ if
--   $$
--   \pi^{(t+1)}=P_{\Delta(\mathcal A)^{|\mathcal S|}}\big(\pi^{(t)}+\eta\nabla_\pi V^{(t)}(\mu)\big)\qquad\text{for all }t\ge0,
--   $$
--   where $V^{(t)}=V^{\pi^{(t)}}$ and $P_{\Delta(\mathcal A)^{|\mathcal S|}}$ is the Euclidean projection onto the product simplex.
--
--   These are the objects of Theorem 4.1, the paper's iteration complexity bound for projected gradient ascent on the policy simplex.
--
--   **Formalization Note** Parameters live in `EuclideanSpace ℝ (S × A)`, so that the norm is the $\ell_2$ norm and Mathlib's `gradient` is $\nabla_\pi$. The objective is defined on the whole space by plugging the table into the value function; it agrees with $V^\pi(\mu)$ on the simplex, and only its values and gradient at policies are used. The gradient formula (7) is a separate theorem, not part of the definition. The projection is any map satisfying the projection predicate.
-- source:
--   arXiv:1908.00261v5, (2), p. 10; §4, p. 13; §4.2, (9), p. 15

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_MDP
import Definitions.Def_PolicyGradTheory_ProjGA_Projection

namespace PolicyGradTheory.ProjGA

open FoundationsML.ReinforcementLearning

/-- The direct parameterization (2) (arXiv:1908.00261v5, p. 10): a parameter vector
`π ∈ ℝ^{S × A}` read as the table `π(a|s) = π_{s,a}`. -/
def asPolicy {S A : Type*} (π : EuclideanSpace ℝ (S × A)) : S → A → ℝ :=
  fun s a => π (s, a)

/-- The product simplex `∆(A)^{|S|}` (p. 10): the parameter vectors whose table is a policy,
`π_{s,a} ≥ 0` and `∑_a π_{s,a} = 1` for every `s`. -/
def simplexSet (S A : Type*) [Fintype A] : Set (EuclideanSpace ℝ (S × A)) :=
  {π | IsPolicy (asPolicy π)}

/-- The objective `π ↦ V^π(μ)` of the direct parameterization, as a function on the whole
parameter space `ℝ^{S × A}` (it is the paper's `V^π(μ)` at points of `simplexSet`). Its
Euclidean gradient is the paper's `∇_π V^π(μ)`. -/
noncomputable def directValue {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ)
    (π : EuclideanSpace ℝ (S × A)) : ℝ :=
  valueAt (asPolicy π) P r γ μ

/-- A run of projected gradient ascent (9) (p. 15) on `V^π(μ)` with step size `η` and projection
`Proj`: `π^{(t+1)} = Proj(π^{(t)} + η ∇_π V^{(t)}(μ))` for every `t`. -/
def IsProjGARun {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (μ : S → ℝ) (η : ℝ)
    (Proj : EuclideanSpace ℝ (S × A) → EuclideanSpace ℝ (S × A))
    (π : ℕ → EuclideanSpace ℝ (S × A)) : Prop :=
  ∀ t : ℕ, π (t + 1) = Proj (π t + η • gradient (directValue P r γ μ) (π t))

end PolicyGradTheory.ProjGA


