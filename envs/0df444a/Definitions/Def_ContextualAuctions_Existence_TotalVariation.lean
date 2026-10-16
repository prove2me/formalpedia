-- Prove2me | Definitions.Def_ContextualAuctions_Existence_TotalVariation
-- name    : ContextualAuctions_Existence_TotalVariation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:21.486982+00:00
-- url     : https://prove2.me/theorems/27ed0efe-e24e-4559-a0f7-5df851dcd18c
-- title:
--   Definition 3, p. 9 — divergence, C¹_c test fields with ‖φ‖_∞ ≤ 1, and the total variation V(u, Ω) of a function on an open set Ω ⊂ ℝᵐ
-- statement:
--   This module defines the multivariate total variation of Definition 3 (Evans–Gariepy, §5.1), for a general dimension $m$. The divergence is the published definition `TeschlODE.HigherDim.divergence`.
--
--   For a vector field $\phi:\mathbb R^m\to\mathbb R^m$ its **divergence** is $\operatorname{div}\phi=\sum_{i=1}^m \partial\phi_i/\partial x_i$. For an open set $\Omega\subset\mathbb R^m$, a **test field** is a continuously differentiable $\phi$ with compact support contained in $\Omega$ and $\|\phi(x)\|\le 1$ for every $x$, where $\|\cdot\|$ is the Euclidean norm; the class of such fields is written $C^1_c(\Omega,\mathbb R^m)$ with $\|\phi\|_\infty\le1$. The **total variation** of a function $u\in L_1(\Omega)$ is
--
--   $$
--   V(u,\Omega)=\sup\Big\{\int_\Omega u(x)\,\operatorname{div}\phi(x)\,dx \;\Big|\; \phi\in C^1_c(\Omega,\mathbb R^m),\ \|\phi\|_\infty\le 1\Big\},
--   $$
--
--   the integral being with respect to Lebesgue measure.
--
--   In the mission, $m=d+1$ and $\Omega=\Theta$; the bound $V(\ell^\mu,\Theta)\le V_0$ (Lemma 3) is what puts the smallest dual minimizer into the compact set $\mathcal X_0$ on which the fixed-point argument runs.
--
--   **Formalization Note** The supremum is taken in the extended reals `EReal`, so an unbounded family of test integrals gives $+\infty$ rather than a junk value, and a bound $V\le V_0$ is a real constraint. Vectors live in `EuclideanSpace ℝ (Fin m)`, whose norm is Euclidean (the norm of `Fin m → ℝ` would be the sup norm). The paper writes $n$ for the dimension; here it is $m$, since $n$ is the number of buyers. The definition is stated for every function $u$; the mission only applies it to Lebesgue-integrable functions on $\Omega$, as Definition 3 does.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 9, Definition 3

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_divergence

namespace ContextualAuctions.Existence

open MeasureTheory

/-- `φ ∈ C¹_c(Ω, ℝᵐ)` with `‖φ‖_∞ ≤ 1`: a continuously differentiable vector field of compact
support contained in `Ω`, whose Euclidean norm is at most `1` at every point. -/
def IsTestField {m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin m)))
    (φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) : Prop :=
  ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧ ∀ x, ‖φ x‖ ≤ 1

/-- Total variation (Definition 3): `V(u, Ω) = sup { ∫_Ω u div φ | φ ∈ C¹_c(Ω, ℝᵐ), ‖φ‖_∞ ≤ 1 }`,
with `div φ = ∑ᵢ ∂φᵢ/∂xᵢ` the divergence `TeschlODE.HigherDim.divergence`, computed in `EReal` so that an unbounded family of test integrals gives `⊤`. The integral is the
Lebesgue integral on `ℝᵐ` restricted to `Ω`. -/
noncomputable def totalVariation {m : ℕ} (u : EuclideanSpace ℝ (Fin m) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin m))) : EReal :=
  ⨆ (φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (_ : IsTestField Ω φ),
    ((∫ x in Ω, u x * TeschlODE.HigherDim.divergence φ x : ℝ) : EReal)

end ContextualAuctions.Existence


