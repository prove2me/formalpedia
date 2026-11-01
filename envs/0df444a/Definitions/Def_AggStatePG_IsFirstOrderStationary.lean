-- Prove2me | Definitions.Def_AggStatePG_IsFirstOrderStationary
-- name    : AggStatePG_IsFirstOrderStationary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:51.772094+00:00
-- url     : https://prove2.me/theorems/a26f3983-aa50-420d-b158-9db357e2c270
-- title:
--   Definition 1: first order stationary point of $J$ on a subset
-- statement:
--   **Definition 1.** A policy $\pi\in\Pi$ is a **first order stationary point** of $J:\Pi\to\mathbb R$ on the subset $\Pi_\phi\subset\Pi$ if
--   $$\langle\nabla J(\pi),\,\pi'-\pi\rangle\le0\qquad\forall\pi'\in\Pi_\phi.$$
--   No feasible direction improves the first-order approximation of $J$; limit points of projected gradient ascent on $\Pi_\phi$ are such points (Lemma 2).
--
--   **Formalization Note** Stated for any subset $C$ of stacked policy vectors (the paper's $C=\Pi_\phi$). As in the definition, $\pi\in\Pi$ is required but $\pi\in C$ is not. $\nabla J$ is the gradient of `Jext`, which is differentiable at every point of $\Pi$ (Lemma 5).
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, Definition 1, p.7

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm
import Definitions.Def_AggStatePG_Jext

open PolicyGradTheory.ProjGA

namespace AggStatePG

/-- **Definition 1** (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, Definition 1, p.7). A policy `π ∈ Π` is a *first order stationary
point of `J : Π → ℝ` on the subset `Π_φ ⊂ Π`* if
`⟨∇J(π), π' - π⟩ ≤ 0` for all `π' ∈ Π_φ`.

**Formalization Note.** Stated for an arbitrary subset `C` of stacked policy vectors (the paper uses
`C = Π_φ`, `aggSet φ`). `π` is a vector `x ∈ EuclideanSpace ℝ (S × A)` with `x ∈ Π = simplexSet S A`, as
in the paper's "`π ∈ Π`"; Definition 1 does not require `x ∈ C`. `∇J(π)` is Mathlib's `gradient` of
`Jext` (`(1-γ)·directValue`), with the standard inner product of p.7. `Jext` is differentiable at
every point of `Π` (milestone Lemma 5), so `gradient` is the true gradient there and not Lean's
default value `0`. -/
def IsFirstOrderStationary {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (ρ : S → ℝ)
    (C : Set (EuclideanSpace ℝ (S × A))) (x : EuclideanSpace ℝ (S × A)) : Prop :=
  x ∈ simplexSet S A ∧ ∀ x' ∈ C, inner ℝ (gradient (Jext P r γ ρ) x) (x' - x) ≤ 0

end AggStatePG


