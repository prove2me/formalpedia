-- Prove2me | Definitions.Def_AggStatePG_Jext
-- name    : AggStatePG_Jext
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:59.153981+00:00
-- url     : https://prove2.me/theorems/cae1df36-fc57-4b1b-8e52-b73f2178154a
-- title:
--   The objective $J$ on stacked policy vectors
-- statement:
--   Policies are viewed as stacked vectors $\pi=(\pi(s,a):s\in\mathcal S,a\in\mathcal A)\in\mathbb R^{|\mathcal S|\cdot|\mathcal A|}$ with the standard inner product. On such a vector $x$ the objective is
--   $$J(x)=(1-\gamma)\sum_{s}\rho(s)V_x(s),$$
--   and its Euclidean gradient $\nabla J$ is the policy gradient used in Definition 1 and Lemma 5.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (S × A)`. The published `directValue` evaluates the value series at the table $x(s,a)$; on $\Pi$ this is the paper's $J$, and near $\Pi$ the series converges and is a smooth function of $x$ (equal to $(1-\gamma)\rho(I-\gamma P_x)^{-1}r_x$), so its gradient at points of $\Pi$ is the paper's $\nabla J$.
-- source:
--   Russo, Approximation Benefits of Policy Gradient Methods with Aggregated States, arXiv:2007.11684v3, §4, p.7 (policies as stacked vectors; ∇J)

import Mathlib
import Definitions.Def_PolicyGradTheory_ProjGA_Algorithm

open PolicyGradTheory.ProjGA

namespace AggStatePG

/-- The objective `J` of (2) **on the stacked policy vectors** (Russo, *Approximation Benefits of Policy Gradient Methods with Aggregated States*, arXiv:2007.11684v3, §4, p.7: "we view each
`π ∈ Π` as a stacked vector `π = (π(s,a) : s ∈ S, a ∈ A) ∈ ℝ^{|S|·|A|}`"), whose Euclidean gradient is
the paper's `∇J(π)`: `Jext x = (1 - γ) · V^x(ρ)`.

**Formalization Note.** Vectors live in `EuclideanSpace ℝ (S × A)` (the standard inner product of
p.7). `directValue P r γ ρ x` (published, `PolicyGradTheory.ProjGA`) evaluates `∑_s ρ(s) V_x(s)` at
the table `x(s,a)`; at `x ∈ Π` it is the paper's `∑_s ρ(s) V_π(s)`, so `Jext x = J(π)` there. Off `Π`
the same series is used; near `Π` it converges and is a smooth function of `x`, so its gradient at
points of `Π` is the gradient of the paper's `J`, i.e. of `π ↦ (1-γ) ρ (I - γP_π)^{-1} r_π`. -/
noncomputable def Jext {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (ρ : S → ℝ)
    (x : EuclideanSpace ℝ (S × A)) : ℝ :=
  (1 - γ) * directValue P r γ ρ x

end AggStatePG


