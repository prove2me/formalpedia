-- Prove2me | Definitions.Def_StochLinOpt_ConfBall2_IsConfBall2Run
-- name    : StochLinOpt_ConfBall2_IsConfBall2Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:49:00.556187+00:00
-- url     : https://prove2.me/theorems/a67238ef-dbfd-4429-a8e1-d3be435b3c83
-- title:
--   A run of ConfidenceBall$_2(D,\delta)$
-- statement:
--   Let $D\subset\mathbb R^n$, let $b$ be a barycentric spanner for $D$ and $\delta$ a confidence parameter. A sequence of decisions $x_1,x_2,\dots$ together with observed losses $\ell_1,\ell_2,\dots$ is a **run of ConfidenceBall$_2(D,\delta)$** if, for every round $t\ge1$,
--
--   $$x_t\in\operatorname*{argmin}_{x\in D}\ \min_{\nu\in B^2_t}\nu^\top x ,$$
--
--   where $B^2_t$ is built from $x_1,\dots,x_{t-1}$ and $\ell_1,\dots,\ell_{t-1}$. Equivalently, $x_t\in D$ and some $\nu_0\in B^2_t$ satisfies $\nu_0^\top x_t\le\nu^\top y$ for all $y\in D$ and $\nu\in B^2_t$.
--
--   This is one sample path of Algorithm 3.1, with any rule for breaking ties.
--
--   **Formalization Note** The argmin is stated as the joint minimizer $(x_t,\nu_0)$, which is equivalent because $D$ and $B^2_t$ are compact and nonempty. In the stochastic model the tie-breaking rule must depend only on the history (see the model definition).
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, Algorithm 3.1, p. 4

import Mathlib
import Definitions.Def_StochLinOpt_ConfBall2_confBall
open Matrix

namespace StochLinOpt.ConfBall2

/-- **A run of ConfidenceBall₂(D, δ)** (Dani, Hayes, Kakade, *Stochastic Linear Optimization under Bandit Feedback*, COLT 2008, Algorithm 3.1, p. 4:
"for t ← 1 to ∞ … xt = argmin_{x∈D} min_{ν∈B2t} (ν†x); Incur and observe loss ℓt := ct(xt)").

`IsConfBall2Run D b δ ℓ x` says that the decision sequence `x` is one path of the algorithm with
spanner `b` against the observed losses `ℓ`: for every round `t ≥ 1`, `x t ∈ D` and there is
`ν₀ ∈ B²_t` with `ν₀ᵀ x_t ≤ νᵀ y` for all `y ∈ D` and `ν ∈ B²_t`, where `B²_t` is built from the
decisions and losses of rounds `1, …, t − 1` only.

**Formalization Note** The argmin is encoded as a joint minimizer `(x_t, ν₀)` of `νᵀy` over
`D × B²_t`. Because `D` and `B²_t` are compact and nonempty this is equivalent to
`x_t ∈ argmin_{x∈D} min_{ν∈B²_t} νᵀx`; ties may be broken by any rule (the probabilistic model
`IsStochLinEnv` requires the rule to depend only on the history). Rounds are 1-based; index `0`
of `x` and `ℓ` is never read. -/
def IsConfBall2Run {n : ℕ} (D : Set (Fin n → ℝ)) (b : Fin n → Fin n → ℝ) (δ : ℝ) (ℓ : ℕ → ℝ)
    (x : ℕ → Fin n → ℝ) : Prop :=
  ∀ t, 1 ≤ t → x t ∈ D ∧
    ∃ ν₀ ∈ confBall b x ℓ δ t, ∀ y ∈ D, ∀ ν ∈ confBall b x ℓ δ t, ν₀ ⬝ᵥ x t ≤ ν ⬝ᵥ y

end StochLinOpt.ConfBall2


