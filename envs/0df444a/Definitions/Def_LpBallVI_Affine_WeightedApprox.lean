-- Prove2me | Definitions.Def_LpBallVI_Affine_WeightedApprox
-- name    : LpBallVI_Affine_WeightedApprox
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:10:59.560785+00:00
-- url     : https://prove2.me/theorems/b77fabc9-b8f9-4433-bac6-1e5382389069
-- title:
--   Compactly supported and rational piecewise-linear functions, the weighted approximation N_{f,λ} and its realization N̂_{f,λ}
-- statement:
--   A function $f : \mathbb R \to \mathbb R$ is **compactly supported** (Definition 4.5) if there is $S > 0$ with $f(t) = 0$ for all $|t| \ge S$. It is **rational piecewise-linear** if there is a finite set $B$ of rational breakpoints such that on every closed interval $[t_1, t_2]$ whose interior contains no point of $B$, $f(t) = mt + c$ for some rationals $m, c$.
--
--   For coefficients $\alpha_j, a_j, \beta_j$, $j \in [m]$, the **weighted approximation function** is
--   $$N_{f,\lambda}(t) = \sum_{j=1}^m \alpha_j\, k_\lambda(a_j t + \beta_j),$$
--   and its **realization** from auxiliary variables $w^-_j, w^0_j, w^+_j$ is $\hat N_{f,\lambda} = \varsigma_p \sum_j \alpha_j (w^+_j + w^-_j - 2w^0_j)$ (33).
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 25, Definition 4.5, Lemma 4.6, (23); p. 28, (33)

import Mathlib
import Definitions.Def_LpBallVI_Affine_Sigma

set_option autoImplicit false

namespace LpBallVI.Affine

open scoped BigOperators

/-- **Compactly supported** (Definition 4.5, Anagnostides–Panageas–Yan, arXiv:2611.04151, p. 25):
there is `S > 0` with `f(t) = 0` for all `|t| ≥ S`. -/
def IsCompactlySupported (f : ℝ → ℝ) : Prop :=
  ∃ S : ℝ, 0 < S ∧ ∀ t : ℝ, S ≤ |t| → f t = 0

/-- **Rational piecewise-linear** (Lemma 4.6, p. 25): there is a finite set `B` of rational
breakpoints such that on every closed interval `[t₁, t₂]` with no breakpoint in its interior,
`f` coincides with an affine function `t ↦ m t + c` with rational slope `m` and intercept `c`. -/
def IsRatPiecewiseLinear (f : ℝ → ℝ) : Prop :=
  ∃ B : Finset ℚ, ∀ t₁ t₂ : ℝ, t₁ < t₂ → (∀ b ∈ B, (b : ℝ) ≤ t₁ ∨ t₂ ≤ (b : ℝ)) →
    ∃ m c : ℚ, ∀ t : ℝ, t₁ ≤ t → t ≤ t₂ → f t = (m : ℝ) * t + (c : ℝ)

/-- The weighted approximation function `N_{f,λ}(t) = ∑_{j=1}^m α_j k_λ(a_j t + β_j)` ((23),
p. 25), for coefficients `α, a, β : Fin m → ℝ`. -/
noncomputable def weightedApprox (p lam : ℝ) {m : ℕ} (α a β : Fin m → ℝ) (t : ℝ) : ℝ :=
  ∑ j, α j * kLam p lam (a j * t + β j)

/-- The realization `N̂_{f,λ}(t) = ς_p ∑_{j=1}^m α_j (w⁺_j + w⁻_j − 2w⁰_j)` ((33), p. 28) from the
auxiliary variables `w⁻, w⁰, w⁺ : Fin m → ℝ`. -/
noncomputable def realization (p : ℝ) {m : ℕ} (α : Fin m → ℝ) (wm w0 wp : Fin m → ℝ) : ℝ :=
  varsigma p * ∑ j, α j * (wp j + wm j - 2 * w0 j)

end LpBallVI.Affine


