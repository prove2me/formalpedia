-- Prove2me | Definitions.Def_LiftSAParity_IsNonnegMultilinear
-- name    : LiftSAParity_IsNonnegMultilinear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:29.131966+00:00
-- url     : https://prove2.me/theorems/d0389fa7-af91-46c1-afa2-e87e9d7cdce4
-- title:
--   Nonnegative combination of multilinear monomials
-- statement:
--   A real polynomial $h$ in formal variables $X$ is a **nonnegative combination of multilinear monomials** when every coefficient of $h$ is $\ge 0$ and every monomial with a nonzero coefficient has degree at most $1$ in each variable:
--   $$h=\sum_{Y\subseteq X}\alpha_Y\prod_{x\in Y}x,\qquad \alpha_Y\ge 0 .$$
--   This is the form (6) of the nonnegative part $h_\alpha$ of a Sherali–Adams refutation ($Y=\{x_i\}_{i\in A}\cup\{\bar x_j\}_{j\in B}$), and the form (12) of the nonnegative part of a semantic SA(⊕) refutation ($Y=\{x_I\}_{I\in\mathcal I}\cup\{\bar x_J\}_{J\in\mathcal J}$).
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §3, p.8, eq. (6); p.9, eq. (12)

import Mathlib

namespace LiftSAParity

/-- The polynomial `h` is a **nonnegative combination of multilinear monomials** (de
Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities
Size*, manuscript (sha256 cab5a032…), §3, p.8 eq. (6) and p.9 eq. (12)): every coefficient is
`≥ 0`, and every monomial with a nonzero coefficient has exponent at most `1` in every variable.
For SA this is the form `∑_{A,B ⊆ [n]} α_{A,B} ∏_{i∈A} x_i ∏_{j∈B} x̄_j` with `α_{A,B} ≥ 0` of (6);
for SA(⊕) it is `∑_{𝓘,𝓙} α_{𝓘,𝓙} ∏_{I∈𝓘} x_I ∏_{J∈𝓙} x̄_J` with `α ≥ 0` of (12), `𝓘, 𝓙` sets of
index sets. -/
def IsNonnegMultilinear {σ : Type*} (h : MvPolynomial σ ℝ) : Prop :=
  ∀ m : σ →₀ ℕ, 0 ≤ h.coeff m ∧ (h.coeff m ≠ 0 → ∀ x, m x ≤ 1)

end LiftSAParity


