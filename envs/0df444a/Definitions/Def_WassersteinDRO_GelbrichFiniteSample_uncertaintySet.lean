-- Prove2me | Definitions.Def_WassersteinDRO_GelbrichFiniteSample_uncertaintySet
-- name    : WassersteinDRO_GelbrichFiniteSample_uncertaintySet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:56:52.768504+00:00
-- url     : https://prove2.me/theorems/30b1cbdb-9610-4070-a630-740f9403f767
-- title:
--   Mean-covariance uncertainty set $\mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma)$
-- statement:
--   Let $\varepsilon \in \mathbb R$, $\widehat\mu \in \mathbb R^m$ and let $\widehat\Sigma$ be an $m \times m$ matrix. The **uncertainty set** is
--
--   $$\mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma) = \Big\{ (\mu, \Sigma) \in \mathbb R^m \times \mathbb S^m_+ : \|\widehat\mu - \mu\|_2^2 + \operatorname{Tr}\Big[\widehat\Sigma + \Sigma - 2\big(\widehat\Sigma^{1/2} \Sigma \widehat\Sigma^{1/2}\big)^{1/2}\Big] \le \varepsilon^2 \Big\},$$
--
--   where $\mathbb S^m_+$ is the cone of symmetric positive semidefinite matrices and $A^{1/2}$ is the positive semidefinite square root. The left-hand side of the inequality is the squared Gelbrich distance between the mean-covariance pairs $(\widehat\mu, \widehat\Sigma)$ and $(\mu, \Sigma)$.
--
--   The Gelbrich hull is the set of distributions whose mean and covariance lie in this set.
--
--   **Formalization Note** The square roots are Mathlib's continuous functional calculus `CFC.sqrt` with the Loewner order, which is the positive semidefinite square root on $\mathbb S^m_+$. The paper assumes $\widehat\Sigma \in \mathbb S^m_+$ throughout §2.3; that is a hypothesis of the statements that need it, not part of the set. The trace term is not replaced by $\|\widehat\Sigma^{1/2} - \Sigma^{1/2}\|_F^2$, which differs unless the two matrices commute.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §2.3, unnumbered display defining U_ε(µ̂, Σ̂), p. 16

import Mathlib

open scoped MatrixOrder

namespace WassersteinDRO.GelbrichFiniteSample

/-- **The mean-covariance uncertainty set `U_ε(µ̂, Σ̂)`.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §2.3, unnumbered display, p. 16: "We first define an uncertainty set in the space of mean
vectors and covariance matrices.
U_ε(µ̂, Σ̂) = {(µ, Σ) ∈ R^m × S^m_+ : ‖µ̂ − µ‖₂² + Tr[Σ̂ + Σ − 2(Σ̂^{1/2} Σ Σ̂^{1/2})^{1/2}] ≤ ε²}".

`uncertaintySet ε µ̂ Σ̂` is the set of pairs `(µ, Σ)` with `Σ` symmetric positive semidefinite and
`‖µ̂ − µ‖₂² + Tr[Σ̂ + Σ − 2 (Σ̂^{1/2} Σ Σ̂^{1/2})^{1/2}] ≤ ε²`. The left-hand side is the squared
Gelbrich distance between `(µ̂, Σ̂)` and `(µ, Σ)` (eq. (8), p. 8).

**Formalization Note.** `ℝ^m` is `EuclideanSpace ℝ (Fin m)` (Euclidean norm `‖·‖₂`). `S^m_+` is
`Matrix.PosSemidef`, which includes symmetry. The square roots are `CFC.sqrt` (continuous functional
calculus with the Loewner order, `open scoped MatrixOrder`): on a positive semidefinite matrix it is
the unique positive semidefinite square root. The paper assumes `Σ̂ ∈ S^m_+` throughout §2.3
(p. 16); this is a hypothesis of the statements that need it, not part of the set (off the PSD
cone `CFC.sqrt` returns a junk value, and no statement of the mission uses that case: `Σ̂` is a
sample covariance or is assumed PSD, and then `Σ̂^{1/2} Σ Σ̂^{1/2}` is PSD). The radius `ε` is a
real number; the theorems of the mission use it with `ε > 0`. The Bures term is not replaced by
`‖Σ̂^{1/2} − Σ^{1/2}‖_F²`, which differs unless `Σ̂` and `Σ` commute. -/
noncomputable def uncertaintySet {m : ℕ} (ε : ℝ) (μh : EuclideanSpace ℝ (Fin m))
    (Sigh : Matrix (Fin m) (Fin m) ℝ) : Set (EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ) :=
  {p | p.2.PosSemidef ∧
    ‖μh - p.1‖ ^ 2 + (Sigh + p.2 - 2 • CFC.sqrt (CFC.sqrt Sigh * p.2 * CFC.sqrt Sigh)).trace ≤ ε ^ 2}

end WassersteinDRO.GelbrichFiniteSample


