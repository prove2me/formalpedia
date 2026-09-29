-- Prove2me | Definitions.Def_SpectralProjGrad_Shared_IsConstrainedStationary
-- name    : SpectralProjGrad_Shared_IsConstrainedStationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:58:38.349985+00:00
-- url     : https://prove2.me/theorems/90357942-f49f-4fa2-9458-3aec57bac791
-- title:
--   Constrained stationary point of $f$ on $\Omega$
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ and $f:\mathbb R^n\to\mathbb R$ with gradient $g=\nabla f$. A point $\bar x$ is a **constrained stationary point** of $f$ on $\Omega$ if
--
--   $$
--   \langle g(\bar x),\,x-\bar x\rangle\ge 0\qquad\text{for all } x\in\Omega .
--   $$
--
--   This is the first-order necessary condition for $\bar x$ to minimize $f$ over a convex set $\Omega$; it is the conclusion of the global convergence theorems for SPG1 and SPG2.
--
--   Used by both missions of this paper: 01-spg2 (SPG2; p. 5, conclusion of Theorem 2.1 and Lemma 2.1 (ii)) and 02-spg1 (SPG1; p. 5, conclusion of Theorem 2.2 and Lemma 2.1 (ii)).
--
--   **Formalization Note** The inner product is the Euclidean one on `EuclideanSpace ℝ (Fin n)` and $g$ is Mathlib's `gradient f`. Membership $\bar x\in\Omega$ is not part of the definition; in the statements that use it, $\bar x\in\Omega$ is assumed or follows from closedness of $\Omega$.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 5, displayed definition before Theorem 2.1

import Mathlib

namespace SpectralProjGrad.Shared

/-- `x̄` is a constrained stationary point of `f` on `Ω`: `⟨∇f(x̄), x - x̄⟩ ≥ 0` for all `x ∈ Ω`. -/
def IsConstrainedStationary {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x ∈ Ω, inner ℝ (gradient f xbar) (x - xbar) ≥ 0

end SpectralProjGrad.Shared


