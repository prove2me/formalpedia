-- Prove2me | Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
-- name    : SpectralProjGrad_Shared_IsProjOnto
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:57:57.032998+00:00
-- url     : https://prove2.me/theorems/39b947bb-dea3-4f64-a3ae-8d09694d5afe
-- title:
--   Orthogonal projection onto a set $\Omega\subseteq\mathbb R^n$
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ and let $P:\mathbb R^n\to\mathbb R^n$ be a map. We say that $P$ is the **orthogonal projection onto $\Omega$** if, for every $z\in\mathbb R^n$, the point $P(z)$ belongs to $\Omega$ and is a point of $\Omega$ nearest to $z$ in the Euclidean norm:
--
--   $$
--   P(z)\in\Omega \quad\text{and}\quad \|z-P(z)\|_2\le\|z-y\|_2 \quad\text{for all } y\in\Omega .
--   $$
--
--   When $\Omega$ is nonempty, closed and convex, the nearest point exists and is unique, so this property determines $P$ completely; it is the projection $P$ used by the spectral projected gradient methods SPG1 and SPG2.
--
--   Used by both missions of this paper: 01-spg2 (SPG2; p. 3, Section 2) and 02-spg1 (SPG1; p. 3, Section 2).
--
--   **Formalization Note** Mathlib has no projection map onto an arbitrary closed convex set, so the projection is passed to every statement as a function $P$ together with this characterizing predicate. The space is `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Birgin, Martínez & Raydan, Nonmonotone Spectral Projected Gradient Methods on Convex Sets, authors' updated version (July 2004) of SIAM J. Optim. 10(4) (2000), https://www.ime.unicamp.br/~martinez/bmr.pdf, p. 3, Section 2 ("Given z ∈ IRn we define P(z) the orthogonal projection on Ω")

import Mathlib

namespace SpectralProjGrad.Shared

/-- `P` is the orthogonal (Euclidean) projection onto `Ω ⊆ ℝⁿ`: for every `z`, the point `P z`
lies in `Ω` and is a point of `Ω` nearest to `z` in the Euclidean norm. (For a nonempty closed
convex `Ω` such a nearest point exists and is unique, so this characterizes `P`.) -/
def IsProjOnto {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ z : EuclideanSpace ℝ (Fin n), P z ∈ Ω ∧ ∀ y ∈ Ω, ‖z - P z‖ ≤ ‖z - y‖

end SpectralProjGrad.Shared


