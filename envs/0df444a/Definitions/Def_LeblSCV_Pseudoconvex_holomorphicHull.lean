-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_holomorphicHull
-- name    : LeblSCV_Pseudoconvex_holomorphicHull
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:45:30.806213+00:00
-- url     : https://prove2.me/theorems/4461df52-268f-4a30-a957-bc47df95a5e1
-- title:
--   Definition 2.6.1 — holomorphic hull $\widehat{K}_U$
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain and $\mathcal{O}(U)$ the holomorphic functions on $U$. For $K \subset U$, the **holomorphic hull** of $K$ is
--   $$\widehat{K}_U = \left\{ z \in U : |f(z)| \le \sup_{w \in K} |f(w)| \text{ for all } f \in \mathcal{O}(U) \right\}.$$
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. Holomorphic on an open set is `DifferentiableOn ℂ`, which is equivalent to the book's Definition 1.1.2 on open sets (Proposition 1.1.3 and Theorem 1.2.1). The moduli and the supremum are taken in $[0, \infty]$, so the supremum is genuine: $\infty$ if unbounded, $0$ for empty $K$. The definition itself does not require $U$ to be a domain.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 98, Definition 2.6.1

import Mathlib

open scoped ENNReal

namespace LeblSCV.Pseudoconvex

/-- Definition 2.6.1, holomorphic hull (Lebl, p. 98): for `K ⊂ U`,
`K̂_U = {z ∈ U : |f(z)| ≤ sup_{w ∈ K} |f(w)| for all f ∈ 𝒪(U)}`, where `𝒪(U)` is the set of
holomorphic (`DifferentiableOn ℂ`) functions on the open set `U`. The moduli and the supremum are
taken in `[0, ∞]`, so the supremum is genuine (`∞` if unbounded, `0` for empty `K`). -/
def holomorphicHull {n : ℕ} (U K : Set (EuclideanSpace ℂ (Fin n))) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | z ∈ U ∧ ∀ f : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ f U →
    (‖f z‖₊ : ℝ≥0∞) ≤ ⨆ w ∈ K, (‖f w‖₊ : ℝ≥0∞)}

end LeblSCV.Pseudoconvex


