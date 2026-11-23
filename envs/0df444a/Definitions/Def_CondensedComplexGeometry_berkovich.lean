-- Prove2me | Definitions.Def_CondensedComplexGeometry_berkovich
-- name    : CondensedComplexGeometry_berkovich
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T01:40:26.856894+00:00
-- url     : https://prove2.me/theorems/ede6f233-003a-4937-920b-1c3d9b908961
-- title:
--   Berkovich spectrum and character space of a complex algebra
-- statement:
--   This definition introduces the two spaces compared by Ostrowski's theorem (Theorem 5.11 of Clausen–Scholze, *Condensed Mathematics and Complex Geometry*).
--
--   Let $R$ be a commutative $\mathbb C$-algebra. The **Berkovich spectrum** $\mathcal M_{\mathrm{Berk}}(R)$ is the set of bounded multiplicative seminorms, i.e. functions $|\cdot| : R \to \mathbb R_{\ge 0}$ such that
--
--   $$|xy| = |x|\,|y|,\qquad |x+y|\le |x|+|y|,\qquad |\lambda| = |\lambda|_{\mathbb C}\quad(\lambda\in\mathbb C),$$
--
--   where $\lambda$ is embedded in $R$ by the structure map $\mathbb C\to R$ and $|\cdot|_{\mathbb C}$ is the usual complex absolute value. The conditions $|0|=0$ and $|1|=1$ follow by taking $\lambda=0,1$. The set is given the subspace topology from the product $\prod_{x\in R}\mathbb R_{\ge 0}$.
--
--   The **character space** $\operatorname{Hom}_{\mathbb C}(R,\mathbb C)$ is the set of $\mathbb C$-algebra homomorphisms $R\to\mathbb C$, regarded as functions $R\to\mathbb C$ with the subspace topology from $\prod_{x\in R}\mathbb C$.
--
--   These definitions are the reusable foundation for the identification $\mathcal M_{\mathrm{Berk}}(R)\cong\operatorname{Hom}_{\mathbb C}(R,\mathbb C)$ and for further work on analytic spectra of complex algebras.
--
--   **Formalization Note.** `BerkovichSpectrum R` is a `Set (R → NNReal)` (functions into the nonnegative reals `ℝ≥0`); `ComplexCharacters R` is `Set.range` of the coercion from `R →ₐ[ℂ] ℂ` to `R → ℂ`. Both subtypes inherit the subspace topology from the Pi topology on the corresponding function type. The complex absolute value is written as the norm `‖·‖` on `ℂ`.
-- source:
--   D. Clausen, P. Scholze, Condensed Mathematics and Complex Geometry, lecture notes (Summer 2022, rev. May 2026), https://people.mpim-bonn.mpg.de/scholze/Complex.pdf, p. 55 (definition of M_Berk(R) preceding Theorem 5.11).

import Mathlib

namespace CondensedComplexGeometry

/-- The Berkovich spectrum of a commutative `ℂ`-algebra `R`: the set of bounded
multiplicative seminorms `|·| : R → ℝ≥0`, i.e. functions satisfying
`|x * y| = |x| * |y|`, `|x + y| ≤ |x| + |y|`, and restricting to the usual complex
absolute value on `ℂ` (via the structure map `algebraMap ℂ R`).

Clausen–Scholze, *Condensed Mathematics and Complex Geometry*, p. 55 (the definition
of `M_Berk(R)` preceding Theorem 5.11).  It carries the subspace topology from the
product topology on `R → ℝ≥0`. -/
def BerkovichSpectrum (R : Type*) [CommRing R] [Algebra ℂ R] : Set (R → NNReal) :=
  { v | (∀ x y, v (x * y) = v x * v y) ∧
        (∀ x y, v (x + y) ≤ v x + v y) ∧
        (∀ c : ℂ, v (algebraMap ℂ R c) = ⟨‖c‖, norm_nonneg c⟩) }

/-- The classical points of the Berkovich spectrum: the `ℂ`-algebra homomorphisms
`R →ₐ[ℂ] ℂ`, viewed as functions `R → ℂ`.  This is `Hom_ℂ(R, ℂ)` with the subspace
topology from the product topology on `R → ℂ` (pointwise convergence). -/
def ComplexCharacters (R : Type*) [CommRing R] [Algebra ℂ R] : Set (R → ℂ) :=
  Set.range (fun f : R →ₐ[ℂ] ℂ => (f : R → ℂ))

end CondensedComplexGeometry


