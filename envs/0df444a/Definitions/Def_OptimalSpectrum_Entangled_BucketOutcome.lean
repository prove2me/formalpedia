-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_BucketOutcome
-- name    : OptimalSpectrum_Entangled_BucketOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:09.651195+00:00
-- url     : https://prove2.me/theorems/d772c4b2-c8a2-4c15-9ddd-438c113e2232
-- title:
--   Outcome space of a bucketing algorithm: a projector $\Pi$ and a sorted list of length $\mathrm{rank}\,\Pi$
-- statement:
--   An outcome of a bucketing algorithm on $\mathbb C^d$ is a pair $(\Pi,\widehat\alpha_{\mathrm{Large}})$ where
--
--   1. $\Pi\in\mathbb C^{d\times d}$ is an orthogonal projector ($\Pi^*=\Pi=\Pi^2$), the large-bucket projector, and $\overline\Pi=I-\Pi$ is the small-bucket projector;
--   2. $\widehat\alpha_{\mathrm{Large}}$ is a nonincreasing list of nonnegative numbers of length $\mathrm{rank}\,\Pi$.
--
--   **Formalization Note** The list is stored as its zero-padding to a vector of $\mathbb R^d$ (nonincreasing, nonnegative, zero from position $\mathrm{rank}\,\Pi$ on), and the matrix as its entry function, so that the outcome space carries the product Borel $\sigma$-algebra.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Definition 5.1, p. 12 (PDF p. 14)

import Mathlib

open scoped Matrix

namespace OptimalSpectrum.Entangled

/-- **Outcome space of a bucketing algorithm.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Definition 5.1, printed p. 12 (PDF p. 14): a bucketing algorithm "returns an orthogonal
projector Π, the small-bucket projector Π̄ = I − Π, and a sorted list of nonnegative numbers
α̂_Large of length rank(Π)".

An outcome is a pair `(Π, α̂)`: the entries of a `d × d` complex matrix `Π` that is an orthogonal
projector (Hermitian and idempotent), and a vector `α̂ ∈ ℝ^d` that is nonincreasing, nonnegative,
and zero from position `rank Π` on. `Π̄ = I − Π` is determined by `Π`.

**Formalization Note.** The list of length `rank Π` is stored as its zero-padding to length `d`; since
the list is nonnegative and sorted, the padded vector is sorted too and the padding is canonical. The
matrix is stored as its entry function so that the outcome space carries the product Borel
σ-algebra (Mathlib has no measurable-space instance on `Matrix`); the subtype gets the subspace
σ-algebra. -/
abbrev BucketOutcome (d : ℕ) : Type :=
  {o : (Fin d → Fin d → ℂ) × (Fin d → ℝ) //
    (Matrix.of o.1).IsHermitian ∧ Matrix.of o.1 * Matrix.of o.1 = Matrix.of o.1 ∧
    Antitone o.2 ∧ (∀ i, 0 ≤ o.2 i) ∧ ∀ i : Fin d, (Matrix.of o.1).rank ≤ i.val → o.2 i = 0}

end OptimalSpectrum.Entangled


