-- Prove2me | Definitions.Def_KnownFidelity_Rank_instMeasurableSpaceMatrix
-- name    : KnownFidelity_Rank_instMeasurableSpaceMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:47.915009+00:00
-- url     : https://prove2.me/theorems/4ea7206c-aef0-4986-aaf9-4255639c7972
-- title:
--   Borel $\sigma$-algebra on complex matrices
-- statement:
--   Priors on states are probability measures on matrices. Complex $m\times n$ matrices carry the product $\sigma$-algebra of their entries, which for finite $m,n$ is the Borel $\sigma$-algebra of the entrywise topology.
--
--   **Formalization Note** Mathlib (at this revision) has no measurable-space instance on `Matrix`; this instance supplies it.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Lemma 2.1, p. 4 (PDF p. 6); Proposition 4.1, p. 8 (PDF p. 10)

import Mathlib

namespace KnownFidelity.Rank

/-- **Borel σ-algebra on complex matrices** (structural instance).
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Lemma 2.1, printed p. 4 (PDF p. 6), and Proposition 4.1, printed p. 8
(PDF p. 10), use "priors on states", i.e. probability measures on matrices.

**Formalization Note.** Mathlib (at this revision) has no measurable space on `Matrix m n ℂ`; this
is the product σ-algebra of the entry functions (`Matrix m n ℂ = m → n → ℂ`), which for finite
`m, n` is the Borel σ-algebra of the entrywise topology. -/
noncomputable instance instMeasurableSpaceMatrix (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

end KnownFidelity.Rank


