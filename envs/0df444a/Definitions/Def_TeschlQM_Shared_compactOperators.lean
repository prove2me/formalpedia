-- Prove2me | Definitions.Def_TeschlQM_Shared_compactOperators
-- name    : TeschlQM_Shared_compactOperators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:36:54.050109+00:00
-- url     : https://prove2.me/theorems/bd38a87c-a0dd-420e-af1f-6109fa09f0c2
-- title:
--   Finite rank operators and the compact operators ℭ(ℌ)
-- statement:
--   An operator $K \in \mathfrak L(\mathfrak H)$ (bounded, everywhere defined) is a **finite rank operator** if its range $\operatorname{Ran}(K)$ is finite dimensional. The set $\mathfrak C(\mathfrak H)$ of **compact operators** is the closure, in the operator norm of $\mathfrak L(\mathfrak H)$, of the set of all finite rank operators.
--
--   This one definition is shared by every chunk of the series that uses it and is reviewed once for all of them. It serves:
--
--   - chunk `05-rage`: p. 128, Section 5.2, Eq. (5.12); p. 73, Eq. (2.66); p. 128, Lemma 5.5; p. 128, Theorem 5.6, Eq. (5.13); p. 129, Theorem 5.7, Eq. (5.14); p. 130, Theorem 5.8, Eq. (5.18); p. 130, Corollary 5.9, Eqs. (5.19)–(5.20)
--   - chunk `07-trace-class`: p. 140, Eq. (6.14); p. 141, Eq. (6.20); p. 142; p. 137, Theorem 6.7; p. 140, Lemma 6.10; p. 141, Corollary 6.11; p. 141, Lemma 6.12; pp. 142–143, Lemma 6.13; p. 143, Corollary 6.14; p. 143, Lemma 6.15; p. 144, Lemma 6.16
--
--   **Formalization Note.** This is the book's definition by approximation, not Mathlib's `IsCompactOperator` (images of bounded sets are relatively compact); the two agree on Hilbert spaces, but that is not assumed anywhere.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, pp. 127–128, Section 5.2

import Mathlib

namespace TeschlQM.Shared

/-- Teschl, p. 127: `K ∈ 𝔏(ℌ)` is a **finite rank operator** if its range is finite dimensional. -/
def IsFiniteRank {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : H →L[ℂ] H) : Prop :=
  FiniteDimensional ℂ (LinearMap.range (K : H →ₗ[ℂ] H))

/-- Teschl, p. 128: the set `ℭ(ℌ)` of **compact operators** is the closure in `𝔏(ℌ)` (operator
norm topology) of the set of all finite rank operators. -/
def compactOperators (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    Set (H →L[ℂ] H) :=
  closure {K : H →L[ℂ] H | IsFiniteRank K}

end TeschlQM.Shared


