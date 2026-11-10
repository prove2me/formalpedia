-- Prove2me | Definitions.Def_KnownFidelity_Rank_IsStatePrior
-- name    : KnownFidelity_Rank_IsStatePrior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:45.125499+00:00
-- url     : https://prove2.me/theorems/25bea923-6886-4b91-ba26-23a66507e810
-- title:
--   A prior on states: a probability measure carried by density matrices
-- statement:
--   A **prior on states** on $\mathbb C^\iota$ is a probability measure $\Lambda$ on $\iota\times\iota$ complex matrices such that $\Lambda$-almost every matrix $\tau$ is a density matrix. The two-prior method (Lemma 2.1) and the hard instances of Proposition 4.1 are stated for such priors.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Lemma 2.1, p. 4 (PDF p. 6); Proposition 4.1, p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_KnownFidelity_Rank_instMeasurableSpaceMatrix

open MeasureTheory

namespace KnownFidelity.Rank

/-- **A prior on states.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Lemma 2.1, printed p. 4 (PDF p. 6): "Let Π₀, Π₁ be priors on states", and
Proposition 4.1, printed p. 8 (PDF p. 10): "priors Λ₀, Λ₁ on states on C^j".

`IsStatePrior Λ` says that `Λ` is a probability measure on `ι × ι` complex matrices that is
carried by density matrices: `Λ`-almost every `τ` is a state.

**Formalization Note.** The σ-algebra on matrices is `instMeasurableSpaceMatrix` (entrywise
Borel). -/
def IsStatePrior {ι : Type*} [Fintype ι] (Λ : Measure (Matrix ι ι ℂ)) : Prop :=
  IsProbabilityMeasure Λ ∧ ∀ᵐ τ ∂Λ, QAlgorithms.IsDensityMatrix τ

end KnownFidelity.Rank


