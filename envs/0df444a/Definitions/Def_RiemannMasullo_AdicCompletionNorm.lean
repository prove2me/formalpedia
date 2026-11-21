-- Prove2me | Definitions.Def_RiemannMasullo_AdicCompletionNorm
-- name    : RiemannMasullo_AdicCompletionNorm
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T22:45:19.793404+00:00
-- url     : https://prove2.me/theorems/86c89b18-b8fc-49b3-82ae-fcacaf10bbda
-- title:
--   The residue-cardinality norm on a finite-place completion
-- statement:
--   Normalize the rank-one valuation on the completion by the cardinality of R/v, as in upstream Mathlib. This supplies its compatible normed-field metric under the finite-quotients hypothesis.
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean

import Mathlib

open IsDedekindDomain
open scoped WithZero NNReal

namespace RiemannMasullo.AdicCompletionNorm

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  [Field K] [Algebra R K] [IsFractionRing R K]

private theorem one_lt_cardQuot (v : HeightOneSpectrum R) : 1 < Submodule.cardQuot v.asIdeal := by
  haveI := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have hp : 0 < Submodule.cardQuot v.asIdeal := by
    rw [Submodule.cardQuot_apply]
    exact Nat.card_pos
  have hn : Submodule.cardQuot v.asIdeal ≠ 1 :=
    fun h ↦ v.isPrime.ne_top (Submodule.cardQuot_eq_one_iff.mp h)
  omega

noncomputable scoped instance (v : HeightOneSpectrum R) :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : ℝ≥0) < (Submodule.cardQuot v.asIdeal : ℝ≥0) by
    exact_mod_cast one_lt_cardQuot v)

noncomputable scoped instance (v : HeightOneSpectrum R) : NormedField (v.adicCompletion K) :=
  Valued.toNormedField _ ℤᵐ⁰

end RiemannMasullo.AdicCompletionNorm


