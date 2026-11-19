-- Prove2me | Definitions.Def_LevyStochCalc_Probability_CondExpInf_F000
-- name    : LevyStochCalc_Probability_CondExpInf_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:40:10.491398+00:00
-- url     : https://prove2.me/theorems/44708113-5dc1-4953-9a79-46576a17cb34
-- title:
--   Source declarations: LevyStochCalc.Probability.CondExpInf
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.CondExpInf. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ProjectionLimit_F000
import Definitions.Def_SourceProof_e0ac148a71832ad384c26210
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# `L²` conditional expectations along a decreasing sequence of σ-algebras

For an antitone sequence of sub-σ-algebras the subspaces `lpMeas (m n)` of `L²` are antitone with
intersection `lpMeas (⨅ n, m n)` (`lpMeas_iInf_of_antitone`, over the `limsup` construction of
`LevyStochCalc.Probability.AEMeasurableInf`), and `condExpL2` is the orthogonal projection onto
them. Projections along an antitone chain of closed subspaces converge to the projection onto the
intersection (`LevyStochCalc.Probability.ProjectionLimit`), so

  `𝔼[f | m n] → 𝔼[f | ⨅ n, m n]` in `L²`.

This is a downward, `L²` counterpart of Lévy's upward theorem
`MeasureTheory.tendsto_eLpNorm_condExp`, the `L¹` convergence along an increasing filtration.
Applied at `m n := ℱ (t + 1/(n+1))` for a right-continuous filtration it gives the
right-`L²`-continuity of `t ↦ 𝔼[ξ | ℱ t]` that the càdlàg regularisation of cited result #13b
needs.

## Main statements

* `lpMeas_iInf_of_antitone` — `⨅ n, lpMeas (m n) = lpMeas (⨅ n, m n)`.
* `tendsto_condExpL2_of_antitone` — the `L²` conditional expectations converge.
-/

open MeasureTheory Filter Topology
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*}

/-- `lpMeas` is monotone in the σ-algebra. -/
theorem lpMeas_mono {m m' m₀ : MeasurableSpace Ω} {μ : Measure Ω} (h : m ≤ m') :
    lpMeas ℝ ℝ m 2 μ ≤ lpMeas ℝ ℝ m' 2 μ := by
  intro f hf
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  obtain ⟨g, hg, hfg⟩ := hf
  exact ⟨g, hg.mono h, hfg⟩
variable {m : ℕ → MeasurableSpace Ω} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The `lpMeas` subspaces of an antitone sequence are antitone. -/
theorem antitone_lpMeas (hanti : Antitone m) :
    Antitone fun n => lpMeas ℝ ℝ (m n) 2 μ := fun _ _ hab => lpMeas_mono (m₀ := m₀) (hanti hab)
/-- **The intersection of the `lpMeas` subspaces of an antitone sequence is the `lpMeas` subspace
of the infimum.** -/
theorem lpMeas_iInf_of_antitone (hanti : Antitone m) :
    ⨅ n, lpMeas ℝ ℝ (m n) 2 μ = lpMeas ℝ ℝ (⨅ n, m n) 2 μ := by
  refine le_antisymm (fun f hf => ?_)
    (le_iInf fun n => lpMeas_mono (m₀ := m₀) (iInf_le m n))
  rw [Submodule.mem_iInf] at hf
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  exact _root_.Prove2MeSourceProof.h_e0ac148a71832ad384c26210 hanti fun n =>
    mem_lpMeas_iff_aestronglyMeasurable.1 (hf n)
end LevyStochCalc.Probability


