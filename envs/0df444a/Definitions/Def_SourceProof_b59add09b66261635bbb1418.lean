-- Prove2me | Definitions.Def_SourceProof_b59add09b66261635bbb1418
-- name    : SourceProof_b59add09b66261635bbb1418
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:27:16.863111+00:00
-- url     : https://prove2.me/theorems/d3da8ffd-5b0c-4121-bb7b-332259c9e052
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.tendsto_condExpL2_of_antitone
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CondExpInf_F000
import Definitions.Def_SourceProof_379d0a4d323e31b94e61b375

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

variable {m : ℕ → MeasurableSpace Ω} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}


theorem _root_.Prove2MeSourceProof.h_b59add09b66261635bbb1418 (hanti : Antitone m) (hle : ∀ n, m n ≤ m₀)
    (hle_inf : (⨅ n, m n) ≤ m₀) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => ((condExpL2 ℝ ℝ (hle n) f : Lp ℝ 2 μ))) atTop
      (𝓝 ((condExpL2 ℝ ℝ hle_inf f : Lp ℝ 2 μ))) := by
  haveI hfn : ∀ n, Fact (m n ≤ m₀) := fun n => ⟨hle n⟩
  haveI hfi : Fact ((⨅ n, m n) ≤ m₀) := ⟨hle_inf⟩
  set V : ℕ → Submodule ℝ (Lp ℝ 2 μ) := fun n => lpMeas ℝ ℝ (m n) 2 μ with hVdef
  have hViInf : ⨅ n, V n = lpMeas ℝ ℝ (⨅ n, m n) 2 μ := LevyStochCalc.Probability.lpMeas_iInf_of_antitone hanti
  haveI hVc : ∀ n, CompleteSpace (V n) := fun n => inferInstanceAs (CompleteSpace (lpMeas ..))
  haveI : (⨅ n, V n).HasOrthogonalProjection := by rw [hViInf]; infer_instance
  have hclosed : ∀ n, IsClosed ((V n : Set (Lp ℝ 2 μ))) :=
    fun n => (completeSpace_coe_iff_isComplete.1 (hVc n)).isClosed
  have key := _root_.Prove2MeSourceProof.h_379d0a4d323e31b94e61b375 (LevyStochCalc.Probability.antitone_lpMeas (m₀ := m₀) hanti) hclosed f
  have heq : (lpMeas ℝ ℝ (⨅ n, m n) 2 μ).starProjection f = (⨅ n, V n).starProjection f := by
    refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
    · exact hViInf ▸ (⨅ n, V n).starProjection_apply_mem f
    · exact hViInf ▸ (⨅ n, V n).sub_starProjection_mem_orthogonal f
  change Tendsto (fun n => (lpMeas ℝ ℝ (m n) 2 μ).starProjection f) atTop
    (𝓝 ((lpMeas ℝ ℝ (⨅ n, m n) 2 μ).starProjection f))
  rw [heq]
  exact key
end LevyStochCalc.Probability


