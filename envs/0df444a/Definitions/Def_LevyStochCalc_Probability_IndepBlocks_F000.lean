-- Prove2me | Definitions.Def_LevyStochCalc_Probability_IndepBlocks_F000
-- name    : LevyStochCalc_Probability_IndepBlocks_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:34:56.078571+00:00
-- url     : https://prove2.me/theorems/de0aedb9-5a12-4731-9d39-6ea458aec202
-- title:
--   Source declarations: LevyStochCalc.Probability.IndepBlocks
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.IndepBlocks. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_7a7d131bbe1cd4c4e9ef0ba0
import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Independence of two joins from blockwise independence

An independent family of σ-algebras, each containing two independent sub-σ-algebras, has the two
joins of those sub-σ-algebras independent: a finite intersection from each join is a single
intersection over the union of the two index sets, which the family's independence factors
blockwise and the blockwise independence factors again.
-/

open MeasureTheory MeasurableSpace ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω ι : Type*} [DecidableEq ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [DecidableEq ι] in
/-- **Independence of two joins from blockwise independence.** -/
theorem indep_iSup_of_indep_blocks {m a b : ι → MeasurableSpace Ω}
    (ha : ∀ i, a i ≤ m i) (hb : ∀ i, b i ≤ m i) (hle : ∀ i, m i ≤ mΩ)
    (hm : iIndep m μ) (hab : ∀ i, Indep (a i) (b i) μ) :
    Indep (⨆ i, a i) (⨆ i, b i) μ := by
  have hgen : ∀ c : ι → MeasurableSpace Ω, (⨆ i, c i)
      = generateFrom (piiUnionInter (fun i => {t | MeasurableSet[c i] t}) Set.univ) := by
    intro c
    rw [generateFrom_piiUnionInter_measurableSet c Set.univ]
    simp
  exact IndepSets.indep (iSup_le fun i => (ha i).trans (hle i))
    (iSup_le fun i => (hb i).trans (hle i))
    (isPiSystem_piiUnionInter _ (fun i => @isPiSystem_measurableSet Ω (a i)) _)
    (isPiSystem_piiUnionInter _ (fun i => @isPiSystem_measurableSet Ω (b i)) _)
    (hgen a) (hgen b) (_root_.Prove2MeSourceProof.h_7a7d131bbe1cd4c4e9ef0ba0 ha hb hm hab)
end LevyStochCalc.Probability


