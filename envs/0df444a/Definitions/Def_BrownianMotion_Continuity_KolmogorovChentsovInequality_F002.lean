-- Prove2me | Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
-- name    : BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:38:51.648746+00:00
-- url     : https://prove2.me/theorems/3362c273-c65e-4de7-8572-c9a5a281fa30
-- title:
--   Source declarations: BrownianMotion.Continuity.KolmogorovChentsovInequality
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.KolmogorovChentsovInequality. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F000
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F001
import Definitions.Def_SourceProof_ade94c0fef305d69001e8022
import Definitions.Def_SourceProof_ed1669131e7bfacd70789378

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

theorem countable_kolmogorov_chentsov (hT : HasBoundedCoveringNumber U c d)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β)
    (T' : Set T) [hT' : Countable T'] (hT'U : T' ⊆ U) :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β U := by
  let K := (Set.Countable.finiteExhaustion hT')
  simp only [iSup_subtype, Subtype.edist_mk_mk, ← biSup_prod', ← (K.prod K).iUnion_eq,
    Set.mem_iUnion, iSup_exists, K.prod_apply, iSup_comm (ι' := ℕ)]
  simp only [biSup_prod]
  simp only [← iSup_subtype'']
  rw [MeasureTheory.lintegral_iSup', iSup_le_iff]
  · exact fun n ↦ _root_.Prove2MeSourceProof.h_ade94c0fef305d69001e8022 hT hX hd_pos hdq_lt hβ_pos (K n)
      ((K.subset n).trans hT'U)
  · intro n
    have h_ae s t := hX.aemeasurable_edist (s := s) (t := t)
    fun_prop
  · filter_upwards with ω
    intro _ _ h
    simp only [iSup_subtype, ← biSup_prod']
    exact iSup_le_iSup_of_subset (Set.prod_mono (K.mono h) (K.mono h))
lemma IsKolmogorovProcess.ae_iSup_rpow_edist_div_lt_top
    (hT : HasBoundedCoveringNumber U c d)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    {T' : Set T} (hT' : T'.Countable) (hT'U : T' ⊆ U) :
    ∀ᵐ ω ∂P, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) < ∞ := by
  have : Countable T' := hT'
  have h_diam : Metric.ediam U < ∞ := hT.ediam_lt_top
  refine ae_lt_top' ?_ ((countable_kolmogorov_chentsov hT hX.IsAEKolmogorovProcess hd_pos
    hdq_lt hβ_pos T' hT'U).trans_lt ?_).ne
  · refine AEMeasurable.iSup (fun s ↦ AEMeasurable.iSup (fun t ↦ ?_))
    exact AEMeasurable.div (hX.measurable_edist.aemeasurable.pow_const _) (by fun_prop)
  · exact ENNReal.mul_lt_top (by simp) (_root_.Prove2MeSourceProof.h_ed1669131e7bfacd70789378 h_diam hc hd_pos hX.p_pos hdq_lt hβ_lt)
end PseudoEMetricSpace

end ProbabilityTheory


