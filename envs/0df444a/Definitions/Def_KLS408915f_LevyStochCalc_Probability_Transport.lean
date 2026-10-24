-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Probability_Transport
-- name    : KLS408915f_LevyStochCalc_Probability_Transport
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:16:38.915025+00:00
-- url     : https://prove2.me/theorems/cd7e048a-d87a-420d-9948-f5c8462d7a59
-- title:
--   Transport of independence through measure-preserving maps
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. If h : α → β is measure preserving from μa to μb, and sub-σ-algebras m₁ and m₂ of β are independent under μb, then `indep_comap_of_measurePreserving` states that their comaps along h are independent under μa. The result explicitly requires m₁ ≤ mβ and m₂ ≤ mβ and concludes independence with respect to the original measurable structures and measures.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Probability/Transport.lean#L29-L44 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Probability.Transport`, definition bundle `KLS408915f_LevyStochCalc_Probability_Transport`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.Probability.Independence.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/Transport.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
namespace LevyStochCalc
namespace Probability
variable {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {μa : Measure α} {μb : Measure β} {h : α → β}
/-- Independence of two sub-σ-algebras of `β` transports to their comaps in `α`
along a measure-preserving map `h : α → β`. -/
theorem indep_comap_of_measurePreserving (hmp : MeasurePreserving h μa μb)
    {m₁ m₂ : MeasurableSpace β} (hm₁ : m₁ ≤ mβ) (hm₂ : m₂ ≤ mβ)
    (hindep : ProbabilityTheory.Indep m₁ m₂ μb) :
    ProbabilityTheory.Indep (m₁.comap h) (m₂.comap h) μa := by
  have h_aux : ∀ s : Set β, @MeasurableSet β mβ s → μa (h ⁻¹' s) = μb s := fun s hs =>
    @MeasurePreserving.measure_preimage α β mα mβ μa μb h hmp s
      (@MeasurableSet.nullMeasurableSet β mβ μb s hs)
  rw [ProbabilityTheory.Indep_iff]
  rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
  have hu' : @MeasurableSet β mβ u := hm₁ _ hu
  have hv' : @MeasurableSet β mβ v := hm₂ _ hv
  rw [show h ⁻¹' u ∩ h ⁻¹' v = h ⁻¹' (u ∩ v) from rfl,
    h_aux _ (@MeasurableSet.inter β mβ _ _ hu' hv'), h_aux _ hu', h_aux _ hv']
  exact (ProbabilityTheory.Indep_iff _ _ _).1 hindep u v hu hv
end Probability
end LevyStochCalc


