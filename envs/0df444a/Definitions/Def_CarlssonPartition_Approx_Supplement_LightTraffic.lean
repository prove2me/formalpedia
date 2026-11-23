-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_LightTraffic
-- name    : CarlssonPartition_Approx_Supplement_LightTraffic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:26:46.278746+00:00
-- url     : https://prove2.me/theorems/6e9ff4ee-17da-4638-b852-90cd1916d315
-- title:
--   §3.1 — nontrivial light-traffic filter and an explicit clustered renewal family
-- statement:
--   Let $\Lambda=(0,1/4)$ be a cofinal positive-rate neighborhood of zero. Light traffic on this domain is the inverse-image filter of $\lambda\to0^+$. A sorry-free instance proves this filter nontrivial. For the explicit Theorem 4 counterexample, set
--    $$
--    G_\lambda=\tfrac12\delta_{1/4}+\tfrac12\delta_{2/\lambda-1/4}\quad(0<\lambda<1).
--    $$
--    Both gaps are positive and the mean is $1/\lambda$. For rates at least one, extend the family by the deterministic gap $1/\lambda$. Thus every positive rate has a genuine renewal law, while the short-gap probability remains one half as the rate tends to zero. The law is a chosen counterexample inside the source domain, not a new premise imposed on all arrival families. The file also restricts the connected model's rate inputs to $\Lambda$.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §3.1 p. 7 (PDF 8); Theorem 4 p. 10 (PDF 11), proof pp. ec3–ec4 (PDF 40–41)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_Model
import Definitions.Def_CarlssonPartition_Approx_Supplement_AdmissiblePolicies

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory Filter
open scoped ENNReal

/-- A cofinal positive-rate neighborhood of zero. No claim about higher loads is
needed to disprove a light-traffic assertion. -/
abbrev LightRate := {lam : ℝ // lam ∈ Set.Ioo 0 (1 / 4 : ℝ)}

/-- Light traffic retains the source's λ→0 from above, on a cofinal neighborhood. -/
def lightTraffic : Filter LightRate :=
  Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))

/-- Restricting to this neighborhood does not create a bottom filter. -/
instance lightTraffic_neBot : NeBot lightTraffic := by
  change NeBot (Filter.comap (Subtype.val : LightRate → ℝ) _)
  apply Filter.NeBot.comap_of_range_mem
    (show NeBot (nhdsWithin (0 : ℝ) (Set.Ioi 0)) by infer_instance)
  have h : Set.Iio (1 / 4 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
  have hr : Set.range (Subtype.val : LightRate → ℝ) = Set.Ioo 0 (1 / 4 : ℝ) :=
    Subtype.range_coe
  rw [hr]
  exact inter_mem self_mem_nhdsWithin h

/-- General renewal gaps with a short-gap probability that does not vanish in light
traffic. For λ<1 the mean is (1/4 + (2/λ-1/4))/2 = 1/λ. Outside that neighborhood
use a deterministic positive gap, so the input family is defined at every positive rate.
This is an explicit counterexample family, NOT an extra assumption on the source. -/
def clusteredGapLaw (lam : ℝ) : Measure ℝ :=
  if lam < 1 then
    (1 / 2 : ℝ≥0∞) • Measure.dirac (1 / 4 : ℝ) +
      (1 / 2 : ℝ≥0∞) • Measure.dirac (2 / lam - 1 / 4)
  else Measure.dirac lam⁻¹

/-- Restriction of a source rate family to the cofinal light-traffic neighborhood. -/
def Model.InputFamily.atLight {M : Model} {Ω : Type*} [MeasurableSpace Ω]
    (A : M.InputFamily Ω) (lam : LightRate) : M.Input Ω :=
  A.input ⟨lam.val, lam.property.1⟩

end CarlssonPartition.Approx.Supplement


