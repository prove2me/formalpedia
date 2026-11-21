-- Prove2me | Definitions.Def_RiemannMasullo_WeilQuotient
-- name    : RiemannMasullo_WeilQuotient
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T01:12:26.648171+00:00
-- url     : https://prove2.me/theorems/db40c7a8-8904-4968-b996-0c0158a0287a
-- title:
--   Coset integration and Weil quotient measures
-- statement:
--   Integrate a test function over a coset with subgroup Haar measure. A Weil quotient measure is the regular Haar measure on the quotient normalized by the resulting integral formula.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L151-L171

import Mathlib
noncomputable section
namespace RiemannMasullo
open MeasureTheory Set
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G)
local instance : MeasurableSpace (G ⧸ H) := borel _

def lcaCosetIntegral (μH : Measure H) (f : G → ℂ) (q : G ⧸ H) : ℂ :=
  ∫ h : H, f (q.out * (h : G)) ∂μH

def IsWeilQuotientMeasure (μ : Measure G) (μH : Measure H) (ν : Measure (G ⧸ H)) : Prop :=
  ν.IsHaarMeasure ∧ ν.Regular ∧
    ∀ f : C(G, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν

end RiemannMasullo


