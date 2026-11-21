-- Prove2me | Definitions.Def_RiemannMasullo_TorsionSector
-- name    : RiemannMasullo_TorsionSector
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T00:33:35.523733+00:00
-- url     : https://prove2.me/theorems/bdb788ab-05e3-4287-a893-28a14d2d4437
-- title:
--   A half-open sector for the action of torsion units
-- statement:
--   At a chosen infinite place the argument of an embedded unit must lie in the half-open interval from zero to two pi divided by the number of torsion units.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L241-L246

import Mathlib
namespace RiemannMasullo
open NumberField InfinitePlace.Completion
variable (F : Type*) [Field F] [NumberField F]
variable (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
def inTorsionSector (x : v₀.Completionˣ) : Prop :=
  (σ (extensionEmbedding v₀ x.val)).arg ∈ Set.Ico 0 (2 * Real.pi / Units.torsionOrder F)
end RiemannMasullo


