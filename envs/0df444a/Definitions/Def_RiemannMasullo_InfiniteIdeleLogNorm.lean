-- Prove2me | Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
-- name    : RiemannMasullo_InfiniteIdeleLogNorm
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-21T00:14:33.923918+00:00
-- url     : https://prove2.me/theorems/974c96a7-f5eb-452a-ba5a-16eb28a7b704
-- title:
--   The norm and logarithm on the archimedean idele group
-- statement:
--   The norm multiplies the local moduli raised to their place multiplicities. The full logarithm records the logarithm of each local modulus with the same multiplicity.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L43-L70

import Mathlib
noncomputable section
namespace RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ

def infiniteIdeleNorm : 𝕀∞ →* ℝ≥0ˣ :=
  ∏ v : InfinitePlace F, ((Units.map nnnormHom.toMonoidHom).comp
    (Units.map (Pi.evalRingHom _ v).toMonoidHom)) ^ v.mult

def infiniteIdeleLog (g : 𝕀∞) (v : InfinitePlace F) : ℝ :=
  v.mult * Real.log ‖g.val v‖
end RiemannMasullo


