-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:25:15.84084+00:00
-- url     : https://prove2.me/theorems/ecd1c2e9-fa23-4d04-931b-ee3344672533
-- title:
--   Pa Th Continuous
-- statement:
--   Definitions and structural lemmas for Pa Th Continuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaThContinuous.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_DetMEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
def thF (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) : ℂ :=
  paTh Y q F v * (starRingEnd ℂ) (F v) * (paW q v : ℂ)
instance lat_vaddInv (Y : GT ι) :
    VAddInvariantMeasure (lat Y.b) (EuclideanSpace ℂ ι) volume :=
  ⟨fun g s _ => by
    simp only [Submodule.vadd_def, vadd_eq_add]
    exact measure_preimage_add volume (g : EuclideanSpace ℂ ι) s⟩
end
end ReciprocityTheory.ChartRestriction.G.I2.FPw


