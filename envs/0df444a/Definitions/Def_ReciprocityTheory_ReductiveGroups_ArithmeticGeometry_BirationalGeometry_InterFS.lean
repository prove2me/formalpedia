-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:50.121397+00:00
-- url     : https://prove2.me/theorems/9b70c7be-2c65-49f9-bd6d-6c0789dd82c7
-- title:
--   Inter FS
-- statement:
--   Definitions and structural lemmas for Inter FS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFS.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance instRealIPS : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
def affL (b : E) : (Fin 1 → ℂ) →L[ℝ] E :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight b
end ReciprocityTheory.ChartRestriction.G.Geo


