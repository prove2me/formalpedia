-- Prove2me | Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_SlopeVcCountableNeighbourhoods
-- name    : GroundTheory_PowerSubgroups_CountableNeighbourhoods_SlopeVcCountableNeighbourhoods
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:02.493447+00:00
-- url     : https://prove2.me/theorems/66078ed0-8482-4fcc-97df-bef80f42dd7b
-- title:
--   Slope Vc Countable Neighbourhoods
-- statement:
--   Definitions and structural lemmas for Slope Vc Countable Neighbourhoods, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/SlopeVcCountableNeighbourhoods.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Variant₂.N1
open WeierstrassCurve
def vcX {R : Type*} [CommRing R] (C : WeierstrassCurve.VariableChange R) (x : R) : R :=
  ↑C.u⁻¹ ^ 2 * (x - C.r)
def vcY {R : Type*} [CommRing R] (C : WeierstrassCurve.VariableChange R) (x y : R) : R :=
  ↑C.u⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)
end GroundTheory.Variant₂.N1


