-- Prove2me | Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
-- name    : GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:59.346697+00:00
-- url     : https://prove2.me/theorems/9031f0fd-00d7-4481-b9a3-4627e592ea4f
-- title:
--   Tilt Countable Neighbourhoods
-- statement:
--   Definitions and structural lemmas for Tilt Countable Neighbourhoods, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PowerSubgroups/CountableNeighbourhoods/TiltCountableNeighbourhoods.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Variant₂.N1
open GroundTheory.PAdicHodge
section
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact ¬IsUnit (p : (normInteger K))] [IsAdicComplete (Ideal.span {(p : (normInteger K))}) (normInteger K)]
end
end GroundTheory.Variant₂.N1


