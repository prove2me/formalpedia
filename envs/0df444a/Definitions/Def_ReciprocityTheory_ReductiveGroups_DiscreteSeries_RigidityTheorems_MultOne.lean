-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:48.410957+00:00
-- url     : https://prove2.me/theorems/389da9ed-0112-40fb-9bd0-ea5cae71c193
-- title:
--   Mult One
-- statement:
--   Definitions and structural lemmas for Mult One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/RigidityTheorems/MultOne.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_RigidOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def closGen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) : Submodule ℂ H :=
  ((genSub E V).map D.subtype).topologicalClosure
end ReciprocityTheory.ChartRestriction.DS


