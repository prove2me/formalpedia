-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_Taylor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:40:35.865706+00:00
-- url     : https://prove2.me/theorems/953ed62c-002a-42ea-8edf-fe5d03e6e96f
-- title:
--   Taylor
-- statement:
--   Definitions and structural lemmas for Taylor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/Taylor.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_IteratedDerivOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Filter Topology
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Rep
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
end Rep
end ReciprocityTheory.ChartRestriction.DS


