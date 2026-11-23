-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_KinstSecondCountable
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_KinstSecondCountable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:16:55.107796+00:00
-- url     : https://prove2.me/theorems/4b0e1196-9bfb-4888-89eb-885ae9514cfa
-- title:
--   Kinst Second Countable
-- statement:
--   Definitions and structural lemmas for Kinst Second Countable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/KinstSecondCountable.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
instance kinst_compact (ε : Fin n → Bool) : CompactSpace (KG ε) := compactSpace_KG ε
instance kinst_secondCountable (ε : Fin n → Bool) : SecondCountableTopology (KG ε) :=
  Topology.IsInducing.subtypeVal.secondCountableTopology
end ReciprocityTheory.ChartRestriction.DS


