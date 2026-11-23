-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:58.265439+00:00
-- url     : https://prove2.me/theorems/67c508bc-eac9-43c6-abad-54da3c90b4b8
-- title:
--   CBinet
-- statement:
--   Definitions and structural lemmas for CBinet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/CBinet.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Lemmata_GeneralBFact_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
def cbPar {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding
end ReciprocityTheory.ChartRestriction.DS.S7


