-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CauchyBinet
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CauchyBinet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:59:44.00607+00:00
-- url     : https://prove2.me/theorems/c7ba6762-be2d-4c4f-bd14-cbe7dcdc7b11
-- title:
--   Cauchy Binet
-- statement:
--   Definitions and structural lemmas for Cauchy Binet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/CauchyBinet.lean

import Mathlib
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
open Finset Matrix MeasureTheory
open scoped InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS
def cauchyBinetPar {i N : ℕ} (p : (Σ _ : {S : Finset (Fin N) // S.card = i}, Equiv.Perm (Fin i))) :
    Fin i ↪ Fin N :=
  p.2.toEmbedding.trans (p.1.1.orderEmbOfFin p.1.2).toEmbedding
end ReciprocityTheory.ChartRestriction.DS


