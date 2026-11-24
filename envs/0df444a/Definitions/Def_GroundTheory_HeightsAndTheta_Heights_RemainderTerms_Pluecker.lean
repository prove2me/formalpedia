-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Pluecker
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Pluecker
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:02.185432+00:00
-- url     : https://prove2.me/theorems/ca8cdc45-6ba5-4701-834b-c0b7d9e68337
-- title:
--   Pluecker
-- statement:
--   Definitions and structural lemmas for Pluecker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Pluecker.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace RestTerms
open Matrix Finset
open scoped ComplexOrder
noncomputable section
namespace Elem
variable {R : Type*} [CommRing R] {κ : Type*}
def subsetCols {p : ℕ} (S : {s : Finset κ // s.card = p}) (i : Fin p) : κ :=
  ((S.1.equivFinOfCardEq S.2).symm i : κ)
end Elem
end
end RestTerms
end GroundTheory.Heights₂.Heights


