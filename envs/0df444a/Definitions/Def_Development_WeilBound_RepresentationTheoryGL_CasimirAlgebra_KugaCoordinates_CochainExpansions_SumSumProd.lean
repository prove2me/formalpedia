-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CochainExpansions_SumSumProd
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CochainExpansions_SumSumProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:05.659202+00:00
-- url     : https://prove2.me/theorems/6ac187ff-9641-4268-a4eb-c416fc60217a
-- title:
--   Sum Sum Prod
-- statement:
--   Definitions and structural lemmas for Sum Sum Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CochainExpansions/SumSumProd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
namespace PositivityTheory.Rg.Cz.Coch
variable {H V : Type*} [AddCommGroup V] [Module ℂ V]
def cEv {N : ℕ} (F : (Fin N → H) → V) (A B : Fin N → H) : V :=
  ∑ S : Fin N → Bool, (∏ k, if S k then (1 : ℂ) else -I) • F (fun k => if S k then A k else B k)
end PositivityTheory.Rg.Cz.Coch
end


