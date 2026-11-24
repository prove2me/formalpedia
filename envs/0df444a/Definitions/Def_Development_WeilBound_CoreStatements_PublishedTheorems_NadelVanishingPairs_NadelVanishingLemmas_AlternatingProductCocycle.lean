-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:48.377246+00:00
-- url     : https://prove2.me/theorems/3e7487cd-3b4c-424e-80f4-f0fa6bb673ec
-- title:
--   Alternating Product Cocycle
-- statement:
--   Definitions and structural lemmas for Alternating Product Cocycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/AlternatingProductCocycle.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI.AltClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
theorem dtot_add {E : Type} [AddCommGroup E] (d : E →+ E) (c c' : Finset ι → E) :
    Dtot d (c + c') = Dtot d c + Dtot d c' := by
  funext t
  simp only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add]
  abel
def dtotHom {E : Type} [AddCommGroup E] (d : E →+ E) : (Finset ι → E) →+ (Finset ι → E) :=
  AddMonoidHom.mk' (Dtot d) (dtot_add d)
end GlobalTheory.DI.AltClosed


