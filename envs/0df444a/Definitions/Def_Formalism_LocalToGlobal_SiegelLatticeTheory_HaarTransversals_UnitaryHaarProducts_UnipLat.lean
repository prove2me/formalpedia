-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipLat
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:29:33.34253+00:00
-- url     : https://prove2.me/theorems/860b53f9-8b45-4270-8b9c-94a064c5a433
-- title:
--   Unip Lat
-- statement:
--   Definitions and structural lemmas for Unip Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/UnipLat.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace Formalism.L2.SG.Pf.UnipLat
def OEApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
    ∀ φ : InfinitePlace F → (E →+* ℂ), (∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) →
    ∃ R : ℝ, ∀ t : InfinitePlace F → ℂ, ∃ y : 𝓞 E, ∀ v, ‖t v - φ v (y : E)‖ ≤ R
end Formalism.L2.SG.Pf.UnipLat


