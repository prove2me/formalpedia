-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:19.271922+00:00
-- url     : https://prove2.me/theorems/c8de9340-c726-49c2-bf44-13564ab002a1
-- title:
--   Kc Pair
-- statement:
--   Definitions and structural lemmas for Kc Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/InertiaGaloisSymmetry/KcPair.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HC.Der
section
open Ideal UniqueFactorizationMonoid
end
open NumberField Ideal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
end Formalism.HC.Der


