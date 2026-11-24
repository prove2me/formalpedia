-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
-- name    : Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T17:22:54.20552+00:00
-- url     : https://prove2.me/theorems/cb387d23-6d8e-4521-bbc0-958a8a843362
-- title:
--   Principal
-- statement:
--   Definitions and structural lemmas for Principal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end Principal
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Principal
section Invariance
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
end Invariance
end Principal
end Formalism.FrobeniusOrbits


