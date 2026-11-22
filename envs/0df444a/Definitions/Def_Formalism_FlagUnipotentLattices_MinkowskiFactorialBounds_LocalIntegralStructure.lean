-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:55:28.56052+00:00
-- url     : https://prove2.me/theorems/58843024-bb06-48c4-b9f8-2414417fc3f7
-- title:
--   Local Integral Structure
-- statement:
--   Definitions and structural lemmas for Local Integral Structure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LocalIntegralStructure.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
section GramAll
open Matrix Polynomial
section Gram
variable {R : Type} [CommRing R]
end Gram
end GramAll
section NF
variable {E : Type} [Field E] [NumberField E]
end NF
end Formalism.HermitianLatticeCounting.P


