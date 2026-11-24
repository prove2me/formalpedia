-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
-- name    : Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:08.201795+00:00
-- url     : https://prove2.me/theorems/0f6d69ec-bd81-427d-8b8d-8642fc20d62d
-- title:
--   Operator Hilbert Schmidt Norm
-- statement:
--   Definitions and structural lemmas for Operator Hilbert Schmidt Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/OperatorHilbertSchmidtNorm.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
namespace Formalism.HermitianLatticeCounting.P
end Formalism.HermitianLatticeCounting.P


