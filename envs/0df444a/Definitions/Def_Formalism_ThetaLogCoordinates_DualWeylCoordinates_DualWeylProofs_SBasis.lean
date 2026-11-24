-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SBasis
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SBasis
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:01.4+00:00
-- url     : https://prove2.me/theorems/25aa74bc-985d-478e-b362-f86cb47b0a34
-- title:
--   SBasis
-- statement:
--   Definitions and structural lemmas for SBasis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SBasis.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
end Formalism.InvariantFactorPaths.ColumnFamilies


