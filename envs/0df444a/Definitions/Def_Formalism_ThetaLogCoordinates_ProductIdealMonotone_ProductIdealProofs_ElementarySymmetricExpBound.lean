-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_ElementarySymmetricExpBound
-- name    : Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_ElementarySymmetricExpBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:24.806238+00:00
-- url     : https://prove2.me/theorems/0c19a866-9676-44c1-ba5f-5f24a4b18a68
-- title:
--   Elementary Symmetric Exp Bound
-- statement:
--   Definitions and structural lemmas for Elementary Symmetric Exp Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ProductIdealMonotone/ProductIdealProofs/ElementarySymmetricExpBound.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
namespace Formalism.InvariantFactorPaths.G0
open Formalism.G0
end Formalism.InvariantFactorPaths.G0


