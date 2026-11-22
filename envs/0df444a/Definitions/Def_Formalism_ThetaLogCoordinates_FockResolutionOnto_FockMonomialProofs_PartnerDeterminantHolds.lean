-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_PartnerDeterminantHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:40.472845+00:00
-- url     : https://prove2.me/theorems/9a75ad04-1668-4a75-8fb5-acbacaffe717
-- title:
--   Partner Determinant Holds
-- statement:
--   Definitions and structural lemmas for Partner Determinant Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/PartnerDeterminantHolds.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementA
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SmithZp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M MvPolynomial Finset
section Gr
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]
end Gr
end Formalism.InvariantFactorPaths.L4


