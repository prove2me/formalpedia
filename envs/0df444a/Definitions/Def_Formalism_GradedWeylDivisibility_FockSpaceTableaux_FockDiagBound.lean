-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound
-- name    : Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:56:28.686581+00:00
-- url     : https://prove2.me/theorems/c0878a91-22d7-413b-988a-d3447b483641
-- title:
--   Fock Diag Bound
-- statement:
--   Definitions and structural lemmas for Fock Diag Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockDiagBound.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
namespace Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
end Formalism.GradedWeylDivisibility


