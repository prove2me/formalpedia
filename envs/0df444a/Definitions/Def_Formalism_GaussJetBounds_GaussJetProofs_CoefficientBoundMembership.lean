-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
-- name    : Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:45.677703+00:00
-- url     : https://prove2.me/theorems/39872648-21a6-4d99-83fc-cf254b2e96f9
-- title:
--   Coefficient Bound Membership
-- statement:
--   Definitions and structural lemmas for Coefficient Bound Membership, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/CoefficientBoundMembership.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.DworkPowerSeriesWeights
open MvPolynomial Formalism.IncomingBounds
end Formalism.DworkPowerSeriesWeights


