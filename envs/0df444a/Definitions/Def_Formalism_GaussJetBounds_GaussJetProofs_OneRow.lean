-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
-- name    : Formalism_GaussJetBounds_GaussJetProofs_OneRow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:00:45.925279+00:00
-- url     : https://prove2.me/theorems/9ce15a40-10ca-4354-80a0-bcd62ca20c7e
-- title:
--   One Row
-- statement:
--   Definitions and structural lemmas for One Row, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneRow.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
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
universe u
namespace Formalism.DworkPowerSeriesWeights
open MvPolynomial
end Formalism.DworkPowerSeriesWeights


