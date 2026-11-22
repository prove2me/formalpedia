-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:58:51.192869+00:00
-- url     : https://prove2.me/theorems/0a2b06af-721c-4f14-aa0f-1db201603ddc
-- title:
--   Block Estimates Sum Form
-- statement:
--   Definitions and structural lemmas for Block Estimates Sum Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity
open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB
variable {E W : Type} [Field E] (D : Data E W)
end Formalism.FourierDecayAlt.P.BaseGramNonnegativity


