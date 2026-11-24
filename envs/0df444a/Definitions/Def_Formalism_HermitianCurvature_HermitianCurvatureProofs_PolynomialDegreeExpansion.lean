-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialDegreeExpansion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialDegreeExpansion
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:54.608211+00:00
-- url     : https://prove2.me/theorems/1473b014-b70c-4b9d-8ae9-e42285893fb0
-- title:
--   Polynomial Degree Expansion
-- statement:
--   Definitions and structural lemmas for Polynomial Degree Expansion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialDegreeExpansion.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.RealWeightedForms
open scoped Matrix
end Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion


