-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeSummability
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:59:36.916294+00:00
-- url     : https://prove2.me/theorems/dd9b85d6-bf00-4836-b50a-e088de4496cc
-- title:
--   Lattice Summability
-- statement:
--   Definitions and structural lemmas for Lattice Summability, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeSummability.lean

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantIntegrals
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Finset Function
noncomputable section
namespace Formalism.FourierDecayAlt.P.LatticeSummability
open Formalism.FourierDecayAlt.crystallineComparison
end Formalism.FourierDecayAlt.P.LatticeSummability


