-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:19.925942+00:00
-- url     : https://prove2.me/theorems/dbb30d9c-cbf0-44a5-bca7-5a11c508c7ff
-- title:
--   Averaged Vector Choices
-- statement:
--   Definitions and structural lemmas for Averaged Vector Choices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedVectorChoices.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace PositiveSemidefiniteClosure
end PositiveSemidefiniteClosure
end Formalism.FourierDecayAlt.P


