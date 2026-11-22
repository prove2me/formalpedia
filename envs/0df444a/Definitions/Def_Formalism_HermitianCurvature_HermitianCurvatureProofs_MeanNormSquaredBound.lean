-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:22.538863+00:00
-- url     : https://prove2.me/theorems/035b589b-6998-4b66-a2b3-e9cfa1e3c698
-- title:
--   Mean Norm Squared Bound
-- statement:
--   Definitions and structural lemmas for Mean Norm Squared Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanNormSquaredBound.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace MeanNormSquaredBound
section Abstract
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
end Abstract
end MeanNormSquaredBound
end Formalism.FourierDecayAlt.P


