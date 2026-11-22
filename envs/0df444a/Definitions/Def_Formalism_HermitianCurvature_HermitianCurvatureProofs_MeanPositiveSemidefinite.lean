-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:29:48.526259+00:00
-- url     : https://prove2.me/theorems/6c674d92-79ab-479e-9f4a-b267c96fc1ff
-- title:
--   Mean Positive Semidefinite
-- statement:
--   Definitions and structural lemmas for Mean Positive Semidefinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanPositiveSemidefinite.lean

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
namespace Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite
section PSD
variable {X : Type}
end PSD
end Formalism.FourierDecayAlt.P.MeanPositiveSemidefinite


