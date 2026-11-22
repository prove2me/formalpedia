-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:29:56.478712+00:00
-- url     : https://prove2.me/theorems/1ce0ad3d-3c2d-4104-9bae-db887d423e60
-- title:
--   Hessian Scaling Integrals
-- statement:
--   Definitions and structural lemmas for Hessian Scaling Integrals, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HessianScalingIntegrals.lean

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
namespace Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]
end Formalism.FourierDecayAlt.P.HessianScalingIntegrals


