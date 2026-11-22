-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:55.12951+00:00
-- url     : https://prove2.me/theorems/0b6d3fb9-8612-440f-a2f5-b511c2ddc3f7
-- title:
--   Frame Level Indices
-- statement:
--   Definitions and structural lemmas for Frame Level Indices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.FrameLevelIndices
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_one)
open Formalism.FourierDecayAlt.S3
section Index
variable {A : Type} [CommRing A] {r k : ℕ}
end Index
section Local
variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}
end Local
noncomputable def fac (q x : ℕ) : ℝ := 1 - ((q : ℝ) ^ (x + 1))⁻¹
section Om
variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}
end Om
end Formalism.FourierDecayAlt.P.FrameLevelIndices
namespace Formalism.FourierDecayAlt.P
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.FrameLevelIndices
end Formalism.FourierDecayAlt.P


