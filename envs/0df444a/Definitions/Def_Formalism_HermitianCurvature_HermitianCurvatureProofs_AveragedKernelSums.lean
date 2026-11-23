-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:28.00011+00:00
-- url     : https://prove2.me/theorems/af28cf08-4b39-4098-ab35-0a0d88e39927
-- title:
--   Averaged Kernel Sums
-- statement:
--   Definitions and structural lemmas for Averaged Kernel Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragedKernelSums.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
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
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
section Basic
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
end Basic
section Sum
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
end Sum
section Parseval
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
end Parseval
end AveragedKernelSums
open AveragedKernelSums
end Formalism.FourierDecayAlt.P


