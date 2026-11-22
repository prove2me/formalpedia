-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:34.247373+00:00
-- url     : https://prove2.me/theorems/6b7180e4-f06b-4009-9af8-f74a561184c2
-- title:
--   Modulus Locally Constant
-- statement:
--   Definitions and structural lemmas for Modulus Locally Constant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
namespace Formalism.FourierDecayAlt.P
namespace A6x4
section Alg
variable {K : Type} [CommRing K]
end Alg
section Top
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
end Top
section Top2
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
end Top2
end A6x4
open A6x4
end Formalism.FourierDecayAlt.P


