-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:35.924877+00:00
-- url     : https://prove2.me/theorems/149e4615-7b41-4d7e-9417-1f95e1ed0ba8
-- title:
--   Eq Zero Of Ideal Compact
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Ideal Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
namespace Formalism.FourierDecayAlt.P.A6x5
section Top
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ψ : AddChar K ℂ}
def unitBox (R : Subring K) (ϖ : Kˣ) (j : ℕ) : Set K :=
  {z | ∃ y, z * y = 1 ∧ (ϖ : K) ^ j * z ∈ R ∧ (ϖ : K) ^ j * y ∈ R}
end Top
end Formalism.FourierDecayAlt.P.A6x5
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x5
end Formalism.FourierDecayAlt.P


