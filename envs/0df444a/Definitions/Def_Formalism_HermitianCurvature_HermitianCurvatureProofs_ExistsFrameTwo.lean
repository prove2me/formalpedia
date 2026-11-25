-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:55:44.446351+00:00
-- url     : https://prove2.me/theorems/b3929ed0-d89b-533b-9b28-18f10797406b
-- title:
--   Exists Frame Two
-- statement:
--   Definitions and structural lemmas for Exists Frame Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ExistsFrameTwo.lean

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace SkewHermitianParts
section Closed
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
end Closed
section Geometry
open AnisotropicColumnSums
variable {k r : ℕ}
end Geometry
section Rep
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
end Rep
end SkewHermitianParts
end Formalism.FourierDecayAlt.P


