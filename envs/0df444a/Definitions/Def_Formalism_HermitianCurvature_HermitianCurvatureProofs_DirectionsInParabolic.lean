-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:28:17.508022+00:00
-- url     : https://prove2.me/theorems/c1f82e8a-83bb-4e0f-8f97-0ff463a922fd
-- title:
--   Directions In Parabolic
-- statement:
--   Definitions and structural lemmas for Directions In Parabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.Ux4
section blocks
variable {k j ρ : ℕ}
end blocks
section rad
variable {k j ρ : ℕ}
noncomputable def RnInv (x : RC k j ρ) : B.Mat k (j + ρ) :=
  blk3 1 (G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ)
    (-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ) * Matrix.of x.1 -
      G.wMat j * ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2))
    0 1 (-(Matrix.of x.1)) 0 0 1
end rad
end Formalism.FourierDecayAlt.P.Ux4
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Ux4
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.Ux4
section lie
variable {k j ρ : ℕ}
end lie
end Formalism.FourierDecayAlt.P.Ux4
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Ux4
end Formalism.FourierDecayAlt.P


