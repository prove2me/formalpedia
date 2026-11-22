-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:50.948164+00:00
-- url     : https://prove2.me/theorems/54e20274-5a61-4cf6-98d3-752f87358ced
-- title:
--   Local Volume Positivity
-- statement:
--   Definitions and structural lemmas for Local Volume Positivity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalVolumePositivity.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3
namespace LocalVolumePositivity
variable {P : Type} [Fintype P] {B : MassData P}
end LocalVolumePositivity
open LocalVolumePositivity
end Formalism.FourierDecayAlt.P


