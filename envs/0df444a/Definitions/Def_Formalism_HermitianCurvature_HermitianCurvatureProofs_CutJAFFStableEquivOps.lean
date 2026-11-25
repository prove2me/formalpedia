-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableEquivOps
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableEquivOps
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:08.607952+00:00
-- url     : https://prove2.me/theorems/98fb8474-a040-5ddf-9f42-7a4c23f93f5d
-- title:
--   Cut JAFFStable Equiv Ops
-- statement:
--   Definitions and structural lemmas for Cut JAFFStable Equiv Ops, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableEquivOps.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
open Formalism.QuantumDeterminants.WeylGroupFacts
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
section aux
variable {k r : ℕ}
def pOf (a b c d : B.Mat k r) : B.SS k r :=
  ((Matrix.of.symm a, Matrix.of.symm b), (Matrix.of.symm c, Matrix.of.symm d))
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
end aux
end
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS


