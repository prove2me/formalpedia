-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:21.236941+00:00
-- url     : https://prove2.me/theorems/934f7bfb-1914-4b3e-84b2-436575d8f790
-- title:
--   Irreducible Smooth Admissible GL
-- statement:
--   Definitions and structural lemmas for Irreducible Smooth Admissible GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IrreducibleSmoothAdmissibleGL.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
namespace GlobalTheory.CompanionTheory.SmGLBridge
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
def glReindex {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    GL a k ≃* GL b k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k e).toMulEquiv
end GlobalTheory.CompanionTheory.SmGLBridge
namespace GlobalTheory.CompanionTheory.SmGLBridge
end GlobalTheory.CompanionTheory.SmGLBridge


