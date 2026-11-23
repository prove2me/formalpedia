-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalAnisotropicFrameBoundedCM
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_OrthogonalAnisotropicFrameBoundedCM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:36.016422+00:00
-- url     : https://prove2.me/theorems/575892c4-28a0-428e-a935-235e6d0324a0
-- title:
--   Orthogonal Anisotropic Frame Bounded CM
-- statement:
--   Definitions and structural lemmas for Orthogonal Anisotropic Frame Bounded CM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/OrthogonalAnisotropicFrameBoundedCM.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
namespace GlobalTheory.SmoothForms
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end GlobalTheory.SmoothForms


