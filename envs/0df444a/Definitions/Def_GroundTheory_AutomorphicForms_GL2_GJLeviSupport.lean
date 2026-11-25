-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLeviSupport
-- name    : GroundTheory_AutomorphicForms_GL2_GJLeviSupport
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:01:02.575423+00:00
-- url     : https://prove2.me/theorems/26ba7333-c33d-4fa8-bc42-2316db27cc43
-- title:
--   GJLevi Support
-- statement:
--   Definitions and structural lemmas for GJLevi Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLeviSupport.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace GodementJacquet
open Matrix GLnLocal Parabolic ValuativeRel
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
end GodementJacquet
end GroundTheory.Automorphic


