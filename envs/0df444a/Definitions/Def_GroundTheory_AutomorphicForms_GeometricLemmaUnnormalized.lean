-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaUnnormalized
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaUnnormalized
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:17:42.373548+00:00
-- url     : https://prove2.me/theorems/a300c353-4271-55b0-9e75-3fa6f57b7c90
-- title:
--   Geometric Lemma Unnormalized
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Unnormalized, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaUnnormalized.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaGraded
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
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
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
end Parabolic
end GroundTheory.Automorphic


