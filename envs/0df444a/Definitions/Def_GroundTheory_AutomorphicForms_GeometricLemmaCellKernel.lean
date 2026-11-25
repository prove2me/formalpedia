-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:57:50.172239+00:00
-- url     : https://prove2.me/theorems/b8fe2b49-33f4-54bd-9610-1c54e2b72c27
-- title:
--   Geometric Lemma Cell Kernel
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Cell Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellKernel.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
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
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
section Vanishing
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
end Vanishing
section AvgConj
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
end AvgConj
section Kernel
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
end Kernel
end Parabolic
end GroundTheory.Automorphic


