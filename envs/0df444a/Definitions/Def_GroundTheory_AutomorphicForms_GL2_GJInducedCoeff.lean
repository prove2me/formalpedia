-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJInducedCoeff
-- name    : GroundTheory_AutomorphicForms_GL2_GJInducedCoeff
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:53.922187+00:00
-- url     : https://prove2.me/theorems/ef7dfe18-1071-5a27-8c3f-bcc8ab1de975
-- title:
--   GJInduced Coeff
-- statement:
--   Definitions and structural lemmas for GJInduced Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJInducedCoeff.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
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
open Matrix GLnLocal Parabolic Iwasawa MeasureTheory
section Extension
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {U : Type*} [AddCommGroup U] [Module ℂ U] {τ : Representation ℂ G U}
end Extension
section Decomposition
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
end Decomposition
section Integral
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
end Integral
end GodementJacquet
end GroundTheory.Automorphic


