-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
-- name    : GroundTheory_AutomorphicForms_AdmissibleInduction
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:14.067641+00:00
-- url     : https://prove2.me/theorems/3928a9e1-f092-478a-bb1a-d98b126f6692
-- title:
--   Admissible Induction
-- statement:
--   Definitions and structural lemmas for Admissible Induction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
section General
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {ρ' : Representation ℂ G V'}
end General
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
section Permute
variable (F) in

def permuteGL (s : Equiv.Perm (Fin n)) : GL (Fin n) F ≃* GL (Fin n) F :=
  Units.mapEquiv (reindexAlgEquiv F F s).toMulEquiv
end Permute
section Admissible
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
end Admissible
end Parabolic
end GroundTheory.Automorphic


