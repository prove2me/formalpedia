-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
-- name    : GroundTheory_AutomorphicForms_SupercuspidalCoefficients
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:45.238076+00:00
-- url     : https://prove2.me/theorems/9f41d696-780b-4bcb-a75d-554356b9ed99
-- title:
--   Supercuspidal Coefficients
-- statement:
--   Definitions and structural lemmas for Supercuspidal Coefficients, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SupercuspidalCoefficients.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepContragredient
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
open scoped Pointwise
section General
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {N M Nbar K : Subgroup G}
end General
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
def IsSupercuspidal (π : Representation ℂ (GL (Fin n) F) V) : Prop :=
  ∀ γ : Fin n → ℕ, (∃ i j, γ i ≠ γ j) → Subsingleton (JacquetModule F n γ π)
def matrixCoeff (π : Representation ℂ (GL (Fin n) F) V) (v : V) (f : Module.Dual ℂ V)
    (g : GL (Fin n) F) : ℂ :=
  f (π g v)
def IsCompactModCenter (φ : GL (Fin n) F → ℂ) : Prop :=
  ∃ C : Set (GL (Fin n) F), IsCompact C ∧
    Function.support φ ⊆ (Subgroup.center (GL (Fin n) F) : Set (GL (Fin n) F)) * C
section Compact
variable {π : Representation ℂ (GL (Fin n) F) V}
end Compact
section Converse
variable {π : Representation ℂ (GL (Fin n) F) V}
end Converse
end Parabolic
end GroundTheory.Automorphic


