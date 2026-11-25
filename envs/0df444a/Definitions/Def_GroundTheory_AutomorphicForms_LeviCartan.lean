-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
-- name    : GroundTheory_AutomorphicForms_LeviCartan
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T11:21:34.46789+00:00
-- url     : https://prove2.me/theorems/67a95b3d-5714-4308-b821-13e0916bd034
-- title:
--   Levi Cartan
-- statement:
--   Definitions and structural lemmas for Levi Cartan, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LeviCartan.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
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
open Matrix Iwasawa GLnLocal ValuativeRel
section Smith
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
end Smith
section Blocks
variable {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
abbrev blockOf : Fin n → Set.range β := Set.rangeFactorization β
abbrev Fiber (a : Set.range β) : Type := {i : Fin n // blockOf β i = a}
variable (R : Type*) [CommRing R]
def blockAssemble : (∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R) →+* Matrix (Fin n) (Fin n) R :=
  (reindexAlgEquiv R R (Equiv.sigmaFiberEquiv (blockOf β))).toRingEquiv.toRingHom.comp
    (blockDiagonal'RingHom (Fiber β) R)
def blocks (X : Matrix (Fin n) (Fin n) R) (a : Set.range β) : Matrix (Fiber β a) (Fiber β a) R :=
  fun i j => X i j
variable {β R}
end Blocks
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
end Parabolic
end GroundTheory.Automorphic


