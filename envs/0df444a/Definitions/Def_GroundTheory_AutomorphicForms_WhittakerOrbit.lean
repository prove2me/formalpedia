-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
-- name    : GroundTheory_AutomorphicForms_WhittakerOrbit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:29.661801+00:00
-- url     : https://prove2.me/theorems/3b3a3658-103d-45bc-bc7a-2b564e7a83fd
-- title:
--   Whittaker Orbit
-- statement:
--   Definitions and structural lemmas for Whittaker Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace Whittaker
open Set Topology MulAction
open scoped Pointwise
section Translation
variable {X : Type*} {H : Type*} [Group H] [MulAction H X]
def transl (h : H) (f : X → ℂ) : X → ℂ := fun x => f (h⁻¹ • x)
end Translation
section Relations
variable {X : Type*} [TopologicalSpace X] {H : Type*} [Group H] [TopologicalSpace H]
  [MulAction H X] [ContinuousSMul H X]
def relSpan (χ : H →* ℂ) (U : Set X) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ {g | ∃ h : H, ∃ f ∈ supportedIn U, g = transl h f - χ h • f}
end Relations
section Orbit
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
def orbitPiece (L : Subgroup H) (y : X) : Set X := (fun l : H => l • y) '' (L : Set H)
section Base
variable {U C : Set X} {x₀ : X}
def GoodPiece (U C : Set X) (x₀ : X) (W : Submodule ℂ (X → ℂ)) (A : Set X) : Prop :=
  ∀ g ∈ supportedIn U, (∀ x ∈ orbit H x₀, g x = A.indicator 1 x) →
    g ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)
end Base
end Orbit
end Whittaker
end GroundTheory.Automorphic


