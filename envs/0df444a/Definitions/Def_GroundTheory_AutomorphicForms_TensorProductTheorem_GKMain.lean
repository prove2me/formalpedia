-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKMain
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_GKMain
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:31:07.425851+00:00
-- url     : https://prove2.me/theorems/9f54ae91-b304-4c78-96c7-4926e6e5cdcc
-- title:
--   GKMain
-- statement:
--   Definitions and structural lemmas for GKMain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKMain.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
namespace GroundTheory.Automorphic
attribute [local instance 100] LieRing.ofAssociativeRing
open Set Module RestrictedTensor CompactRep TensorProduct
open scoped TensorProduct
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G}
  [CompactSpace K]
def IsExpLieAlgebra.GKModule.IsKAdmissible {W : Type*} [AddCommGroup W] [Module ℂ W]
    (M : h.GKModule K W) : Prop :=
  ∀ (c : Submodule (MonoidAlgebra ℂ K) M.σ.asModule)
    (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) M.σ.asModule),
    FiniteDimensional ℂ (LinearMap.range (kProj M.isKFinite hc))
namespace GKTensor
section Smooth
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {τ : Representation ℂ L V}
def mGenQuotMap (e : End ℂ V) (N : Submodule ℂ V) :
    Representation.IntertwiningMap (mGenSubrep τ N).toRepresentation (mGenQuotRep τ e N) where
  toLinearMap := (mGenKernel τ e N).mkQ
  isIntertwining' g := LinearMap.ext fun _ => rfl
end Smooth
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type u} [AddCommGroup V] [Module ℂ V]
namespace GKLModule
variable (Mx : GKLModule h K L V)
structure Decomposition where

  W₁ : Type u

  W₂ : Type u
  [instAddCommGroup₁ : AddCommGroup W₁]
  [instModule₁ : Module ℂ W₁]
  [instAddCommGroup₂ : AddCommGroup W₂]
  [instModule₂ : Module ℂ W₂]

  π₁ : h.GKModule K W₁

  π₂ : Representation ℂ L W₂
  isIrreducible₁ : π₁.IsIrreducible
  isKAdmissible₁ : π₁.IsKAdmissible
  isIrreducible₂ : π₂.IsIrreducible
  isAdmissible₂ : GroundTheory.Automorphic.IsAdmissible π₂

  equiv : Mx.fullRep.Equiv (outerTensor π₁.rep π₂)
attribute [instance] Decomposition.instAddCommGroup₁ Decomposition.instModule₁
  Decomposition.instAddCommGroup₂ Decomposition.instModule₂
namespace Decomposition
variable {Mx}
end Decomposition
end GKLModule
end GKTensor
end GroundTheory.Automorphic


