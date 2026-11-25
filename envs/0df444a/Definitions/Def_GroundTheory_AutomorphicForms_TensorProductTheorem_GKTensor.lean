-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_GKTensor
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:23:09.006415+00:00
-- url     : https://prove2.me/theorems/4e0036c4-a668-4a21-8721-ae58110cf5df
-- title:
--   GKTensor
-- statement:
--   Definitions and structural lemmas for GKTensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/GKTensor.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactorUnique
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_GKModule_rep_comm

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
open Set Module RestrictedTensor CompactRep
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace GKTensor
section FixedEnd
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {τ : Representation ℂ L V} (hτ : IsSmooth τ)
  {H : Subgroup L} (hHc : IsCompact (H : Set L)) (hHo : IsOpen (H : Set L))
def fixedEnd : End ℂ V := (fixedVectors τ H).subtype ∘ₗ fixedProj τ hτ hHc hHo
end FixedEnd
variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} [CompactSpace K]
theorem _root_.GroundTheory.Automorphic.IsExpLieAlgebra.GKModule.isKFinite {V : Type*} [AddCommGroup V]
    [Module ℂ V] (M : h.GKModule K V) : IsKFinite M.σ :=
  ⟨M.locallyFinite, M.hasContinuousCoeff⟩
variable (h K) in

structure GKLModule (L : Type*) [Group L] (V : Type*) [AddCommGroup V] [Module ℂ V] where

  gk : h.GKModule K V

  τ : Representation ℂ L V
  comm_ρ : ∀ X g, gk.ρ X * τ g = τ g * gk.ρ X
  comm_σ : ∀ k g, gk.σ k * τ g = τ g * gk.σ k
namespace GKLModule
variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
  [T2Space L] [TotallyDisconnectedSpace L] {V : Type u} [AddCommGroup V] [Module ℂ V]
  (Mx : GKLModule h K L V)
theorem rep_comm (a : FreeMonoid (h.lieSubalgebra ⊕ K)) (g : L) :
    Mx.gk.rep a * Mx.τ g = Mx.τ g * Mx.gk.rep a :=
  Mx.gk.rep_comm (fun X => Mx.comm_ρ X g) (fun k => Mx.comm_σ k g) a
def fullRep : Representation ℂ (FreeMonoid (h.lieSubalgebra ⊕ K) × L) V :=
  prodRep Mx.gk.rep Mx.τ Mx.rep_comm
def IsIrreducible : Prop := Mx.fullRep.IsIrreducible
def IsAdmissible : Prop :=
  IsSmooth Mx.τ ∧ ∀ (H : Subgroup L), IsCompact (H : Set L) → IsOpen (H : Set L) →
    ∀ (c : Submodule (MonoidAlgebra ℂ K) Mx.gk.σ.asModule)
      (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) Mx.gk.σ.asModule),
      FiniteDimensional ℂ (LinearMap.range (kProj Mx.gk.isKFinite hc ∘ₗ (fixedVectors Mx.τ H).subtype))
end GKLModule
end GKTensor
end GroundTheory.Automorphic


