-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
-- name    : Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:19.027228+00:00
-- url     : https://prove2.me/theorems/1609edf8-34c8-416b-8615-e526c821f728
-- title:
--   Is Irreducible Iff
-- statement:
--   Definitions and structural lemmas for Is Irreducible Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/IsIrreducibleIff.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Theorems.Thm_GlobalTheory_CuspRep_isOpen_stab_of_mem_nhds
import Theorems.Thm_Reformulated_TransposeInverseTheory_coe_transposeInv
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_symm
import Theorems.Thm_Reformulated_TransposeInverseTheory_transposeInv_transposeInv
import Theorems.Thm_UpperTheory_Reformulated_B_IsOpenStabilizer_isOpen_stab_of_mem_nhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.TransposeInverseTheory.coe_transposeInv
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_symm
attribute [local simp] Reformulated.TransposeInverseTheory.transposeInv_transposeInv


set_option autoImplicit false
noncomputable section
open Topology
namespace GlobalTheory.CuspRep
variable {G : Type} [Group G]
theorem isIrreducible_iff {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun W hW => ?_⟩
    · have : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
        bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).1 ⟨⟨_, _, this⟩⟩
    · exact (eq_bot_or_eq_top (⟨W, hW⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule)
        (congrArg Subrepresentation.toSubmodule)
  · rintro ⟨h0, h⟩
    have : Nontrivial (Subrepresentation ρ) :=
      ⟨⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e : (⊥ : Submodule ℂ V) = ⊤)⟩⟩
    exact ⟨fun W => (h W.toSubmodule W.apply_mem_toSubmodule).imp
      (fun e => Subrepresentation.toSubmodule_injective e) (fun e => Subrepresentation.toSubmodule_injective e)⟩
@[simp] theorem twRep_apply {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (χ : G →* ℂˣ)
    (g : G) (v : V) : twRep ρ χ g v = ((χ g : ℂˣ) : ℂ) • ρ g v := rfl
variable [TopologicalSpace G]
variable (G) in

structure SmIrr where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  ρ : Representation ℂ G V
  smooth : GlobalTheory.PRep.IsSmooth ρ
  irred : ρ.IsIrreducible
attribute [instance] SmIrr.acg SmIrr.mod
variable (G) in

instance SmIrr.setoid : Setoid (SmIrr G) where
  r σ σ' := Nonempty (σ.ρ.Equiv σ'.ρ)
  iseqv := ⟨fun σ => ⟨.refl σ.ρ⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩
variable (G) in

def Irr : Type 1 := Quotient (SmIrr.setoid G)
variable (G) in

def SmIrr.triv : SmIrr G where
  V := ℂ
  ρ := Representation.trivial ℂ G ℂ
  smooth v := by simp
  irred := (isIrreducible_iff _).2 ⟨inferInstance, fun W _ => eq_bot_or_eq_top W⟩
instance : Inhabited (Irr G) := ⟨Quotient.mk _ (SmIrr.triv G)⟩
variable [IsTopologicalGroup G]
def SmIrr.twist (σ : SmIrr G) (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : SmIrr G where
  V := σ.V
  ρ := twRep σ.ρ χ
  smooth v := isOpen_stab_of_mem_nhds _ v <| Filter.mem_of_superset
    (((σ.smooth v).inter hχ).mem_nhds ⟨by simp, by simp⟩) fun g hg => by
      have h1 : σ.ρ g v = v := hg.1
      have h2 : χ g = 1 := hg.2
      simp [h1, h2]
  irred := by
    obtain ⟨h0, h⟩ := (isIrreducible_iff _).1 σ.irred
    refine (isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    exact (W.smul_mem_iff (Units.ne_zero (χ g))).1 (hW g v hv)
def Irr.twist (σ : Irr G) (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : Irr G :=
  Quotient.map (sa := SmIrr.setoid G) (sb := SmIrr.setoid G) (fun σ : SmIrr G => σ.twist χ hχ) (fun σ σ' ⟨e⟩ => ⟨.mk e.toLinearEquiv fun g => by
    ext v
    change e (((χ g : ℂˣ) : ℂ) • σ.ρ g v) = ((χ g : ℂˣ) : ℂ) • σ'.ρ g (e v)
    rw [map_smul]
    exact congrArg _ (LinearMap.congr_fun (e.isIntertwining' g) v)⟩) σ
def Irr.ofChar (χ : G →* ℂˣ) (hχ : IsOpen {g | χ g = 1}) : Irr G := Quotient.mk _ ((SmIrr.triv G).twist χ hχ)
end GlobalTheory.CuspRep


