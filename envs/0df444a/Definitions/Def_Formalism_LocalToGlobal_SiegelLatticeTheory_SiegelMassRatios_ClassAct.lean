-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:22.620104+00:00
-- url     : https://prove2.me/theorems/b43775f7-b6fb-4207-8296-754fe34eed89
-- title:
--   Class Act
-- statement:
--   Definitions and structural lemmas for Class Act, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ClassAct.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.ClassAct
open Formalism.UG Module
section Abstract
variable {G : Type} [Group G]
def Normalises (D K : Subgroup G) : Prop := ∀ δ ∈ D, ∀ κ ∈ K, δ * κ * δ⁻¹ ∈ K
def rtCl (Γ K : Subgroup G) (δ : G) (hδ : ∀ κ ∈ K, δ⁻¹ * κ * δ ∈ K) : ClassSet Γ K → ClassSet Γ K :=
  _root_.Quotient.map' (fun x => x * δ) (by
    intro a b hab
    obtain ⟨γ, hγ, κ, hκ, rfl⟩ := DoubleCoset.rel_iff.mp hab
    refine DoubleCoset.rel_iff.mpr ⟨γ, hγ, δ⁻¹ * κ * δ, hδ κ hκ, ?_⟩
    group)
def DiaFree (Γ K D : Subgroup G) : Prop :=
  ∀ x : G, ∀ δ ∈ D, DoubleCoset.mk Γ K (x * δ) = DoubleCoset.mk Γ K x → δ ∈ K
def AMFChi (k : Type) [CommRing k] {W : Type} [AddCommGroup W] [Module k W] (Γ K : Subgroup G)
    (ρ : Representation k Γ W) (χ : K →* kˣ) : Submodule k (G → W) where
  carrier := {f | ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ((χ κ : kˣ) : k) • ρ γ (f g)}
  zero_mem' := by intro γ g κ; simp
  add_mem' := by
    intro f f' hf hf' γ g κ
    simp only [Pi.add_apply, hf γ g κ, hf' γ g κ, map_add, smul_add]
  smul_mem' := by
    intro c f hf γ g κ
    simp only [Pi.smul_apply, hf γ g κ, map_smul]
    rw [smul_comm]
def rtF (k : Type) [CommRing k] (W : Type) [AddCommGroup W] [Module k W] (δ : G) : (G → W) →ₗ[k] (G → W) :=
  LinearMap.funLeft k W (fun g => g * δ)
def FixAt (k : Type) [CommRing k] {W : Type} [AddCommGroup W] [Module k W] (Γ K : Subgroup G)
    (ρ : Representation k Γ W) (χ : K →* kˣ) (D : Subgroup G) : Submodule k (G → W) :=
  AMFChi k Γ K ρ χ ⊓ ⨅ δ : D, LinearMap.ker (rtF k W (δ : G) - LinearMap.id)
end Abstract
def FixedDim : Prop :=
  ∀ (G : Type) [Group G] (Γ K K₀ D : Subgroup G) (k : Type) [Field k] (W : Type) [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (ρ : Representation k Γ W) (χ : K →* kˣ),
    K ≤ K₀ → D ≤ K₀ → IsNeat Γ K₀ → Normalises D K →
    (∀ δ ∈ D, ∀ κ κ' : K, (κ' : G) = δ * κ * δ⁻¹ → χ κ' = χ κ) →
    (∀ κ : K, (κ : G) ∈ D → χ κ = 1) →
    Finite (ClassSet Γ K) →
    finrank k (FixAt k Γ K ρ χ D) * K.relIndex D = finrank k (AMFChi k Γ K ρ χ)
end Formalism.L2.SG.ClassAct


