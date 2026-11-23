-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsSimplicial
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IsSimplicial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:27.688298+00:00
-- url     : https://prove2.me/theorems/5f01933a-7523-4cb0-b447-3d1bb2c23f94
-- title:
--   Is Simplicial
-- statement:
--   Definitions and structural lemmas for Is Simplicial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsSimplicial.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
namespace GlobalTheory.Shintani
def openCone {W : Type} [AddCommGroup W] [Module ℚ W] (s : Finset W) : Set W :=
  {x | ∃ t : W → ℚ, (∀ v ∈ s, 0 < t v) ∧ x = ∑ v ∈ s, t v • v}
def IsSimplicial {W : Type} [AddCommGroup W] [Module ℚ W] (P : Set W) (s : Finset W) : Prop :=
  s.Nonempty ∧ LinearIndepOn ℚ id (s : Set W) ∧ (s : Set W) ⊆ P
def coneFuns {W : Type} [AddCommGroup W] [Module ℚ W] (P : Set W) : Submodule ℚ (W → ℚ) :=
  Submodule.span ℚ {f | ∃ s : Finset W, IsSimplicial P s ∧ f = (openCone s).indicator 1}
def IsPosCone {W : Type} [AddCommGroup W] [Module ℚ W] (P : Set W) : Prop :=
  ∀ u ∈ P, ∀ v ∈ P, ∀ a b : ℚ, 0 < a → 0 < b → a • u + b • v ∈ P
def totPos (F : Type) [Field F] : Set F := {x | ∀ σ : F →+* ℝ, 0 < σ x}
def rayUnits {F : Type} [Field F] (𝔣 : Ideal (𝓞 F)) : Subgroup (𝓞 F)ˣ where
  carrier := {u | (u : 𝓞 F) - 1 ∈ 𝔣 ∧ ((u : 𝓞 F) : F) ∈ totPos F}
  one_mem' := ⟨by simp, fun σ => by simp⟩
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨?_, fun σ => ?_⟩
    · rw [show ((u * v : (𝓞 F)ˣ) : 𝓞 F) - 1 = (u : 𝓞 F) * ((v : 𝓞 F) - 1) + ((u : 𝓞 F) - 1) by push_cast; ring]
      exact 𝔣.add_mem (𝔣.mul_mem_left _ hv) hu
    · have e : (((u * v : (𝓞 F)ˣ) : 𝓞 F) : F) = ((u : 𝓞 F) : F) * ((v : 𝓞 F) : F) := rfl
      rw [e, map_mul]
      exact mul_pos (hu' σ) (hv' σ)
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨?_, fun σ => ?_⟩
    · rw [show ((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) - 1 = -((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((u : 𝓞 F) - 1) by
        rw [neg_mul, mul_sub, Units.inv_mul]; ring]
      exact 𝔣.mul_mem_left _ hu
    · have e : (((u⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((u : 𝓞 F) : F) = 1 := by
        have := congrArg (algebraMap (𝓞 F) F) (Units.inv_mul u)
        rwa [map_mul, map_one] at this
      have e' := congrArg σ e
      rw [map_mul, map_one] at e'
      exact (mul_pos_iff_of_pos_right (hu' σ)).1 (by rw [e']; exact one_pos)
def IsEntRat {ι : Type} (f N : ι → ℚ) : Prop :=
  ∃ A : ℂ → ℂ, Differentiable ℂ A ∧ (∀ s : ℂ, 1 < s.re → HasSum (fun i => (f i : ℂ) * (N i : ℂ) ^ (-s)) (A s)) ∧
    ∀ k : ℕ, ∃ r : ℚ, A (-(k : ℂ)) = (r : ℂ)
def IsBalanced {ι : Type} [DecidableEq ι] (l : ℕ) (φ : (ι → ℕ) → ℚ) : Prop :=
  (∀ i j, φ (Function.update j i (j i + l)) = φ j) ∧ ∀ i j, ∑ t ∈ Finset.range l, φ (Function.update j i t) = 0
open Classical in

def smooth {F : Type} [Field F] [NumberField F] (𝔠 : Ideal (𝓞 F)) (x : 𝓞 F) : ℚ :=
  1 - if x ∈ 𝔠 then (Ideal.absNorm 𝔠 : ℚ) else 0
open Classical in

def smoothIdeal {F : Type} [Field F] [NumberField F] (𝔠 I : Ideal (𝓞 F)) : ℚ :=
  1 - if 𝔠 ∣ I then (Ideal.absNorm 𝔠 : ℚ) else 0
example : IsEntRat (fun _ : Unit => 1) (fun _ => 1) :=
  ⟨fun _ => 1, differentiable_const _, fun s _ => by simpa using hasSum_fintype (fun _ : Unit => (1 : ℂ)), fun _ => ⟨1, by simp⟩⟩
example : IsSimplicial (Set.Ioi (0 : ℚ)) {1} :=
  ⟨by simp, by simp, by simp⟩
end GlobalTheory.Shintani


