-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:25.867261+00:00
-- url     : https://prove2.me/theorems/c0a5c13d-bdcc-40b4-ace5-cd667e0d505d
-- title:
--   Polarisation Module Index
-- statement:
--   Definitions and structural lemmas for Polarisation Module Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/PolarisationModuleIndex.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_algebraMap_mem_orderC
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_CMVal_mul_mem_lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
variable {E : Type} [Field E] [NumberField E]
def latMod (c : Ideal (OF E)) (y : (Af E)ˣ) : Submodule (OF E) E where
  carrier := lattice c y
  zero_mem' := (latticeSub c y).zero_mem
  add_mem' := fun ha hb => (latticeSub c y).add_mem ha hb
  smul_mem' := fun a x hx => by
    rw [Algebra.smul_def]
    exact mul_mem_lattice (algebraMap_mem_orderC c a) hx
@[simp] theorem coe_latMod (c : Ideal (OF E)) (y : (Af E)ˣ) : (latMod c y : Set E) = lattice c y := rfl
def TrInt (x : E) : Prop := ∃ n : ℤ, Algebra.trace ℚ E x = n
theorem TrInt.zero : TrInt (0 : E) := ⟨0, by simp⟩
theorem TrInt.add {x y : E} (hx : TrInt x) (hy : TrInt y) : TrInt (x + y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  exact ⟨m + n, by rw [map_add, hm, hn]; push_cast; rfl⟩
variable [IsCMField E]
abbrev bar (x : E) : E := IsCMField.complexConj E x
theorem bar_algebraMap (a : OF E) : bar (algebraMap (OF E) E a) = algebraMap (OF E) E a :=
  (IsCMField.complexConj E).commutes (a : maximalRealSubfield E)
def dualLat (L : Submodule (OF E) E) : Submodule (OF E) E where
  carrier := {z | ∀ x ∈ L, TrInt (z * bar x)}
  zero_mem' := fun x _ => by rw [zero_mul]; exact TrInt.zero
  add_mem' := fun ha hb x hx => by rw [add_mul]; exact (ha x hx).add (hb x hx)
  smul_mem' := fun a z hz x hx => by
    have h := hz (a • x) (L.smul_mem a hx)
    have e : z * bar (a • x) = a • z * bar x := by
      rw [Algebra.smul_def, Algebra.smul_def, bar, map_mul, ← bar, bar_algebraMap]; ring
    rwa [e] at h
def polMod (L : Submodule (OF E) E) : Submodule (OF E) E where
  carrier := {ξ | bar ξ = -ξ ∧ ∀ x ∈ L, ∀ y ∈ L, TrInt (ξ * x * bar y)}
  zero_mem' := ⟨by simp, fun x _ y _ => by rw [zero_mul, zero_mul]; exact TrInt.zero⟩
  add_mem' := fun {a b} ha hb => ⟨by
      have h1 := ha.1
      have h2 := hb.1
      simp only [bar] at h1 h2 ⊢
      rw [map_add, h1, h2]; ring,
    fun x hx y hy => by rw [add_mul, add_mul]; exact (ha.2 x hx y hy).add (hb.2 x hx y hy)⟩
  smul_mem' := fun a ξ hξ => ⟨by
      have h1 := hξ.1
      rw [Algebra.smul_def, bar, map_mul, ← bar, ← bar, bar_algebraMap, h1]; ring,
    fun x hx y hy => by
      have h := hξ.2 (a • x) (L.smul_mem a hx) y hy
      have e : ξ * (a • x) = a • ξ * x := by rw [Algebra.smul_def, Algebra.smul_def]; ring
      rwa [e] at h⟩
def polPos {I : Type} (φ : I → E →+* ℂ) (e₀ : ℤˣ) (L : Submodule (OF E) E) : Set E :=
  {ξ | ξ ∈ polMod L ∧ ∀ i, 0 < ((e₀ : ℤ) : ℝ) * (φ i ξ).im}
def GenAt (l : ℕ) (M : Submodule (OF E) E) (ξ : E) : Prop :=
  ξ ∈ M ∧ ∀ η ∈ M, ∃ n : ℕ, n.Coprime l ∧ ∃ a : OF E, (n : E) * η = algebraMap (OF E) E a * ξ
def mulLat (ξ : E) (L : Submodule (OF E) E) : Submodule (OF E) E := L.map (LinearMap.mulLeft (OF E) ξ)
def polIndex (ξ : E) (L : Submodule (OF E) E) : ℕ := (mulLat ξ L).toAddSubgroup.relIndex (dualLat L).toAddSubgroup
def ModulePart {I : Type} (φ : I → E →+* ℂ) (e₀ : ℤˣ) : Prop :=
  ∀ (c : Ideal (OF E)), c ≠ ⊥ → ∀ y : (Af E)ˣ,
    Module.Invertible (OF E) (polMod (latMod c y)) ∧
    polMod (latMod c y) * latMod c y = dualLat (latMod c y) ∧
    (polPos φ e₀ (latMod c y)).Nonempty ∧
    ∀ l : ℕ, l.Prime →
      (∃ ξ ∈ polPos φ e₀ (latMod c y), GenAt l (polMod (latMod c y)) ξ) ∧
      ∀ ξ ∈ polPos φ e₀ (latMod c y), GenAt l (polMod (latMod c y)) ξ →
        mulLat ξ (latMod c y) ≤ dualLat (latMod c y) ∧ polIndex ξ (latMod c y) ≠ 0 ∧ (polIndex ξ (latMod c y)).Coprime l
def SizePart {I : Type} (φ : I → E →+* ℂ) (e₀ : ℤˣ) : Prop :=
  ∀ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q →
    ∀ l : ℕ, l.Prime → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
      ∀ y : (Af E)ˣ, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → (y : Af E) P = 1) →
        ∀ ξ ∈ polPos φ e₀ (latMod (condQ 𝔣 Q) y), GenAt l (polMod (latMod (condQ 𝔣 Q) y)) ξ →
          ξ ≠ 0 ∧ (∀ σ : E →+* ℂ, IntAt l (σ ξ)⁻¹) ∧
          (¬ (l : ℤ) ∣ discr E → (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 → (l : OF E) ∉ v.asIdeal) →
            ∀ σ : E →+* ℂ, UnitAt l (σ ξ))
def PolarisationModule : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], UnramFin E →
    ∀ (I : Type) (φ : I → E →+* ℂ), IsCMType φ → ∀ e₀ : ℤˣ, ModulePart φ e₀ ∧ SizePart φ e₀
def PolarisationModuleInduced : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], UnramFin E →
    ∀ (I : Type) (φ : I → E →+* ℂ), IsCMType φ →
      ∀ (d : ℕ) (δ : E), 0 < d → δ ^ 2 = -(d : E) → (∀ i, φ i δ = Complex.I * (Real.sqrt d : ℝ)) →
        ∀ e₀ : ℤˣ, ModulePart φ e₀ ∧ SizePart φ e₀
example {I : Type} (φ : I → E →+* ℂ) (e₀ : ℤˣ) (L : Submodule (OF E) E) (ξ : E) :
    ξ ∈ polPos φ (-e₀) L ↔ -ξ ∈ polPos φ e₀ L := by
  simp [polPos]
example {I : Type} [Nonempty I] (φ : I → E →+* ℂ) (e₀ : ℤˣ) (L : Submodule (OF E) E) : (0 : E) ∉ polPos φ e₀ L :=
  fun h => by simpa using h.2 (Classical.arbitrary I)
end GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex


