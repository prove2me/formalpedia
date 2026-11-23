-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:26.306399+00:00
-- url     : https://prove2.me/theorems/d028f1fe-8b91-4ae9-bfaf-a1a47df7e8aa
-- title:
--   Is Iwasawa Of Is Compact
-- statement:
--   Definitions and structural lemmas for Is Iwasawa Of Is Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean

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
namespace GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
section Iwasawa
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)
def IsIwasawa : Prop := (∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) ∧ ∀ p : P, (p : G) ∈ K → δ p = 1
open Classical in

def iwAbs (g : G) : ℝ≥0 := if h : ∃ p : P, ∃ k ∈ K, g = p * k then δ h.choose else 1
variable {δ K}
namespace IsIwasawa
variable (h : IsIwasawa δ K)
include h
end IsIwasawa
variable [TopologicalSpace G] [IsTopologicalGroup G]
end Iwasawa
def npow (r : ℝ≥0) (t : ℂ) : ℂ := ((r : ℝ) : ℂ) ^ t
@[simp] theorem npow_zero (r : ℝ≥0) : npow r 0 = 1 := Complex.cpow_zero _
@[simp] theorem one_npow (t : ℂ) : npow 1 t = 1 := by simp [npow]
section Induced
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
def IndLaw (Φ : G → ℂ) : Prop := ∀ (p : P) (g : G), Φ (p * g) = χ p * npow (δ p) t * Φ g
def kSpan (Φ : G → ℂ) : Submodule ℂ (G → ℂ) := Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = fun g => Φ (g * k)}
def IsKFinite (Φ : G → ℂ) : Prop := FiniteDimensional ℂ (kSpan K Φ)
variable {K}
theorem isKFinite_iff {Φ : G → ℂ} : IsKFinite K Φ ↔
    ∃ W : Submodule ℂ (G → ℂ), FiniteDimensional ℂ W ∧ ∀ k ∈ K, (fun g => Φ (g * k)) ∈ W :=
  ⟨fun h => ⟨_, h, fun k hk => Submodule.subset_span ⟨k, hk, rfl⟩⟩, fun ⟨_, _, h⟩ =>
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact h k hk))⟩
theorem IsKFinite.of_invariant {Φ : G → ℂ} (h : ∀ g, ∀ k ∈ K, Φ (g * k) = Φ g) : IsKFinite K Φ :=
  isKFinite_iff.2 ⟨ℂ ∙ Φ, inferInstance, fun k hk => by
    rw [show (fun g => Φ (g * k)) = Φ from funext fun g => h g k hk]; exact Submodule.mem_span_singleton_self _⟩
theorem IsKFinite.add {Φ Ψ : G → ℂ} (h : IsKFinite K Φ) (h' : IsKFinite K Ψ) : IsKFinite K (Φ + Ψ) := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  obtain ⟨W', _, hW'⟩ := isKFinite_iff.1 h'
  exact isKFinite_iff.2 ⟨W ⊔ W', inferInstance, fun k hk => Submodule.add_mem_sup (hW k hk) (hW' k hk)⟩
theorem IsKFinite.mul_invariant {Φ f : G → ℂ} (h : IsKFinite K Φ) (hf : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    IsKFinite K fun g => Φ g * f g := by
  obtain ⟨W, _, hW⟩ := isKFinite_iff.1 h
  refine isKFinite_iff.2 ⟨W.map (LinearMap.mulRight ℂ f), inferInstance, fun k hk => ⟨_, hW k hk, funext fun g => ?_⟩⟩
  simp [hf g k hk]
variable (K)
def indSpace [TopologicalSpace G] : Submodule ℂ (G → ℂ) where
  carrier := {Φ | IndLaw δ χ t Φ ∧ Continuous Φ ∧ IsKFinite K Φ}
  zero_mem' := ⟨fun _ _ => by simp, continuous_zero, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨fun p g => by simp only [Pi.add_apply, h.1 p g, h'.1 p g, mul_add],
    h.2.1.add h'.2.1, h.2.2.add h'.2.2⟩
  smul_mem' := fun c Φ h => ⟨fun p g => by simp only [Pi.smul_apply, h.1 p g, smul_eq_mul]; ring,
    h.2.1.const_smul c, by
      have := h.2.2.mul_invariant (f := fun _ => c) fun _ _ _ => rfl
      simp only [mul_comm _ c] at this
      exact this⟩
def flatSec (Φ : G → ℂ) (s₀ s : ℂ) : G → ℂ := fun g => Φ g * npow (iwAbs δ K g) (s - s₀)
def IsFlat (Φ : ℂ → G → ℂ) : Prop := ∀ s s', ∀ k ∈ K, Φ s k = Φ s' k
variable {δ K χ t}
theorem IndLaw.ext (h : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) {Φ Ψ : G → ℂ} (h1 : IndLaw δ χ t Φ) (h2 : IndLaw δ χ t Ψ)
    (e : ∀ k ∈ K, Φ k = Ψ k) : Φ = Ψ := funext fun g => by
  obtain ⟨p, k, hk, rfl⟩ := h g
  rw [h1, h2, e k hk]
namespace IsIwasawa
variable (h : IsIwasawa δ K)
include h
variable [TopologicalSpace G] [IsTopologicalGroup G]
end IsIwasawa
def IsRightSmooth [TopologicalSpace G] (Φ : G → ℂ) : Prop :=
  ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ g, ∀ u ∈ U, Φ (g * u) = Φ g
end Induced
section ZetaNonvanishing₂
variable {H : Type} {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
def coef (π : H → X → X) (x y : X) : H → ℂ := fun g => inner ℂ y (π g x)
variable [MeasurableSpace H] (m : Measure H)
def pairInt (f c : H → ℂ) : ℂ := ∫ g, f g * starRingEnd ℂ (c g) ∂m
def PairConv (f c : H → ℂ) : Prop := Integrable (fun g => f g * starRingEnd ℂ (c g)) m
end ZetaNonvanishing₂
example {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (x y : X) (c : ℂ) :
    coef (fun _ : Unit => id) (c • x) y () = c * coef (fun _ : Unit => id) x y () := inner_smul_right _ _ _
example {G : Type} [Group G] (δ : (⊤ : Subgroup G) →* ℝ≥0) : IsIwasawa δ ⊥ :=
  ⟨fun g => ⟨⟨g, trivial⟩, 1, one_mem _, (mul_one g).symm⟩, fun p hp => by
    rw [show p = 1 from Subtype.ext hp, map_one]⟩
end GlobalTheory.Doubling
end


