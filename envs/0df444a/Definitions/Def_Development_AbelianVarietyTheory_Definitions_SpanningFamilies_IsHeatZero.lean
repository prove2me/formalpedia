-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
-- name    : Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:29.931398+00:00
-- url     : https://prove2.me/theorems/4716cc4a-9631-47d5-8c86-4b61a836e7a7
-- title:
--   Is Heat Zero
-- statement:
--   Definitions and structural lemmas for Is Heat Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SpanningFamilies/IsHeatZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
namespace GlobalTheory.SW
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
def SWAt (n N : ℕ) : Prop :=
  ∀ (M R : ℕ) (φ : Fam E n N), admitted M R φ → ∀ Z ∈ Hn Ψ N, swd Ψ M φ Z 0 0 = 0
def LevelL (Λ : Lt E n) (R : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ) : Prop :=
  (∀ x, φ x ≠ 0 → ColsIn Λ ((R : E) • x)) ∧ ∀ x y, ColsIn Λ y → φ (x + (R : E) • y) = φ x
abbrev CF (a b : ℕ) : Type := Ψ → Fin a → Fin b → ℂ
def IsHeat (D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ) : Prop :=
  DifferentiableOn ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
    {p | (p.1 : CM Ψ N N) ∈ Hn Ψ N} ∧
  ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (τ : Ψ) (a b : Fin N),
    2 * Real.pi * I * deriv (fun s : ℂ =>
      D (fun σ => Z σ + if σ = τ then Matrix.single a b s else 0) z z') 0 =
    ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ =>
      D Z (fun σ => z σ + if σ = τ then Matrix.single k a s else 0)
        (fun σ => z' σ + if σ = τ then Matrix.single k b t else 0)) 0) 0
def IsMaj {m : ℕ} (G : Matrix (Fin m) (Fin m) E) (H : CM Ψ m m) : Prop :=
  ∀ τ : Ψ, (H τ).PosDef ∧ H τ * (G.map τ.1)⁻¹ * H τ = G.map τ.1
def hval {m : ℕ} (H : CM Ψ m m) (τ : Ψ) (v : Fin m → E) : ℝ :=
  ((fun a => τ.1 (v a)) ⬝ᵥ H τ *ᵥ fun a => conj (τ.1 (v a))).re
def IsoRows {k m : ℕ} (G : Matrix (Fin m) (Fin m) E) (W : Matrix (Fin k) (Fin m) E) : Prop :=
  LinearIndependent E (fun i => W i) ∧ W * G * ccT W = 0
def ShortIso (N D : ℕ) (ε C : ℝ) : Prop :=
  ∀ (G : Matrix (Fin (2 * N)) (Fin (2 * N)) E) (H : CM Ψ (2 * N) (2 * N)), ccT G = G → G.det ≠ 0 →
    Den D G → Den D G⁻¹ → (∃ W : Matrix (Fin N) (Fin (2 * N)) E, IsoRows G W) → IsMaj Ψ G H →
    (∀ v : Fin (2 * N) → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) → ε ≤ ∑ τ, hval Ψ H τ v) →
    ∃ W : Matrix (Fin N) (Fin (2 * N)) E, IntM W ∧ IsoRows G W ∧ ∀ i τ, hval Ψ H τ (W i) ≤ C
end
end GlobalTheory.SW


