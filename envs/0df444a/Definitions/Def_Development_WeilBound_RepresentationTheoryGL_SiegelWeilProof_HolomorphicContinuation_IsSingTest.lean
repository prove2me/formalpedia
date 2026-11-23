-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_IsSingTest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:13.340801+00:00
-- url     : https://prove2.me/theorems/4478a6d0-8326-46fd-93b2-e6e1ff83cf29
-- title:
--   Is Sing Test
-- statement:
--   Definitions and structural lemmas for Is Sing Test, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/IsSingTest.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
namespace PositivityTheory.Rg.Sw
variable {n : ℕ}
abbrev M2 (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ
def JJ (n : ℕ) : M2 n := fromBlocks 0 1 (-1) 0
def InG (g : M2 n) : Prop := gᴴ * JJ n * g = JJ n
def InK (g : M2 n) : Prop := InG g ∧ gᴴ * g = 1
def herm (x : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((x i j + x j i : ℝ) : ℂ) / 2 + Complex.I * ((x i j - x j i : ℝ) : ℂ) / 2
def nU (b : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks 1 b 0 1
def u1 (g : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • g.toBlocks₂₁ + g.toBlocks₂₂
def u2 (g : M2 n) : Matrix (Fin n) (Fin n) ℂ := -(Complex.I • g.toBlocks₂₁) + g.toBlocks₂₂
def f0 (p q : ℤ) (g : M2 n) : ℂ := (u1 g).det ^ (-p) * (u2 g).det ^ (-q)
def eTr (β : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (β * herm x).trace)
def IsSingTest (ψ : (Fin n → Fin n → ℝ) → ℂ) : Prop :=
  Continuous ψ ∧ HasCompactSupport ψ ∧
    ∀ β : Matrix (Fin n) (Fin n) ℂ, β.IsHermitian → β.det = 0 → ∫ x, ψ x * eTr β x = 0
def GoodSig (n p q : ℕ) : Prop := n < p ∨ n < q ∨ (q = 0 ∧ n ≤ p) ∨ (p = 0 ∧ n ≤ q)
def LV : Prop :=
  ∀ (n p q : ℕ), GoodSig n p q →
    ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
      [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι → (∀ g, InK g ↔ ∃ k, ι k = g) →
      ∃ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n), IsSingTest ψ ∧ InG a ∧ InG b ∧
        ∫ k, (∫ x, f0 p q (ι k * a * nU (herm x) * b) * ψ x) * (f0 p q (ι k))⁻¹ ∂μ ≠ 0
def TwoSided : Prop :=
  ∀ (n : ℕ) (H : Type) (F : H → M2 n → ℂ) (Γ : Set (M2 n)), (∀ h, ContinuousOn (F h) {g | InG g}) →
    (∀ γ ∈ Γ, InG γ) → {g | InG g} ⊆ closure Γ → (∀ γ ∈ Γ, ∀ h, ∃ h', ∀ g, InG g → F h (γ * g) = F h' g) →
    ∀ ψ : (Fin n → Fin n → ℝ) → ℂ, Continuous ψ → HasCompactSupport ψ →
      (∀ h g, InG g → ∫ x, F h (nU (herm x) * g) * ψ x = 0) →
      ∀ h a b, InG a → InG b → ∫ x, F h (a * nU (herm x) * b) * ψ x = 0
end PositivityTheory.Rg.Sw


