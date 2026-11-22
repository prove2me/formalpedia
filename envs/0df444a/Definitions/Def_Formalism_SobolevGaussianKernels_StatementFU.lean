-- Prove2me | Definitions.Def_Formalism_SobolevGaussianKernels_StatementFU
-- name    : Formalism_SobolevGaussianKernels_StatementFU
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:41.826075+00:00
-- url     : https://prove2.me/theorems/b176364b-68a3-4d03-b117-512fa649528d
-- title:
--   Statement FU
-- statement:
--   Definitions and structural lemmas for Statement FU, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/StatementFU.lean

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.SL.FU
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR
def FrameGram : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (B : ∀ i, V i →ₗ[ℂ] H) (c : ι → ℝ),
    (LinearMap.trace ℂ H (frQ c B ∘ₗ frQ c B)).re
        = ∑ i, ∑ j, c i * c j * hs2 (LinearMap.adjoint (B i) ∘ₗ B j) ∧
    (LinearMap.trace ℂ H (frQ c B)).re
        = ∑ i, c i * (LinearMap.trace ℂ (V i) (LinearMap.adjoint (B i) ∘ₗ B i)).re
def FrameSplit : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (K0 K2 : ∀ i j, V j →ₗ[ℂ] V i),
    (∀ i j, i ≠ j → K2 i j = 0) →
    Real.sqrt (∑ i, ∑ j, hs2 (K0 i j + K2 i j))
        ≤ Real.sqrt (∑ i, ∑ j, hs2 (K0 i j)) + Real.sqrt (∑ i, hs2 (K2 i i)) ∧
    Real.sqrt (∑ i, hs2 (K0 i i + K2 i i - LinearMap.id))
        ≤ Real.sqrt (∑ i, hs2 (K0 i i - LinearMap.id)) + Real.sqrt (∑ i, hs2 (K2 i i)) ∧
    |∑ i, (LinearMap.trace ℂ (V i) (K2 i i)).re|
        ≤ Real.sqrt (∑ i, (finrank ℂ (V i) : ℝ)) * Real.sqrt (∑ i, hs2 (K2 i i))
def nebP {A : Type} [AddCommGroup A] [Fintype A] {H : Type} [AddCommGroup H] [Module ℂ H]
    (ρ : A → (H →ₗ[ℂ] H)) (χ : AddChar A ℂ) : H →ₗ[ℂ] H :=
  ((Fintype.card A : ℂ)⁻¹) • ∑ a, χ (-a) • ρ a
def NebProj : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (H : Type) [AddCommGroup H] [Module ℂ H]
    (ρ : A → (H →ₗ[ℂ] H)),
    ρ 0 = LinearMap.id → (∀ a b, ρ (a + b) = ρ a ∘ₗ ρ b) →
    (∀ χ : AddChar A ℂ, nebP ρ χ ∘ₗ nebP ρ χ = nebP ρ χ) ∧
    (∀ χ χ' : AddChar A ℂ, χ ≠ χ' → nebP ρ χ ∘ₗ nebP ρ χ' = 0) ∧
    (∑ χ : AddChar A ℂ, nebP ρ χ = LinearMap.id) ∧
    (∀ (a : A) (χ : AddChar A ℂ), ρ a ∘ₗ nebP ρ χ = χ a • nebP ρ χ) ∧
    (∀ T : H →ₗ[ℂ] H, (∀ a, T ∘ₗ ρ a = ρ a ∘ₗ T) →
      ∀ χ χ' : AddChar A ℂ, χ ≠ χ' → nebP ρ χ ∘ₗ T ∘ₗ nebP ρ χ' = 0)
def NebHS : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : A → (H →ₗ[ℂ] H)),
    ρ 0 = LinearMap.id → (∀ a b, ρ (a + b) = ρ a ∘ₗ ρ b) → (∀ a, LinearMap.adjoint (ρ a) = ρ (-a)) →
    (∀ χ : AddChar A ℂ, LinearMap.adjoint (nebP ρ χ) = nebP ρ χ) ∧
    (∀ T : H →ₗ[ℂ] H, ∑ χ : AddChar A ℂ, ∑ χ' : AddChar A ℂ, hs2 (nebP ρ χ ∘ₗ T ∘ₗ nebP ρ χ') = hs2 T) ∧
    (∀ T : H →ₗ[ℂ] H,
      ∑ χ : AddChar A ℂ, hs2 (nebP ρ χ ∘ₗ T ∘ₗ nebP ρ χ - nebP ρ χ) ≤ hs2 (T - LinearMap.id))
def Compress : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (P T : H →ₗ[ℂ] H), P ∘ₗ P = P → LinearMap.adjoint P = P →
    hs2 (P ∘ₗ T ∘ₗ P) ≤ hs2 T ∧ hs2 (P ∘ₗ T ∘ₗ P - P) ≤ hs2 (T - LinearMap.id)
end Formalism.SL.FU


