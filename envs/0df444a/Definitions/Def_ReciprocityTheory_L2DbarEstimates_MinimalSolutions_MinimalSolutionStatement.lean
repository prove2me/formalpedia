-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolutionStatement
-- name    : ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolutionStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:40.036804+00:00
-- url     : https://prove2.me/theorems/e429bfbb-513d-44f7-8d06-1fea57d59056
-- title:
--   Minimal Solution Statement
-- statement:
--   Definitions and structural lemmas for Minimal Solution Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/MinimalSolutions/MinimalSolutionStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates
open scoped InnerProductSpace
def WeakAdj {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) (f : H₂) (w : H₁) : Prop :=
  ∀ g : E, ⟪t g, f⟫_ℂ = ⟪ι g, w⟫_ℂ
def CVXStatement (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Prop :=
  ∀ K : ℕ → Set H, Antitone K → (∀ n, (K n).Nonempty) → (∀ n, IsClosed (K n)) →
    (∀ n, ∀ x ∈ K n, ∀ y ∈ K n, (2 : ℂ)⁻¹ • (x + y) ∈ K n) → Bornology.IsBounded (K 0) →
    ∃ x : H, ∀ n, x ∈ K n
def RieszOnRangeStatement (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ (θ : E →ₗ[ℂ] H) (ℓ : E →ₗ[ℂ] ℂ) (A : ℝ), 0 ≤ A →
    (∀ e : E, ‖ℓ e‖ ^ 2 ≤ A * ‖θ e‖ ^ 2) →
    ∃ u ∈ (LinearMap.range θ).topologicalClosure, ‖u‖ ^ 2 ≤ A ∧ ∀ e : E, ⟪u, θ e⟫_ℂ = ℓ e
def MinimalSolutionStatement (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Prop :=
  ∀ (θ : E →ₗ[ℂ] H) (ℓ : E →ₗ[ℂ] ℂ) (u u' : H),
    u ∈ (LinearMap.range θ).topologicalClosure →
    (∀ e : E, ⟪u, θ e⟫_ℂ = ℓ e) → (∀ e : E, ⟪u', θ e⟫_ℂ = ℓ e) →
    u' - u ∈ (LinearMap.range θ)ᗮ ∧ ‖u‖ ≤ ‖u'‖ ∧
      (u' ∈ (LinearMap.range θ).topologicalClosure → u' = u)
def SplitStatement (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] : Prop :=
  ∀ (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) (K : Submodule ℂ H₂), IsClosed (K : Set H₂) →
    LinearMap.range t ≤ K → ∀ (f : H₂) (w : H₁), WeakAdj ι t f w →
    ∃ f₁ f₂ : H₂, f = f₁ + f₂ ∧ f₁ ∈ K ∧ f₂ ∈ Kᗮ ∧ WeakAdj ι t f₁ w ∧ WeakAdj ι t f₂ 0
def HormanderLemmaStatement (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] : Prop :=
  ∀ (ι : E →ₗ[ℂ] H₁) (t : E →ₗ[ℂ] H₂) (K : Submodule ℂ H₂), IsClosed (K : Set H₂) →
    LinearMap.range t ≤ K → ∀ (v : H₂) (A : ℝ), 0 ≤ A → v ∈ K →
    (∀ f ∈ K, ∀ w : H₁, WeakAdj ι t f w → ‖⟪v, f⟫_ℂ‖ ^ 2 ≤ A * ‖w‖ ^ 2) →
    ∃ u : H₁, ‖u‖ ^ 2 ≤ A ∧ ∀ (f : H₂) (w : H₁), WeakAdj ι t f w → ⟪u, w⟫_ℂ = ⟪v, f⟫_ℂ
def OntoWithBoundStatement (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] : Prop :=
  ∀ (G : H₁ →ₗ[ℂ] H₂) (Gs : H₂ →ₗ[ℂ] H₁) (θ : E →ₗ[ℂ] H₁) (Q : Submodule ℂ H₂) (c : ℝ), 0 < c →
    (∀ u ∈ Q, ∀ x : H₁, ⟪Gs u, x⟫_ℂ = ⟪u, G x⟫_ℂ) →
    (∀ u ∈ Q, ∀ e : E, c * ‖u‖ ^ 2 ≤ ‖Gs u + θ e‖ ^ 2) →
    ∀ f ∈ Q, ∃ h : H₁, (∀ u ∈ Q, ⟪u, G h⟫_ℂ = ⟪u, f⟫_ℂ) ∧ (∀ e : E, ⟪h, θ e⟫_ℂ = 0) ∧
      c * ‖h‖ ^ 2 ≤ ‖f‖ ^ 2
end ReciprocityTheory.L2DbarEstimates


