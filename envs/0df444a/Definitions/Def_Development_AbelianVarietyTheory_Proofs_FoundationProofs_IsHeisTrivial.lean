-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:36.527242+00:00
-- url     : https://prove2.me/theorems/2f3d15fb-79aa-4100-9e88-5256f76d961c
-- title:
--   Is Heis Trivial
-- statement:
--   Definitions and structural lemmas for Is Heis Trivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsHeisTrivial.lean

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
open Classical
open scoped BigOperators
namespace GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
structure IsHeis (σ : R →+* R) (w : R) (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M) : Prop where
  sg_sg : ∀ r, σ (σ r) = r
  w_add : w + σ w = 1
  add_left : ∀ x y z, γ (x + y) z = γ x z * γ y z
  add_right : ∀ x y z, γ x (y + z) = γ x y * γ x z
  alt : ∀ x, γ x x = 1
  adj : ∀ r x y, γ (r • x) y = γ x (σ r • y)
  zero : ∀ v, W 0 v = v
  comp : ∀ x y v, W x (W y v) = γ (w • x) y • W (x + y) v
def SelfDual (γ : X → X → ℂ) (A : Submodule R X) : Prop := ∀ x, x ∈ A ↔ ∀ a ∈ A, γ x a = 1
def Fixes (W : X → M →ₗ[ℂ] M) (A : Submodule R X) (v : M) : Prop := ∀ a ∈ A, W a v = v
def idx (A B : Submodule R X) : ℕ := A.toAddSubgroup.relIndex B.toAddSubgroup
def sumOp (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  ∑ᶠ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, W ((Quotient.out q : B.toAddSubgroup) : X) v
def normOp (lam : ℕ →* ℂ) (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  (lam (idx A B))⁻¹ • sumOp W A B v
def GoodNorm (σ : R →+* R) (lam : ℕ →* ℂ) : Prop :=
  (∀ n, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) →
    lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧
    ((∀ r ∈ P, σ r ∈ P) → lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P)
def Adj (A B : Submodule R X) : Prop :=
  ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x}
namespace IsHeis
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W)
include h
end IsHeis
end GlobalTheory.FinWeil


