-- Prove2me | Definitions.Def_Formalism_AlphaUniqueness_Statement
-- name    : Formalism_AlphaUniqueness_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:12.398816+00:00
-- url     : https://prove2.me/theorems/8f0cd903-739a-4624-8f7e-bff3e3b5825a
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AlphaUniqueness/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.K
section Gauss
variable {M : Type*} [AddCommGroup M]
def polar (Q : M → ℂ) (x y : M) : ℂ :=
  Q (x + y) * (starRingEnd ℂ) (Q x) * (starRingEnd ℂ) (Q y)
structure IsUQuad (Q : M → ℂ) : Prop where
  norm_eq : ∀ x, ‖Q x‖ = 1
  neg : ∀ x, Q (-x) = Q x
  polar_add : ∀ x x' y, polar Q (x + x') y = polar Q x y * polar Q x' y
def Nondeg (Q : M → ℂ) : Prop := ∀ y, (∀ x, polar Q x y = 1) → y = 0
def gsum [Fintype M] (Q : M → ℂ) : ℂ := ∑ x, Q x
def prim (p : ℕ) : AddSubgroup M where
  carrier := {x | ∃ k : ℕ, p ^ k • x = 0}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have h1 : (p ^ (a + b)) • x = 0 := by rw [pow_add, mul_comm (p ^ a), mul_smul, ha, smul_zero]
    have h2 : (p ^ (a + b)) • y = 0 := by rw [pow_add, mul_smul, hb, smul_zero]
    rw [smul_add, h1, h2, add_zero]
  neg_mem' := by
    rintro x ⟨k, hk⟩
    exact ⟨k, by rw [smul_neg, hk, neg_zero]⟩
end Gauss
def GaussAbs : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (Q : M → ℂ), IsUQuad Q →
    (Nondeg Q ↔ ‖gsum Q‖ ^ 2 = (Fintype.card M : ℝ))
def QuadraticGaussSumSign : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (Q : M → ℂ) (l : ℕ) (σ : AddMonoid.End M),
    l.Prime → l % 4 = 1 → IsUQuad Q → Nondeg Q →
    (∀ x, Q (σ x) = Q x) → (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    (∀ p : ℕ, p.Prime → p ≠ l → IsSquare (Nat.card (prim (M := M) p))) →
    gsum Q ^ 2 = (Fintype.card M : ℂ)
def DetSign : Prop :=
  ∀ (S : Type) [Fintype S] (n : ℕ) (γ : S → Matrix (Fin n) (Fin n) ℂ),
    (∀ k, γ k ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ k, (1 - (γ k)⁻¹).det ≠ 0) →
    (((‖∏ k, (1 - (γ k)⁻¹).det‖ : ℝ) : ℂ) / (∏ k, (1 - (γ k)⁻¹).det)) ^ 2
      = (-1) ^ (n * Fintype.card S) * ∏ k, (γ k).det
def SquareClassUnitaryProduct : Prop :=
  ∀ (S : Type) [Fintype S] (n : ℕ) (γ : S → Matrix (Fin n) (Fin n) ℂ),
    (∀ k, γ k ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ k, (1 - (γ k)⁻¹).det ≠ 0) →
    Even (Fintype.card S) →
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (Q : M → ℂ) (l : ℕ) (σ : AddMonoid.End M),
    l.Prime → l % 4 = 1 → IsUQuad Q → Nondeg Q →
    (∀ x, Q (σ x) = Q x) → (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    (∀ p : ℕ, p.Prime → p ≠ l → IsSquare (Nat.card (prim (M := M) p))) →
    ((((‖∏ k, (1 - (γ k)⁻¹).det‖ : ℝ) : ℂ) / (∏ k, (1 - (γ k)⁻¹).det))
        * (gsum Q / ((Real.sqrt (Fintype.card M) : ℝ) : ℂ))) ^ 2
      = ∏ k, (γ k).det
section Alpha
variable {L : Type*} [AddCommGroup L]
def qRef (ψ : L →+ L →+ ZMod 2) (σ : AddMonoid.End L) (l : ℕ) (x : L) : ZMod 2 :=
  ∑ i ∈ range l, ∑ j ∈ Ico (i + 1) l, ψ ((σ ^ i) x) ((σ ^ j) x)
end Alpha
def AlphaRefine : Prop :=
  ∀ (L : Type) [AddCommGroup L] (ψ : L →+ L →+ ZMod 2) (σ : AddMonoid.End L) (l : ℕ),
    Odd l → (∀ x, ψ x x = 0) → (∀ x y, ψ (σ x) (σ y) = ψ x y) →
    (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    (∀ x y, qRef ψ σ l (x + y) = qRef ψ σ l x + qRef ψ σ l y + ψ x y) ∧
    (∀ x, qRef ψ σ l (σ x) = qRef ψ σ l x)
def AlphaUnique : Prop :=
  ∀ (L : Type) [AddCommGroup L] (ψ : L →+ L →+ ZMod 2) (σ : AddMonoid.End L) (l : ℕ),
    Odd l → (∀ x, ψ x x = 0) → (∀ x y, ψ (σ x) (σ y) = ψ x y) →
    (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    ∀ q' : L → ZMod 2, (∀ x y, q' (x + y) = q' x + q' y + ψ x y) → (∀ x, q' (σ x) = q' x) →
      q' = qRef ψ σ l
def AlphaInv : Prop :=
  ∀ (L : Type) [AddCommGroup L] (ψ : L →+ L →+ ZMod 2) (σ : AddMonoid.End L) (l : ℕ),
    Odd l → (∀ x, ψ x x = 0) → (∀ x y, ψ (σ x) (σ y) = ψ x y) →
    (∀ x, ∑ i ∈ range l, (σ ^ i) x = 0) →
    ∀ γ : AddMonoid.End L, (∀ x, γ (σ x) = σ (γ x)) → (∀ x y, ψ (γ x) (γ y) = ψ x y) →
      ∀ x, qRef ψ σ l (γ x) = qRef ψ σ l x
end Formalism.K


