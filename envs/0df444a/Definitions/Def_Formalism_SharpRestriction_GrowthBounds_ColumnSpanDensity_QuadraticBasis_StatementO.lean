-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
-- name    : Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:47.993173+00:00
-- url     : https://prove2.me/theorems/be08456b-b311-45d4-aba5-fb1bcb6c99d6
-- title:
--   Statement O
-- statement:
--   Definitions and structural lemmas for Statement O, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/StatementO.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
def IsQuadBasis {W O : Type} [CommRing W] [CommRing O] (j : W →+* O) (θ w : O) : Prop :=
  ∀ x : O, ∃! t : W × W × W × W, x = j t.1 + j t.2.1 * θ + j t.2.2.1 * w + j t.2.2.2 * θ * w
def PresIso : Prop :=
  ∀ (W₁ W₂ O₁ O₂ : Type) [CommRing W₁] [CommRing W₂] [CommRing O₁] [CommRing O₂] (j₁ : W₁ →+* O₁) (j₂ : W₂ →+* O₂)
    (θ₁ w₁ : O₁) (θ₂ w₂ : O₂) (f0 f1 ϖ : W₁) (φW : W₁ ≃+* W₂),
    θ₁ ^ 2 + j₁ f1 * θ₁ + j₁ f0 = 0 → θ₂ ^ 2 + j₂ (φW f1) * θ₂ + j₂ (φW f0) = 0 →
    w₁ ^ 2 = j₁ ϖ → w₂ ^ 2 = j₂ (φW ϖ) → IsQuadBasis j₁ θ₁ w₁ → IsQuadBasis j₂ θ₂ w₂ →
    ∃ φO : O₁ ≃+* O₂, (∀ x, φO (j₁ x) = j₂ (φW x)) ∧ φO w₁ = w₂ ∧ φO θ₁ = θ₂
def QuadBasis : Prop :=
  ∀ (p n' : ℕ), p.Prime → ∀ (W O : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (j : W →+* O) (w θ : O), Irreducible (p : W) →
    Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n' → j.Finite → w ^ 2 = (p : O) → Irreducible w →
    Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n') → (∀ a : W, ¬ w ∣ θ - j a) → IsQuadBasis j θ w
def QuadRoots : Prop :=
  ∀ (p n' : ℕ), p.Prime → 0 < n' → ∀ (W₁ W₂ O₁ O₂ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁]
    [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁]
    [CommRing O₂] [IsDomain O₂] [IsDiscreteValuationRing O₂] (j₁ : W₁ →+* O₁) (j₂ : W₂ →+* O₂) (w₁ : O₁) (w₂ : O₂),
    Irreducible (p : W₁) → Irreducible (p : W₂) → Nat.card (W₁ ⧸ Ideal.span {(p : W₁)}) = p ^ n' →
    Nat.card (W₂ ⧸ Ideal.span {(p : W₂)}) = p ^ n' → IsAdicComplete (IsLocalRing.maximalIdeal O₁) O₁ →
    IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂ → w₁ ^ 2 = (p : O₁) → w₂ ^ 2 = (p : O₂) → Irreducible w₁ →
    Irreducible w₂ → Nat.card (O₁ ⧸ Ideal.span {w₁}) = p ^ (2 * n') → Nat.card (O₂ ⧸ Ideal.span {w₂}) = p ^ (2 * n') →
    ∀ φW : W₁ ≃+* W₂, ∃ (f0 f1 : W₁) (θ₁ : O₁) (θ₂ : O₂),
      θ₁ ^ 2 + j₁ f1 * θ₁ + j₁ f0 = 0 ∧ θ₂ ^ 2 + j₂ (φW f1) * θ₂ + j₂ (φW f0) = 0 ∧
      (∀ a : W₁, ¬ w₁ ∣ θ₁ - j₁ a) ∧ (∀ a : W₂, ¬ w₂ ∣ θ₂ - j₂ a)
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis


