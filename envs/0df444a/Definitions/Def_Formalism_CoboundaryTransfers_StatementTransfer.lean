-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_StatementTransfer
-- name    : Formalism_CoboundaryTransfers_StatementTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:25.372053+00:00
-- url     : https://prove2.me/theorems/01c5e37a-d394-4a37-8071-8d0d5d018b9b
-- title:
--   Statement Transfer
-- statement:
--   Definitions and structural lemmas for Statement Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/StatementTransfer.lean

import Definitions.Def_Formalism_CoboundaryTransfers_StatementBridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
def WBU : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ), B.φ B.X = B.X * B.Q → B.GammaX (u : ℤ_[ℓ]) → B.GammaQ →
    ∀ (D₁ D₂ : Type)
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (f : Hom W₁ W₂) (s H c : ℕ) (ε : A)
    (aa : Ideal A),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    Function.Injective B.φ →
    B.φ ε = ε ^ ℓ →
    (∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * B.φ (e i)) →
    (∀ a, a ∈ aa ↔ ∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N, f.f n₁ = a • n) →
    (∀ a ∈ aa, B.Q ^ H * a ∈ Ideal.map (B.φ : A →+* A) aa) →
    (ε - 1) ^ c ∈ aa →
    B.X ^ H ∈ aa ∧ ∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N,
      f.f n₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * H * s + padicValNat ℓ (2 * H).factorial)) • n
def UClaimU : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ), B.p = ℓ → B.φ B.X = B.X * B.Q → B.GammaX (u : ℤ_[ℓ]) → B.GammaQ →
    ∀ (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : WachMod B M D) (s : ℕ) (J : Finset ℤ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s → 0 ∉ J →
    (∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W.φ (B.X ^ (M + 1) • z)) →
    (∀ y, W.QInv y → B.X • y ∈ W.N → y ∈ W.N) →
    (∀ y, W.QInv y → Polynomial.aeval W.γ ((Polynomial.X - 1) *
      ∏ j ∈ J, (Polynomial.X - Polynomial.C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W.N) →
    (∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N) →
    W.TorsKilled ((∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
      ∏ i ∈ Finset.Icc 1 M, ((u : ℤ_[ℓ]) ^ i - 1))
def LemmaUU : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ), B.p = ℓ → B.φ B.X = B.X * B.Q → B.GammaX (u : ℤ_[ℓ]) → B.GammaQ →
    ∀ (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e s : ℕ) (J : Finset ℤ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s → 0 ∉ J →
    (∀ n ∈ W₀.N, ∃ z ∈ W₀.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W₀.φ (B.X ^ (M + 1) • z)) →
    (∀ y, W₀.QInv y → B.X • y ∈ W₀.N → y ∈ W₀.N) →
    (∀ y, W₀.QInv y → Polynomial.aeval W₀.γ ((Polynomial.X - 1) *
      ∏ j ∈ J, (Polynomial.X - Polynomial.C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W₀.N) →
    (∀ y, W₀.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W₀.N → y ∈ W₀.N) →
    CokerKilled S e → RatSurj S → Lifts S ((ℓ : ℤ_[ℓ]) ^ (e + LIFT.eU ℓ M s J))
end Formalism.CoboundaryTransfers


