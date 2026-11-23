-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
-- name    : Formalism_CoboundaryTransfers_StatementAPI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:56.562867+00:00
-- url     : https://prove2.me/theorems/93c639f2-848c-48c6-b1ad-738d4c4fb611
-- title:
--   Statement API
-- statement:
--   Definitions and structural lemmas for Statement API, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/StatementAPI.lean

import Definitions.Def_Formalism_CoboundaryTransfers_Statement
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
def Complex : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D),
    (∀ x ∈ W.N, W.C1 (W.φ x - x) (W.γ x - x)) ∧
    (∀ x, W.d1 (W.φ x - x) (W.γ x - x) = 0) ∧
    (∀ y z, W.C1 y z → W.C2 (W.d1 y z)) ∧
    (∀ y z, W.IsCob1 y z → W.Cocycle y z)
def Submods : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D),
    (∃ S : Submodule A D, ∀ y, y ∈ S ↔ W.QInv y) ∧
    (∃ S : Submodule A D, ∀ z, z ∈ S ↔ W.XN z) ∧
    (∃ S : Submodule A D, ∀ ω, ω ∈ S ↔ W.C2 ω) ∧
    (∃ S : Submodule O (D × D), ∀ y z, (y, z) ∈ S ↔ W.Cocycle y z) ∧
    (∃ S : Submodule O (D × D), ∀ y z, (y, z) ∈ S ↔ W.IsCob1 y z) ∧
    (∃ S : Submodule O D, ∀ ω, ω ∈ S ↔ W.IsCob2 ω) ∧
    (∀ n ∈ W.N, W.QInv n) ∧ (∀ z, W.XN z → z ∈ W.N)
def CocZf : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D),
    (∀ y z, W.Cocycle y z → (y, z) ∈ W.Zf) ∧ W.B1 ≤ W.Z1 ∧ W.Zf ≤ W.Z1 ∧
    (∀ y z, W.IsCob1 y z → (y, z) ∈ W.B1)
def HomMaps : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D D' : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
    (W : WachMod B M D) (W' : WachMod B M D') (F : Hom W W'),
    (∀ y, W.QInv y → W'.QInv (F.f y)) ∧ (∀ z, W.XN z → W'.XN (F.f z)) ∧
    (∀ ω, W.C2 ω → W'.C2 (F.f ω)) ∧ (∀ y z, F.f (W.d1 y z) = W'.d1 (F.f y) (F.f z)) ∧
    (∀ y z, W.Cocycle y z → W'.Cocycle (F.f y) (F.f z)) ∧
    (∀ y z, W.IsCob1 y z → W'.IsCob1 (F.f y) (F.f z)) ∧
    (∀ ω, W.IsCob2 ω → W'.IsCob2 (F.f ω)) ∧
    W.Z1.map F.f2 ≤ W'.Z1 ∧ W.B1.map F.f2 ≤ W'.B1 ∧ W.Zf.map F.f2 ≤ W'.Zf
def GammaQNOf : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (N : Submodule A D) (γ : D →ₗ[O] D),
    B.GammaQ → Function.Bijective (fun x : D => B.Q • x) →
    (∀ (a : A) (x : D), γ (a • x) = B.γ a • γ x) →
    (∀ x ∈ N, ∃ x' ∈ N, γ x - x = B.X • x') →
    ∀ y : D, B.Q ^ M • y ∈ N → ∃ y' : D, B.Q ^ M • y' ∈ N ∧ γ y - y = B.X • y'
def DiagramChase₂ : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e : ℕ) (c : O),
    CokerKilled S e → RatSurj S → W₀.TorsKilled c → Lifts S ((B.p : O) ^ e * c)
def CoboundaryTransfer : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a k : ℕ) (cΓ : O),
    B.PhiX k → M ≤ k * (a + 1) →
    (∀ y, B.X • δ y = W.γ y - y) →
    (∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N) →
    (∀ y, W.QInv y → (B.p : O) • y ∈ W.N → y ∈ W.N) →
    (∀ y, W.QInv y → cΓ • y ∈ W.N → y ∈ W.N) →
    (∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z') →
    (∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W.φ (B.X ^ (a + 1) • z)) →
    W.TorsKilled (R.eval 0 * cΓ)
def GradedStep : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D) (u : O), B.GammaX u → ∀ i : ℕ, ∀ n ∈ W.N, ∃ n' ∈ W.N,
      W.γ (B.X ^ i • n) - (u ^ i) • (B.X ^ i • n) = B.X ^ (i + 1) • n'
def GammaOnto : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D) (u : O) (a : ℕ),
    (∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W.N, ∃ n' ∈ W.N,
      W.γ (B.X ^ i • n) = u ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n') →
    ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)) • (B.X • n) =
        (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z'
def ColBound : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D D' : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
    (W : WachMod B M D) (W' : WachMod B M D') (F : Hom W W') (g e : ℕ),
    W'.FIN g → F.LiftF e →
    F.col ≤ (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(B.p : O)})
def LiftHf : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module O H₁] [AddCommGroup H₂] [Module O H₂]
    (cl₁ : W₁.Z1 →ₗ[O] H₁) (cl₂ : W₂.Z1 →ₗ[O] H₂) (Hf₁ : Submodule O H₁)
    (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (eW : ℕ) (c : O),
    ClNat S.π cl₁ cl₂ g →
    (∀ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 → cl₁ pr ∈ Hf₁) →
    HfInt W₂ cl₂ Hf₂ eW → Lifts S c →
    ∀ κ ∈ Hf₂, ∃ κ₁ ∈ Hf₁, g κ₁ = ((B.p : O) ^ eW * c) • κ
def Mono : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M M' : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D), M ≤ M' → B.GammaQ →
    ∃ W' : WachMod B M' D, W'.N = W.N ∧ W'.φ = W.φ ∧ W'.γ = W.γ
def IntDefs : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D),
    (∀ y, y ∈ W.QInvSub ↔ W.QInv y) ∧ (∀ z, z ∈ W.XNSub ↔ W.XN z) ∧
    (∀ y z, (y, z) ∈ W.ZInt ↔ W.Cocycle y z) ∧ (∀ y z, (y, z) ∈ W.BInt ↔ W.IsCob1 y z) ∧
    W.BInt ≤ W.ZInt ∧ W.BInt ≤ W.B1 ∧ W.ZInt ≤ W.Zf
def NonemptyQ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ (B : Base ℤ_[p] (Polynomial ℤ_[p]))
    (W : WachMod B 0 (FractionRing (Polynomial ℤ_[p]))),
    B.p = p ∧ W.N ≠ ⊥ ∧ ¬ IsUnit B.X ∧ ¬ IsUnit B.Q ∧ B.QLin ∧ B.PhiX (p - 1)
def NonemptyU : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ), ∃ (B : Base ℤ_[p] (Polynomial ℤ_[p]))
    (W : WachMod B 0 (Polynomial ℤ_[p])),
    B.p = p ∧ W.N ≠ ⊥ ∧ ¬ IsUnit B.X ∧ B.GammaX (u : ℤ_[p]) ∧ B.GammaQ
end Formalism.CoboundaryTransfers


