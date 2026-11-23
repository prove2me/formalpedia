-- Prove2me | Definitions.Def_Formalism_WachModuleLifts_StatementW
-- name    : Formalism_WachModuleLifts_StatementW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:19.476922+00:00
-- url     : https://prove2.me/theorems/89a1850c-6e21-4056-a5bb-b34c7da9dc09
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachModuleLifts/StatementW.lean

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
namespace Formalism.CL.W
structure Base (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] where
  φA : A →ₐ[ℤ_[p]] A
  γA : A →ₐ[ℤ_[p]] A
  π₀ : A
  q : A
  hq : q = π₀ + algebraMap ℤ_[p] A p
  hφ : ∃ v : A, φA π₀ = π₀ * q ^ (p - 1) * v
  comm : ∀ a, φA (γA a) = γA (φA a)
variable {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]
structure WachMod (B : Base p A) (η : ℕ) (D : Type) [AddCommGroup D] [Module A D]
    [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D] where
  N : Submodule A D
  φ : D →ₗ[ℤ_[p]] D
  γ : D →ₗ[ℤ_[p]] D
  φ_smul : ∀ (a : A) (x : D), φ (a • x) = B.φA a • φ x
  γ_smul : ∀ (a : A) (x : D), γ (a • x) = B.γA a • γ x
  comm : ∀ x, φ (γ x) = γ (φ x)
  π₀_inj : ∀ x : D, B.π₀ • x = 0 → x = 0
  q_bij : Function.Bijective (fun x : D => B.q • x)
  φ_N : ∀ x ∈ N, B.q ^ η • φ x ∈ N
  γ_N : ∀ x ∈ N, ∃ x' ∈ N, γ x - x = B.π₀ • x'
  γ_qN : ∀ y : D, B.q ^ η • y ∈ N → ∃ y' : D, B.q ^ η • y' ∈ N ∧ γ y - y = B.π₀ • y'
namespace WachMod
variable {B : Base p A} {η : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D]
  [IsScalarTower ℤ_[p] A D] (W : WachMod B η D)
def QInv (y : D) : Prop := B.q ^ η • y ∈ W.N
def C1 (y z : D) : Prop := W.QInv y ∧ ∃ n ∈ W.N, z = B.π₀ • n
def C2 (ω : D) : Prop := ∃ y, W.QInv y ∧ ω = B.π₀ • y
def d1 (y z : D) : D := (W.γ y - y) - (W.φ z - z)
def Cocycle (y z : D) : Prop := W.C1 y z ∧ W.d1 y z = 0
def IsCob2 (ω : D) : Prop := ∃ y z, W.C1 y z ∧ ω = W.d1 y z
end WachMod
variable {B : Base p A} {η : ℕ}
structure Hom {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']
    (W : WachMod B η D) (W' : WachMod B η D') where
  f : D →ₗ[A] D'
  φ_comm : ∀ x, f (W.φ x) = W'.φ (f x)
  γ_comm : ∀ x, f (W.γ x) = W'.γ (f x)
  N_le : ∀ x ∈ W.N, f x ∈ W'.N
structure SES {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[p] D₀] [IsScalarTower ℤ_[p] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[p] D₁] [IsScalarTower ℤ_[p] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[p] D₂] [IsScalarTower ℤ_[p] A D₂]
    (W₀ : WachMod B η D₀) (W₁ : WachMod B η D₁) (W₂ : WachMod B η D₂) where
  ι : Hom W₀ W₁
  π : Hom W₁ W₂
  ι_inj : Function.Injective ι.f
  exact : ∀ x, π.f x = 0 ↔ ∃ x₀, ι.f x₀ = x
  π_surj : Function.Surjective π.f
  sat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N
section Hyp
variable {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[p] D₀] [IsScalarTower ℤ_[p] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[p] D₁] [IsScalarTower ℤ_[p] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[p] D₂] [IsScalarTower ℤ_[p] A D₂]
    {W₀ : WachMod B η D₀} {W₁ : WachMod B η D₁} {W₂ : WachMod B η D₂}
def CokerKilled (S : SES W₀ W₁ W₂) (e : ℕ) : Prop :=
  ∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N, S.π.f n₁ = (p : ℤ_[p]) ^ e • n
def RatSurj (S : SES W₀ W₁ W₂) : Prop :=
  ∀ y z, W₂.Cocycle y z → ∃ k : ℕ, ∃ y₁ z₁, W₁.Cocycle y₁ z₁ ∧ ∃ x ∈ W₂.N,
    S.π.f y₁ = (p : ℤ_[p]) ^ k • y + (W₂.φ x - x) ∧ S.π.f z₁ = (p : ℤ_[p]) ^ k • z + (W₂.γ x - x)
def Lifts (S : SES W₀ W₁ W₂) (c : ℤ_[p]) : Prop :=
  ∀ y z, W₂.Cocycle y z → ∃ y₁ z₁, W₁.Cocycle y₁ z₁ ∧ S.π.f y₁ = c • y ∧ S.π.f z₁ = c • z
end Hyp
def TorsKilled {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (c : ℤ_[p]) : Prop :=
  ∀ ω, W.C2 ω → (∃ k : ℕ, W.IsCob2 ((p : ℤ_[p]) ^ k • ω)) → W.IsCob2 (c • ω)
def LiftW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : Base p A) (η : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[p] D₀] [IsScalarTower ℤ_[p] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[p] D₁] [IsScalarTower ℤ_[p] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[p] D₂] [IsScalarTower ℤ_[p] A D₂]
    (W₀ : WachMod B η D₀) (W₁ : WachMod B η D₁) (W₂ : WachMod B η D₂) (S : SES W₀ W₁ W₂)
    (e : ℕ) (c : ℤ_[p]),
    CokerKilled S e → RatSurj S → TorsKilled W₀ c → Lifts S ((p : ℤ_[p]) ^ e * c)
def ClaimW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : Base p A) (η : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (δ : D →ₗ[ℤ_[p]] D) (R : Polynomial ℤ_[p]) (a : ℕ) (cΓ : ℤ_[p]),
    η ≤ (p - 1) * (a + 1) →
    (∀ y, B.π₀ • δ y = W.γ y - y) →
    (∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N) →
    (∀ y, W.QInv y → (p : ℤ_[p]) • y ∈ W.N → y ∈ W.N) →
    cΓ ≠ 0 →
    (∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.π₀ • n) = (W.γ (B.π₀ • x) - B.π₀ • x) + B.π₀ ^ (a + 1) • z') →
    (∀ n ∈ W.N, ∃ z ∈ W.N, B.π₀ ^ (a + 1) • n = B.π₀ ^ (a + 1) • z - W.φ (B.π₀ ^ (a + 1) • z)) →
    TorsKilled W (R.eval 0 * cΓ)
def GammaOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : Base p A) (η : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (u : ℤ_[p]) (a : ℕ),
    (∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W.N, ∃ n' ∈ W.N,
      W.γ (B.π₀ ^ i • n) = u ^ i • (B.π₀ ^ i • n) + B.π₀ ^ (i + 1) • n') →
    ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)) • (B.π₀ • n) =
        (W.γ (B.π₀ • x) - B.π₀ • x) + B.π₀ ^ (a + 1) • z'
def polyBase (p : ℕ) [Fact p.Prime] : Base p (Polynomial ℤ_[p]) where
  φA := Polynomial.aeval (Polynomial.X * (Polynomial.X + Polynomial.C (p : ℤ_[p])) ^ (p - 1))
  γA := AlgHom.id ℤ_[p] _
  π₀ := Polynomial.X
  q := Polynomial.X + Polynomial.C (p : ℤ_[p])
  hq := by simp [Polynomial.algebraMap_apply]
  hφ := ⟨1, by simp⟩
  comm := fun _ => rfl
def WachNonempty : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∃ W : WachMod (polyBase p) 0 (FractionRing (Polynomial ℤ_[p])),
    W.N ≠ ⊥ ∧ ¬ IsUnit (polyBase p).π₀
end Formalism.CL.W


