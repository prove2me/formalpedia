-- Prove2me | Definitions.Def_Formalism_LagrangeIdealLifts_Statement
-- name    : Formalism_LagrangeIdealLifts_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:49.868259+00:00
-- url     : https://prove2.me/theorems/ef805e12-003f-48fc-ae9a-d8739f6be4ac
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/Statement.lean

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
namespace Formalism.LIFT
def LagrangeIdeal : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ℓ : R) (ι : Type) [DecidableEq ι]
    (S₁ S₂ : Finset ι) (c : ι → R) (w : ι → ι → ℕ),
    Disjoint S₁ S₂ →
    (∀ a ∈ S₁, ∀ b ∈ S₁ ∪ S₂, a ≠ b → Associated (c a - c b) (ℓ ^ w a b)) →
    Polynomial.C (ℓ ^ (S₁.sup fun a => (∑ b ∈ S₂, w a b) + ∑ a' ∈ S₁.erase a, w a a')) ∈
      Ideal.span ({∏ a ∈ S₁, (Polynomial.X - Polynomial.C (c a)),
        ∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))} : Set (Polynomial R))
def LagrangeIdealInt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Type) [CommRing R] [IsDomain R] (S₁ S₂ : Finset ℤ) (c : ℤ → R),
    Disjoint S₁ S₂ →
    (∀ a ∈ S₁, ∀ b ∈ S₁ ∪ S₂, a ≠ b →
      Associated (c a - c b) ((ℓ : R) ^ padicValInt ℓ (a - b))) →
    Polynomial.C ((ℓ : R) ^ (S₁.sup fun a =>
        (∑ b ∈ S₂, padicValInt ℓ (a - b)) + ∑ a' ∈ S₁.erase a, padicValInt ℓ (a - a'))) ∈
      Ideal.span ({∏ a ∈ S₁, (Polynomial.X - Polynomial.C (c a)),
        ∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))} : Set (Polynomial R))
def LagrangeIdealCyc : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s → ∀ a : ℕ,
    Polynomial.C ((ℓ : ℤ_[ℓ]) ^ (2 * a * s + padicValNat ℓ (2 * a).factorial)) ∈
      Ideal.span ({∏ i ∈ Finset.range a, (Polynomial.X - Polynomial.C ((u : ℤ_[ℓ]) ^ i)),
        ∏ i ∈ Finset.Ico a (2 * a), (Polynomial.X - Polynomial.C ((u : ℤ_[ℓ]) ^ i))} :
        Set (Polynomial ℤ_[ℓ]))
structure Base (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] where
  φA : A →ₐ[ℤ_[ℓ]] A
  γA : A →ₐ[ℤ_[ℓ]] A
  X : A
  Q : A
  u : ℤ_[ℓ]ˣ
  comm : ∀ a, φA (γA a) = γA (φA a)
  φX : φA X = X * Q
  γX : ∃ t : A, γA X = X * (algebraMap ℤ_[ℓ] A (u : ℤ_[ℓ]) + X * t)
  γQ : ∃ t : A, IsUnit (1 + X * t) ∧ γA Q = Q * (1 + X * t)
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
structure WD (B : Base ℓ A) (M : ℕ) (D : Type) [AddCommGroup D] [Module A D]
    [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D] where
  N : Submodule A D
  φ : D →ₗ[ℤ_[ℓ]] D
  γ : D →ₗ[ℤ_[ℓ]] D
  φ_smul : ∀ (a : A) (x : D), φ (a • x) = B.φA a • φ x
  γ_smul : ∀ (a : A) (x : D), γ (a • x) = B.γA a • γ x
  comm : ∀ x, φ (γ x) = γ (φ x)
  X_inj : ∀ x : D, B.X • x = 0 → x = 0
  Q_bij : Function.Bijective (fun x : D => B.Q • x)
  φ_N : ∀ x ∈ N, B.Q ^ M • φ x ∈ N
  γ_N : ∀ x ∈ N, ∃ x' ∈ N, γ x - x = B.X • x'
namespace WD
variable {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)
def QInv (y : D) : Prop := B.Q ^ M • y ∈ W.N
def XN (z : D) : Prop := ∃ n ∈ W.N, z = B.X • n
def C1 (y z : D) : Prop := W.QInv y ∧ W.XN z
def C2 (ω : D) : Prop := ∃ y, W.QInv y ∧ ω = B.X • y
def d1 (y z : D) : D := (W.γ y - y) - (W.φ z - z)
def Cocycle (y z : D) : Prop := W.C1 y z ∧ W.d1 y z = 0
def IsCob2 (ω : D) : Prop := ∃ y z, W.C1 y z ∧ ω = W.d1 y z
def TorsKilled (c : ℤ_[ℓ]) : Prop :=
  ∀ ω, W.C2 ω → (∃ k : ℕ, W.IsCob2 (((ℓ : ℤ_[ℓ]) ^ k) • ω)) → W.IsCob2 (c • ω)
end WD
variable {B : Base ℓ A} {M : ℕ}
structure Hom {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A D']
    (W : WD B M D) (W' : WD B M D') where
  f : D →ₗ[A] D'
  φ_comm : ∀ x, f (W.φ x) = W'.φ (f x)
  γ_comm : ∀ x, f (W.γ x) = W'.γ (f x)
  N_le : ∀ x ∈ W.N, f x ∈ W'.N
structure SES {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WD B M D₀) (W₁ : WD B M D₁) (W₂ : WD B M D₂) where
  ι : Hom W₀ W₁
  π : Hom W₁ W₂
  ι_inj : Function.Injective ι.f
  exact : ∀ x, π.f x = 0 ↔ ∃ x₀, ι.f x₀ = x
  sat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N
section Hyp
variable {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : WD B M D₀} {W₁ : WD B M D₁} {W₂ : WD B M D₂}
def CokerKilled (S : SES W₀ W₁ W₂) (e : ℕ) : Prop :=
  ∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N, S.π.f n₁ = ((ℓ : ℤ_[ℓ]) ^ e) • n
def RatSurj (S : SES W₀ W₁ W₂) : Prop :=
  ∀ y z, W₂.Cocycle y z → ∃ k : ℕ, ∃ y₁ z₁, W₁.Cocycle y₁ z₁ ∧ ∃ x ∈ W₂.N,
    S.π.f y₁ = ((ℓ : ℤ_[ℓ]) ^ k) • y + (W₂.φ x - x) ∧
    S.π.f z₁ = ((ℓ : ℤ_[ℓ]) ^ k) • z + (W₂.γ x - x)
def Lifts (S : SES W₀ W₁ W₂) (c : ℤ_[ℓ]) : Prop :=
  ∀ y z, W₂.Cocycle y z → ∃ y₁ z₁, W₁.Cocycle y₁ z₁ ∧ S.π.f y₁ = c • y ∧ S.π.f z₁ = c • z
end Hyp
def GradedStep : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℓ A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : WD B M D) (i : ℕ), ∀ n ∈ W.N, ∃ n' ∈ W.N,
      W.γ (B.X ^ i • n) - ((B.u : ℤ_[ℓ]) ^ i) • (B.X ^ i • n) = B.X ^ (i + 1) • n'
def WBTail : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℓ A) (M : ℕ)
    (D₁ D₂ : Type)
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₁ : WD B M D₁) (W₂ : WD B M D₂) (f : Hom W₁ W₂) (s a : ℕ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((B.u : ℤ_[ℓ]) - 1) = s →
    (∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N, f.f n₁ = B.X ^ a • n) →
    ∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N,
      f.f n₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * a * s + padicValNat ℓ (2 * a).factorial)) • n
def XHKills : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] (φA : A →+* A) (ε X Q : A) (H c : ℕ)
    (aa : Ideal A),
    Function.Injective φA →
    φA ε = ε ^ ℓ →
    (∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) →
    φA X = X * Q →
    (∀ a ∈ aa, Q ^ H * a ∈ Ideal.map φA aa) →
    (ε - 1) ^ c ∈ aa →
    X ^ H ∈ aa
def WB : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℓ A) (M : ℕ)
    (D₁ D₂ : Type)
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₁ : WD B M D₁) (W₂ : WD B M D₂) (f : Hom W₁ W₂) (s H c : ℕ) (ε : A) (aa : Ideal A),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((B.u : ℤ_[ℓ]) - 1) = s →
    Function.Injective B.φA →
    B.φA ε = ε ^ ℓ →
    (∀ g : A, ∃! e : Fin ℓ → A, g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * B.φA (e i)) →
    (∀ a, a ∈ aa ↔ ∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N, f.f n₁ = a • n) →
    (∀ a ∈ aa, B.Q ^ H * a ∈ Ideal.map (B.φA : A →+* A) aa) →
    (ε - 1) ^ c ∈ aa →
    B.X ^ H ∈ aa ∧ ∀ n ∈ W₂.N, ∃ n₁ ∈ W₁.N,
      f.f n₁ = ((ℓ : ℤ_[ℓ]) ^ (2 * H * s + padicValNat ℓ (2 * H).factorial)) • n
def GapDLift : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] (A₀ : Type) [CommRing A₀]
    [Algebra O A₀] (D₁ D₂ : Type)
    [AddCommGroup D₁] [Module A₀ D₁] [Module O D₁] [IsScalarTower O A₀ D₁]
    [AddCommGroup D₂] [Module A₀ D₂] [Module O D₂] [IsScalarTower O A₀ D₂]
    (N₁ : Submodule A₀ D₁) (N₂ : Submodule A₀ D₂) (q : A₀) (d₁ : D₁ →ₗ[O] D₁)
    (d₂ : D₂ →ₗ[O] D₂) (f : D₁ →ₗ[A₀] D₂) (a : ℕ) (S₁ S₂ : Finset ℤ) (c : ℤ → O) (x : D₂),
    Function.Bijective (fun y : D₁ => q • y) →
    (∀ y : D₂, q • y = 0 → y = 0) →
    (∀ y, f (d₁ y) = d₂ (f y)) →
    (∀ y ∈ N₁, d₁ y ∈ N₁) →
    (∀ y ∈ N₁, f y ∈ N₂) →
    (∀ n ∈ N₂, ∃ n₁ ∈ N₁, f n₁ = q ^ a • n) →
    Disjoint S₁ S₂ →
    (∀ b ∈ S₁, ∀ b' ∈ S₁ ∪ S₂, b ≠ b' →
      Associated (c b - c b') ((ℓ : O) ^ padicValInt ℓ (b - b'))) →
    (∀ y : D₁, q ^ a • y ∈ N₁ →
      Polynomial.aeval d₁ (∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))) y ∈ N₁) →
    x ∈ N₂ →
    (∃ n ∈ N₂, Polynomial.aeval d₂ (∏ b ∈ S₁, (Polynomial.X - Polynomial.C (c b))) x = q ^ a • n) →
    ∃ n₁ ∈ N₁, f n₁ = ((ℓ : O) ^ (S₁.sup fun b =>
        (∑ b' ∈ S₂, padicValInt ℓ (b - b')) + ∑ b' ∈ S₁.erase b, padicValInt ℓ (b - b'))) • x
def h0c (ℓ m : ℕ) (U : Finset ℤ) : ℕ := ∑ a ∈ U, (m + padicValInt ℓ a)
def lagrangeIdealLifts_fact_alt : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ), 0 ∉ U →
    ∀ (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V),
    Polynomial.aeval g (∏ a ∈ U, (Polynomial.X - Polynomial.C (((u ^ a : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) = 0 →
    (∀ x : V, ∃ y : V, ((ℓ : ℤ_[ℓ]) ^ h0c ℓ m U) • x = g y - y) ∧
    (∀ (r : ℕ) (x y : V), g x - x = ((ℓ : ℤ_[ℓ]) ^ r) • y →
      ∃ z : V, ((ℓ : ℤ_[ℓ]) ^ h0c ℓ m U) • x = ((ℓ : ℤ_[ℓ]) ^ r) • z) ∧
    ((∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) → ∀ x : V, g x = x → x = 0)
def lagrangeIdealLifts_fact : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ), 0 ∉ U →
    ∀ (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V),
    Polynomial.aeval g (∏ a ∈ U, (Polynomial.X - Polynomial.C (((u ^ a : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) = 0 →
    ∀ (r C : ℕ) (Mo : Type) [AddCommGroup Mo]
      (α : Mo →+ V ⧸ LinearMap.range (((ℓ : ℤ_[ℓ]) ^ r) • (LinearMap.id : V →ₗ[ℤ_[ℓ]] V))),
    (∀ (mo : Mo) (v : V), α mo = Submodule.Quotient.mk v → ∃ y : V, g v - v = ((ℓ : ℤ_[ℓ]) ^ r) • y) →
    (∀ mo : Mo, α mo = 0 → (ℓ ^ C) • mo = 0) →
    ∀ mo : Mo, (ℓ ^ (h0c ℓ m U + C)) • mo = 0
def TorsCard : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (Y : Type) [AddCommGroup Y] (Mo : AddSubgroup Y) (N : ℕ),
    Finite {y : Y // ℓ • y = 0} →
    (∀ y ∈ Mo, (ℓ ^ N) • y = 0) →
    Nat.card Mo ≤ Nat.card {y : Y // ℓ • y = 0} ^ N
def UGraded : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℓ A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : WD B M D) (K : ℕ), ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ n' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 K, ((B.u : ℤ_[ℓ]) ^ i - 1)) • (B.X • n) =
        (W.γ (B.X • x) - B.X • x) + B.X ^ (K + 1) • n'
def UClaim : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℓ A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : WD B M D) (s : ℕ) (J : Finset ℤ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((B.u : ℤ_[ℓ]) - 1) = s → 0 ∉ J →
    (∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W.φ (B.X ^ (M + 1) • z)) →
    (∀ y, W.QInv y → B.X • y ∈ W.N → y ∈ W.N) →
    (∀ y, W.QInv y → Polynomial.aeval W.γ ((Polynomial.X - 1) *
      ∏ j ∈ J, (Polynomial.X - Polynomial.C (((B.u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W.N) →
    (∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N) →
    W.TorsKilled ((∏ j ∈ J, (1 - ((B.u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
      ∏ i ∈ Finset.Icc 1 M, ((B.u : ℤ_[ℓ]) ^ i - 1))
def UChase : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℓ A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WD B M D₀) (W₁ : WD B M D₁) (W₂ : WD B M D₂) (S : SES W₀ W₁ W₂) (e : ℕ) (c : ℤ_[ℓ]),
    CokerKilled S e → RatSurj S → W₀.TorsKilled c → Lifts S (((ℓ : ℤ_[ℓ]) ^ e) * c)
def eU (ℓ M s : ℕ) (J : Finset ℤ) : ℕ :=
  (∑ j ∈ J, (s + padicValInt ℓ j)) + M * s + padicValNat ℓ M.factorial
def LemmaU : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℓ A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WD B M D₀) (W₁ : WD B M D₁) (W₂ : WD B M D₂) (S : SES W₀ W₁ W₂) (e s : ℕ) (J : Finset ℤ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((B.u : ℤ_[ℓ]) - 1) = s → 0 ∉ J →
    (∀ n ∈ W₀.N, ∃ z ∈ W₀.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W₀.φ (B.X ^ (M + 1) • z)) →
    (∀ y, W₀.QInv y → B.X • y ∈ W₀.N → y ∈ W₀.N) →
    (∀ y, W₀.QInv y → Polynomial.aeval W₀.γ ((Polynomial.X - 1) *
      ∏ j ∈ J, (Polynomial.X - Polynomial.C (((B.u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W₀.N) →
    (∀ y, W₀.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W₀.N → y ∈ W₀.N) →
    CokerKilled S e → RatSurj S → Lifts S ((ℓ : ℤ_[ℓ]) ^ (e + eU ℓ M s J))
def LiftAbstract : Prop :=
  ∀ (H₁ H₂ Z₁ Z₂ : Type) [AddCommGroup H₁] [AddCommGroup H₂] [AddCommGroup Z₁] [AddCommGroup Z₂]
    (h : H₁ →+ H₂) (ζ : Z₁ →+ Z₂) (cl₁ : Z₁ →+ H₁) (cl₂ : Z₂ →+ H₂) (ℓ eW eU : ℕ),
    (∀ z, h (cl₁ z) = cl₂ (ζ z)) →
    (∀ κ, ∃ z, cl₂ z = (ℓ ^ eW) • κ) →
    (∀ z, ∃ z₁, ζ z₁ = (ℓ ^ (eW + eU)) • z) →
    ∀ κ, ∃ κ₁, h κ₁ = (ℓ ^ (2 * eW + eU)) • κ
def LiftDescent : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H₁ H₂ H₁' H₂' : Type)
    [AddCommGroup H₁] [Module ℤ_[ℓ] H₁] [AddCommGroup H₂] [Module ℤ_[ℓ] H₂]
    [AddCommGroup H₁'] [Module ℤ_[ℓ] H₁'] [AddCommGroup H₂'] [Module ℤ_[ℓ] H₂']
    (h : H₁ →ₗ[ℤ_[ℓ]] H₂) (h' : H₁' →ₗ[ℤ_[ℓ]] H₂') (res₂ : H₂' →ₗ[ℤ_[ℓ]] H₂)
    (cor₁ : H₁ →ₗ[ℤ_[ℓ]] H₁') (cor₂ : H₂ →ₗ[ℤ_[ℓ]] H₂') (g E : ℕ),
    0 < g →
    (∀ x, cor₂ (res₂ x) = (g : ℤ_[ℓ]) • x) →
    (∀ x, h' (cor₁ x) = cor₂ (h x)) →
    (∀ κ, ∃ κ₁, h κ₁ = ((ℓ : ℤ_[ℓ]) ^ E) • κ) →
    ∀ κ', ∃ κ₁', h' κ₁' = ((ℓ : ℤ_[ℓ]) ^ (E + padicValNat ℓ g)) • κ'
def WDNonempty : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ), ∃ (B : Base ℓ (Polynomial ℤ_[ℓ]))
    (W : WD B 0 (Polynomial ℤ_[ℓ])), B.u = u ∧ W.N ≠ ⊥ ∧ ¬ IsUnit B.X
def PhiSideNonempty : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (φA : Polynomial ℤ_[ℓ] →+* Polynomial ℤ_[ℓ]) (ε X Q : Polynomial ℤ_[ℓ]),
    Function.Injective φA ∧ φA ε = ε ^ ℓ ∧
    (∀ g : Polynomial ℤ_[ℓ], ∃! e : Fin ℓ → Polynomial ℤ_[ℓ], g = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)) ∧
    φA X = X * Q ∧ ¬ IsUnit X ∧ ¬ IsUnit Q
end Formalism.LIFT


