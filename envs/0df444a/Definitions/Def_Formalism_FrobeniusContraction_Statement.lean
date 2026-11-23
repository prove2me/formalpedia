-- Prove2me | Definitions.Def_Formalism_FrobeniusContraction_Statement
-- name    : Formalism_FrobeniusContraction_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:42.18924+00:00
-- url     : https://prove2.me/theorems/22df802e-8ddc-431d-bf23-cb2f3a00d96b
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusContraction/Statement.lean

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
namespace Formalism.WachCohomologyFacts
structure Base (O A : Type) [CommRing O] [CommRing A] [Algebra O A] where
  ℓ : ℕ
  hℓ : ℓ.Prime
  X : A
  u : A
  c : A
  φ : A →ₐ[O] A
  γ : A →ₐ[O] A
  hu : IsUnit u
  hc : IsUnit c
  comm : ∀ a, φ (γ a) = γ (φ a)
  γ_bij : Function.Bijective γ
  hφX : φ X = u * X * (X + (ℓ : A)) ^ (ℓ - 1)
  hγX : γ X - X = c * X * (X + (ℓ : A))
  γ_modX : ∀ a, γ a - a ∈ Ideal.span {X}
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
def Base.q (B : Base O A) : A := B.X + (B.ℓ : A)
def Base.p (B : Base O A) (s : ℕ) : A := (⇑B.φ)^[s] B.q
def Base.I (B : Base O A) : Ideal A := Ideal.span {B.X, (B.ℓ : A)}
structure Amb (B : Base O A) (AA : Type) [CommRing AA] [Algebra O AA] [Algebra A AA]
    [IsScalarTower O A AA] where
  φ : AA →ₐ[O] AA
  γ : AA →ₐ[O] AA
  φ_ext : ∀ a : A, φ (algebraMap A AA a) = algebraMap A AA (B.φ a)
  γ_ext : ∀ a : A, γ (algebraMap A AA a) = algebraMap A AA (B.γ a)
  comm : ∀ a, φ (γ a) = γ (φ a)
  γ_bij : Function.Bijective γ
  hq : IsUnit (algebraMap A AA B.q)
  hX : IsUnit (algebraMap A AA B.X)
variable {AA : Type} [CommRing AA] [Algebra O AA] [Algebra A AA] [IsScalarTower O A AA]
structure WachDatum {B : Base O A} (E : Amb B AA) (n : ℕ) (V : Type) [AddCommGroup V] [Module AA V]
    [Module A V] [IsScalarTower A AA V] [Module O V] [IsScalarTower O AA V] where
  N : ZMod n → Submodule A V
  φ : ZMod n → V →ₗ[O] V
  γ : ZMod n → V →ₗ[O] V
  φ_smul : ∀ i (a : AA) (x : V), φ i (a • x) = E.φ a • φ i x
  γ_smul : ∀ i (a : AA) (x : V), γ i (a • x) = E.γ a • γ i x
  comm : ∀ i x, φ i (γ i x) = γ (i + 1) (φ i x)
  γ_bij : ∀ i, Function.Bijective (γ i)
  γ_N : ∀ i x, x ∈ N i ↔ γ i x ∈ N i
  γ_sub : ∀ i, ∀ x ∈ N i, ∃ x' ∈ N i, γ i x - x = B.X • x'
  N_span : ∀ i, Submodule.span AA (N i : Set V) = ⊤
  φ_span : ∀ i, Submodule.span AA (Set.range (φ i)) = ⊤
  φ_N : ∀ i, ∀ x ∈ N i, ∃ k : ℕ, B.q ^ k • φ i x ∈ N (i + 1)
  N_φ : ∀ i, ∀ y ∈ N (i + 1), ∃ k : ℕ, B.q ^ k • y ∈ Submodule.span A (φ i '' (N i : Set V))
namespace WachDatum
variable {B : Base O A} {E : Amb B AA} {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V]
variable (W : WachDatum E n V)
def Φ : (ZMod n → V) →ₗ[O] (ZMod n → V) :=
  LinearMap.pi (fun j => (W.φ (j - 1)).comp (LinearMap.proj (j - 1)))
def Γ : (ZMod n → V) →ₗ[O] (ZMod n → V) :=
  LinearMap.pi (fun j => (W.γ j).comp (LinearMap.proj j))
def Z1 : Submodule O ((ZMod n → V) × (ZMod n → V)) :=
  LinearMap.ker ((W.Γ - LinearMap.id).coprod (-(W.Φ - LinearMap.id)))
def B1 : Submodule O ((ZMod n → V) × (ZMod n → V)) :=
  LinearMap.range ((W.Φ - LinearMap.id).prod (W.Γ - LinearMap.id))
def IntRep (p : (ZMod n → V) × (ZMod n → V)) : Prop :=
  (∃ k : ℕ, ∀ j, B.q ^ k • p.1 j ∈ W.N j) ∧ ∀ j, ∃ m ∈ W.N j, p.2 j = B.X • m
def Zf : Submodule O ((ZMod n → V) × (ZMod n → V)) :=
  Submodule.span O {p | p ∈ W.Z1 ∧ ∃ a : ℕ, ∃ b ∈ W.B1, W.IntRep ((B.ℓ ^ a : ℕ) • p + b)} ⊔ W.B1
def XMN (M : ℕ) : Submodule A (ZMod n → V) :=
  Submodule.pi Set.univ (fun j => Ideal.span {B.X ^ M} • W.N j)
def FIN (g : ℕ) : Prop :=
  ∃ s : Finset ((ZMod n → V) × (ZMod n → V)), s.card ≤ g ∧
    Submodule.span O (s : Set ((ZMod n → V) × (ZMod n → V))) ⊔ W.B1 = W.Zf
end WachDatum
section Hom
variable {B : Base O A} {E : Amb B AA} {n : ℕ}
variable {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁]
variable {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂]
structure Hom (W₁ : WachDatum E n V₁) (W₂ : WachDatum E n V₂) where
  f : V₁ →ₗ[AA] V₂
  φ_comm : ∀ i x, f (W₁.φ i x) = W₂.φ i (f x)
  γ_comm : ∀ i x, f (W₁.γ i x) = W₂.γ i (f x)
  N_le : ∀ i, ∀ x ∈ W₁.N i, f x ∈ W₂.N i
namespace Hom
variable {W₁ : WachDatum E n V₁} {W₂ : WachDatum E n V₂} (h : Hom W₁ W₂)
def IsSurj : Prop :=
  Function.Surjective h.f ∧
    ∀ i, ∀ m ∈ W₂.N i, ∃ k : ℕ, ∃ m₁ ∈ W₁.N i, h.f m₁ = (B.ℓ ^ k : ℕ) • m
def fD : (ZMod n → V₁) →ₗ[O] (ZMod n → V₂) :=
  LinearMap.pi (fun j => (h.f.restrictScalars O).comp (LinearMap.proj j))
def Im : Submodule O ((ZMod n → V₂) × (ZMod n → V₂)) :=
  W₁.Zf.map (h.fD.prodMap h.fD) ⊔ W₂.B1
def col : ℕ∞ := Module.length O (↥W₂.Zf ⧸ h.Im.comap W₂.Zf.subtype)
def LIFT (e : ℕ) : Prop := ∀ p ∈ W₂.Zf, (B.ℓ ^ e : ℕ) • p ∈ h.Im
end Hom
end Hom
def PsModX : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (s : ℕ),
    B.p s - (B.ℓ : A) ∈ Ideal.span {B.X}
def PsCoprime : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (s t : ℕ), s < t →
    B.p t - (B.ℓ : A) ∈ Ideal.span {B.p s}
def PsModL : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (s : ℕ),
    ∃ v : A, IsUnit v ∧ B.p s - v * B.X ^ (B.ℓ ^ s) ∈ Ideal.span {(B.ℓ : A)}
def CobCoc : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V),
    W.B1 ≤ W.Z1 ∧ W.Zf ≤ W.Z1
def HomZf : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V₁ : Type) [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
    [Module O V₁] [IsScalarTower O AA V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
    [Module O V₂] [IsScalarTower O AA V₂]
    (W₁ : WachDatum E n V₁) (W₂ : WachDatum E n V₂) (h : Hom W₁ W₂),
    W₁.Z1.map (h.fD.prodMap h.fD) ≤ W₂.Z1 ∧ W₁.B1.map (h.fD.prodMap h.fD) ≤ W₂.B1 ∧
      W₁.Zf.map (h.fD.prodMap h.fD) ≤ W₂.Zf
def IncLocal : Prop :=
  ∀ (K R P : Type) [Field K] [CommRing R] [Algebra K R] [AddCommGroup P] [Module R P] [Module K P]
    [IsScalarTower K R P] (t : R) (τ : P ≃ₗ[R] P), (∀ x, τ x = t • x) →
    ∀ (D₀ : Submodule K P) (Fil : ℤ → Submodule K P) (a b : ℤ),
    Antitone Fil → (∀ u, Fil u ≤ D₀) → Fil (-a) = D₀ → Fil (b + 1) = ⊥ →
    let L' : Submodule R P := Submodule.span R (D₀ : Set P)
    let L : Submodule R P := ⨆ u : ℤ, (Submodule.span R (Fil u : Set P)).map (τ ^ (-u)).toLinearMap
    (∀ x ∈ L, (τ ^ b) x ∈ L') ∧ (∀ y ∈ L', (τ ^ a) y ∈ L)
def ContractBij : Prop :=
  ∀ (R P : Type) [CommRing R] [AddCommGroup P] [Module R P] (I : Ideal R) [IsAdicComplete I P]
    (f : P →+ P),
    (∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P)) →
    Function.Bijective (fun x => f x - x)
def PhiContract : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V) (M h : ℕ),
    1 ≤ M → 4 * h ≤ (B.ℓ - 1) * M → (∀ i, ∀ x ∈ W.N i, B.q ^ h • W.φ i x ∈ W.N (i + 1)) →
    ∀ k : ℕ, ∀ x ∈ B.I ^ k • W.XMN M, W.Φ x ∈ B.I ^ (k + 1) • W.XMN M
def F1 : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V) (M h : ℕ),
    1 ≤ M → 4 * h ≤ (B.ℓ - 1) * M → (∀ i, ∀ x ∈ W.N i, B.q ^ h • W.φ i x ∈ W.N (i + 1)) →
    IsAdicComplete B.I ↥(W.XMN M) →
    ∀ y ∈ W.XMN M, ∃! x, x ∈ W.XMN M ∧ W.Φ x - x = y
def FiniteCocycleOfIntegral : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V) (M h k : ℕ) (y : ZMod n → V),
    1 ≤ M → 4 * h ≤ (B.ℓ - 1) * M → (∀ i, ∀ x ∈ W.N i, B.q ^ h • W.φ i x ∈ W.N (i + 1)) →
    IsAdicComplete B.I ↥(W.XMN M) →
    (∀ j, B.q ^ k • y j ∈ W.N j) → W.Γ y - y ∈ W.XMN M →
    ∃ z ∈ W.XMN M, W.Φ z - z = W.Γ y - y ∧ (y, z) ∈ W.Zf
def TrivDatum : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n],
    ∃ T : WachDatum E n AA, (∀ i, T.N i = 1) ∧ (∀ i, ⇑(T.φ i) = ⇑E.φ) ∧ (∀ i, ⇑(T.γ i) = ⇑E.γ)
def ExtDatum : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V : Type) [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
    [IsScalarTower O AA V] (W : WachDatum E n V) (y z : ZMod n → V),
    (y, z) ∈ W.Z1 → W.IntRep (y, z) →
    ∃ Y : WachDatum E n (V × AA),
      (∀ i, Y.N i = (W.N i).prod (1 : Submodule A AA)) ∧
      (∀ i v a, Y.φ i (v, a) = (W.φ i v + E.φ a • y (i + 1), E.φ a)) ∧
      (∀ i v a, Y.γ i (v, a) = (W.γ i v + E.γ a • z i, E.γ a)) ∧
      (∀ i v, (v, (0 : AA)) ∈ Y.N i ↔ v ∈ W.N i) ∧
      (∃ ι : Hom W Y, ∀ v, ι.f v = (v, 0)) ∧
      (∀ T : WachDatum E n AA, (∀ i, T.N i = 1) → (∀ i, ⇑(T.φ i) = ⇑E.φ) →
        (∀ i, ⇑(T.γ i) = ⇑E.γ) → ∃ π : Hom Y T, (∀ x, π.f x = x.2) ∧ π.IsSurj)
def LenBound : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g e : ℕ)
    (Z Bc I : Submodule O M) (s : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})
def ColBound : Prop :=
  ∀ (O A AA : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
    [Algebra A AA] [IsScalarTower O A AA] (B : Base O A) (E : Amb B AA) (n : ℕ) [NeZero n]
    (V₁ : Type) [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
    [Module O V₁] [IsScalarTower O AA V₁]
    (V₂ : Type) [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
    [Module O V₂] [IsScalarTower O AA V₂]
    (W₁ : WachDatum E n V₁) (W₂ : WachDatum E n V₂) (h : Hom W₁ W₂) (g e : ℕ),
    W₂.FIN g → h.LIFT e →
    h.col ≤ (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(B.ℓ : O)})
end Formalism.WachCohomologyFacts


