-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteEpsilonOperator
-- name    : Formalism_LocalToGlobal_IndefiniteReal_IndefiniteEpsilonOperator
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:39.650034+00:00
-- url     : https://prove2.me/theorems/25255bd5-5544-4796-8635-cd82e564a864
-- title:
--   Indefinite Epsilon Operator
-- statement:
--   Definitions and structural lemmas for Indefinite Epsilon Operator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/IndefiniteEpsilonOperator.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.IndefR.IndefiniteEpsilonOperator
structure Pair (G K : Type) [Group G] [Field K] where

  H : Subgroup G

  χ : H →* Kˣ
section Ops
variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [AddCommGroup U] [Module K U]
def epOp [Finite G] (σ : Representation K G U) (P : Pair G K) : U →ₗ[K] U :=
  letI : Fintype P.H := Fintype.ofFinite P.H
  (Nat.card P.H : K)⁻¹ • ∑ h : P.H, ((P.χ h⁻¹ : Kˣ) : K) • σ (h : G)
def epSp [Finite G] (σ : Representation K G U) (P : Pair G K) : Submodule K U :=
  LinearMap.range (epOp σ P)
def charOf (σ : Representation K G U) (g : G) : K :=
  LinearMap.trace K U (σ g)
def eOp [Fintype G] {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W)
    (ρ : Representation K G U) : U →ₗ[K] U :=
  (charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, charOf τ x⁻¹ • ρ x
def nOf [Finite G] {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W)
    (P : Pair G K) : ℕ :=
  finrank K (epSp τ P)
end Ops
def la (G : Type) [Fintype G] : ℝ := Real.log (Fintype.card G)
section Lat
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
  [Fintype κ] [DecidableEq κ]
def latAt {G : Type} [Group G] [Finite G] (ρ : Representation K G V) (A : Submodule (𝓞 K) V)
    (P : Pair G K) : Submodule (𝓞 K) V :=
  A ⊓ (epSp ρ P).restrictScalars (𝓞 K)
def HtLe (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) (U : Submodule K V) (t : ℝ) : Prop :=
  ∃ c : InfinitePlace K → ℝ, (∀ v, 0 < c v) ∧
    (∀ v, ∀ x ∈ U, Formalism.HermitianLatticesTheory.normAt b' X' v (φ x) ≤ c v * Formalism.HermitianLatticesTheory.normAt b X v x) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (c v ^ 2) ≤ t
def CKa (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (RPl : Submodule (𝓞 K) V)
    (bP : Basis κ K W) (XP : InfinitePlace K → Matrix κ κ ℂ) (RP : Submodule (𝓞 K) W) (t : ℝ) :
    Prop :=
  (∀ v, IsUnit (XP v).det) ∧ RP.FG ∧ Submodule.span K (RP : Set W) = ⊤ ∧
  (∃ φ : W →ₗ[K] V, (∀ x ∈ RP, φ x ∈ RPl) ∧ Set.InjOn φ (RP : Set W) ∧
    HtLe bP XP b X φ (Submodule.span K (RP : Set W)) t) ∧
  (∃ ψ : V →ₗ[K] W, (∀ x ∈ RPl, ψ x ∈ RP) ∧ Set.InjOn ψ (RPl : Set V) ∧
    HtLe b X bP XP ψ (Submodule.span K (RPl : Set V)) t)
def muDual (bP : Basis κ K W) (XP : InfinitePlace K → Matrix κ κ ℂ) (RP : Submodule (𝓞 K) W) : ℝ :=
  Formalism.HN.muDef bP.dualBasis (Formalism.HN.dualFrame XP) (Formalism.HN.dualLat RP)
structure GoodTransferSetting {G : Type} [Group G] [Fintype G] {S : Type} [Fintype S] {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V)
    (R : Submodule (𝓞 K) V) (τ : ∀ s, Representation K G (Ws s)) : Prop where

  frame : ∀ v, IsUnit (X v).det

  fg : R.FG

  span : Submodule.span K (R : Set V) = ⊤

  ne_bot : R ≠ ⊥

  roots : ∃ ζ : K, IsPrimitiveRoot ζ (Fintype.card G)

  stable : ∀ g : G, ∀ x ∈ R, ρ g x ∈ R

  unitary : ∀ (g : G) (v : InfinitePlace K) (x : V),
    Formalism.HermitianLatticesTheory.normAt b X v (ρ g x) = Formalism.HermitianLatticesTheory.normAt b X v x

  irred : ∀ s, (τ s).IsIrreducible

  split : ∀ s (f : Ws s →ₗ[K] Ws s), (∀ g, f ∘ₗ τ s g = τ s g ∘ₗ f) → ∃ c : K, f = c • LinearMap.id

  distinct : Function.Injective fun s => charOf (τ s)

  good : ∀ x : V, (∑ s, eOp (τ s) ρ) x = x
end Lat
def M1 {K : Type} [Field K] {G : Type} [Group G] [Finite G] {S : Type} {Ws : S → Type}
    [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)] (τ : ∀ s, Representation K G (Ws s))
    (P0 : Pair G K) : Prop :=
  ∀ s, nOf (τ s) P0 = 1
def M2 {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V]
    [Module K V] {S : Type} {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (ρ : Representation K G V) (τ : ∀ s, Representation K G (Ws s)) (P1 : Pair G K)
    (nbar de : ℝ) : Prop :=
  ∀ s, LinearMap.range (eOp (τ s) ρ) ≠ ⊥ →
    (1 - de) * nbar ≤ (nOf (τ s) P1 : ℝ) ∧ (nOf (τ s) P1 : ℝ) ≤ (1 + de) * nbar
def Lemma5Prime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [IsGalois ℚ K]
    (V ι : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (G : Type) [Group G] [Fintype G] (ρ : Representation K G V) (R : Submodule (𝓞 K) V)
    (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s))
    (P0 P1 : Pair G K) (nbar de ka HH0 : ℝ)
    (W0 ι0 : Type) [AddCommGroup W0] [Module K W0] [Module (𝓞 K) W0] [IsScalarTower (𝓞 K) K W0]
    [Fintype ι0] [DecidableEq ι0] (b0 : Basis ι0 K W0) (X0 : InfinitePlace K → Matrix ι0 ι0 ℂ)
    (R0 : Submodule (𝓞 K) W0)
    (W1 ι1 : Type) [AddCommGroup W1] [Module K W1] [Module (𝓞 K) W1] [IsScalarTower (𝓞 K) K W1]
    [Fintype ι1] [DecidableEq ι1] (b1 : Basis ι1 K W1) (X1 : InfinitePlace K → Matrix ι1 ι1 ℂ)
    (R1 : Submodule (𝓞 K) W1),
    GoodTransferSetting b X ρ R τ →
    M1 τ P0 →
    0 < nbar → 0 ≤ de → de ≤ 1 / 3 →
    M2 ρ τ P1 nbar de →
    0 ≤ ka →
    CKa b X (latAt ρ R P0) b0 X0 R0 (ka * la G) →
    CKa b X (latAt ρ R P1) b1 X1 R1 (ka * la G) →
    Formalism.HN.muMaxDef b0 X0 R0 ≤ HH0 →
    Formalism.HN.muMaxDef b1 X1 R1 ≤ HH0 + (8.5 + 2 * ka) * la G ∧
      muDual b1 X1 R1 ≤ muDual b0 X0 R0 + 3 * de * (muDual b0 X0 R0 + HH0 + (2 * ka + 2) * la G) +
        (2 * ka + 10.5) * la G ∧
      0 ≤ muDual b0 X0 R0 + HH0 + (2 * ka + 2) * la G
end Formalism.IndefR.IndefiniteEpsilonOperator


