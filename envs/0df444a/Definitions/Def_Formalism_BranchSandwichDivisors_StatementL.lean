-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
-- name    : Formalism_BranchSandwichDivisors_StatementL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:50:40.979089+00:00
-- url     : https://prove2.me/theorems/504ed1f4-64d0-4bfd-b824-c911c119a457
-- title:
--   Statement L
-- statement:
--   Definitions and structural lemmas for Statement L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/StatementL.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_HarderNarasimhan_StatementMod
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.BranchingDeterminantCap
section Defs
variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
def degD (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  (Formalism.HN.rkK L : ℝ) * Formalism.HN.muDef b X L
def OrthAt (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (A B : Submodule (𝓞 K) V) : Prop :=
  ∀ v, ∀ x ∈ A, ∀ y ∈ B, Formalism.HermitianLatticesTheory.majAt b X v x y = 0
def scaleFrame (c : ℝ) (X : InfinitePlace K → Matrix ι ι ℂ) : InfinitePlace K → Matrix ι ι ℂ :=
  fun v => (c : ℂ) • X v
end Defs
def MapMu : Prop :=
  ∀ (K V ι W κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (X' v).det) →
    ∀ (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W), A.FG → B.FG → A ≠ ⊥ →
      Set.InjOn φ (A : Set V) → A.map (φ.restrictScalars (𝓞 K)) ≤ B →
      Formalism.HN.rkK B = Formalism.HN.rkK A →
      Formalism.HN.muDef b X A ≤ Formalism.HN.muDef b' X' B + Formalism.HN.htMap b X b' X' φ
def ScaleSandwich : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (A B : Submodule (𝓞 K) V) (n : ℕ), A.FG → A ≠ ⊥ → 0 < n → B ≤ A →
      (∀ x ∈ A, (n : 𝓞 K) • x ∈ B) →
      Formalism.HN.rkK B = Formalism.HN.rkK A ∧
      Formalism.HN.muDef b X B ≤ Formalism.HN.muDef b X A ∧
      Formalism.HN.muDef b X A ≤ Formalism.HN.muDef b X B + 2 * Real.log n ∧
      Formalism.HN.muMaxDef b X B ≤ Formalism.HN.muMaxDef b X A ∧
      Formalism.HN.muMaxDef b X A ≤ Formalism.HN.muMaxDef b X B + 2 * Real.log n
def OrthSum : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (S : Type) [Fintype S] (A : S → Submodule (𝓞 K) V), (∀ s, (A s).FG) →
      (∀ s t, s ≠ t → OrthAt b X (A s) (A t)) →
      Formalism.HN.rkK (⨆ s, A s) = ∑ s, Formalism.HN.rkK (A s) ∧
      degD b X (⨆ s, A s) = ∑ s, degD b X (A s) ∧
      ∀ c : ℝ, (∀ s, A s ≠ ⊥ → Formalism.HN.muMaxDef b X (A s) ≤ c) → (⨆ s, A s) ≠ ⊥ →
        Formalism.HN.muMaxDef b X (⨆ s, A s) ≤ c
def PowMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (A : Submodule (𝓞 K) V) (n : ℕ), A.FG → A ≠ ⊥ → 0 < n →
      let bn : Basis (Σ _ : Fin n, ι) K (Fin n → V) := Pi.basis fun _ : Fin n => b
      let Xn : InfinitePlace K → Matrix (Σ _ : Fin n, ι) (Σ _ : Fin n, ι) ℂ :=
        fun v => Matrix.blockDiagonal' fun _ : Fin n => X v
      let An : Submodule (𝓞 K) (Fin n → V) := Submodule.pi Set.univ fun _ : Fin n => A
      Formalism.HN.rkK An = n * Formalism.HN.rkK A ∧ Formalism.HN.muDef bn Xn An = Formalism.HN.muDef b X A ∧
        Formalism.HN.muMaxDef bn Xn An = Formalism.HN.muMaxDef b X A
def GoodDeg : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (e : V →ₗ[K] V), e ∘ₗ e = e →
      (∀ v x y, Formalism.HermitianLatticesTheory.majAt b X v (e x) y = Formalism.HermitianLatticesTheory.majAt b X v x (e y)) →
    ∀ (A : Submodule (𝓞 K) V) (n : ℕ), A.FG → A ≠ ⊥ → 0 < n → (∀ a ∈ A, (n : 𝓞 K) • e a ∈ A) →
      degD b X A - (Formalism.HN.rkK (A ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) *
          (Formalism.HN.muMaxDef b X A + 2 * Real.log n) ≤
        degD b X (A ⊓ (LinearMap.range e).restrictScalars (𝓞 K))
def GoodDualDed : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), (∀ x, (∀ y, h y x = 0) → x = 0) →
    ∀ e : V →ₗ[K] V, e ∘ₗ e = e → (∀ x y, h (e x) y = h x (e y)) →
    ∀ A : Submodule (𝓞 K) V, A.FG → Submodule.span K (A : Set V) = ⊤ →
      Formalism.HermitianLatticesTheory.dual h (A ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) ⊓
                (LinearMap.range e).restrictScalars (𝓞 K) =
        (Formalism.HermitianLatticesTheory.dual h A).map (e.restrictScalars (𝓞 K))
def InvariantsDual : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), (∀ x, (∀ y, h y x = 0) → x = 0) →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (ρ : Γ →* Module.End K V),
    (∀ γ x y, h (ρ γ x) (ρ γ y) = h x y) →
    ∀ A : Submodule (𝓞 K) V, A.FG → Submodule.span K (A : Set V) = ⊤ →
      Formalism.HermitianLatticesTheory.dual (((Fintype.card Γ : K)⁻¹) • h)
                  (A ⊓ (LinearMap.range (∑ γ, ρ γ : Module.End K V)).restrictScalars (𝓞 K)) ⊓
                (LinearMap.range (∑ γ, ρ γ : Module.End K V)).restrictScalars (𝓞 K) =
        (Formalism.HermitianLatticesTheory.dual h A).map ((∑ γ, ρ γ : Module.End K V).restrictScalars (𝓞 K))
def BoundsI : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n' n : ℕ)
    (H' E : Matrix (Fin n') (Fin n') K) (I0 : Matrix (Fin n') (Fin n) K),
    IsUnit H'.det → E * E = E → H' * E = Eᴴ * H' → Function.Injective I0.mulVec →
    (∀ y, (∃ x, I0.mulVec x = y) ↔ E.mulVec y = y) →
    ∀ A Bd : Submodule (𝓞 K) (Fin n' → K), Submodule.IsLattice K A →
    ∀ G dG : ℕ, 0 < G → 0 < dG →
    (∀ x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H') A, (dG : 𝓞 K) • x ∈ Bd) →
    (∀ a ∈ Bd, (G : 𝓞 K) • E.mulVec a ∈ A) →
      Submodule.IsLattice K (A.comap ((Matrix.mulVecLin I0).restrictScalars (𝓞 K))) ∧
      ∀ x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform (I0ᴴ * H' * I0))
          (A.comap ((Matrix.mulVecLin I0).restrictScalars (𝓞 K))),
        (((G * dG : ℕ) : 𝓞 K) ^ 1) • x ∈ A.comap ((Matrix.mulVecLin I0).restrictScalars (𝓞 K))
def BoundsIVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    Formalism.DivisionValues.IsCMSub K0 → ∀ v0 : InfinitePlace K, Formalism.DivisionValues.IsConjAt v0 →
    ∀ (n' n D : ℕ) (H' E : Matrix (Fin n') (Fin n') K) (I0 : Matrix (Fin n') (Fin n) K),
    IsUnit H'.det → E * E = E → H' * E = Eᴴ * H' → Function.Injective I0.mulVec →
    (∀ y, (∃ x, I0.mulVec x = y) ↔ E.mulVec y = y) →
    (∀ i j, (I0ᴴ * H' * I0) i j ∈ K0) →
    (∀ v : InfinitePlace K, ((I0ᴴ * H' * I0).map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ A Bd : Submodule (𝓞 K) (Fin n' → K), Submodule.IsLattice K A →
    ∀ G dG : ℕ, 0 < G → 0 < dG →
    (∀ x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H') A, (dG : 𝓞 K) • x ∈ Bd) →
    (∀ a ∈ Bd, (G : 𝓞 K) • E.mulVec a ∈ A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (e : Fin D → Fin D → K),
      Formalism.DivisionValues.IsLocBasis
        (Formalism.DivisionValues.matLat P (A.comap ((Matrix.mulVecLin I0).restrictScalars (𝓞 K)))) w e →
      Formalism.DivisionValues.vw w (Formalism.DivisionValues.gramR (Formalism.DivisionValues.quotGram P (I0ᴴ * H' * I0)) e) ≤
        (D : ℤ) * Formalism.DivisionValues.vw w (((G * dG : ℕ) : ℕ) : K)
def OrthSandwich : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (S : Type) [Fintype S] (A : S → Submodule (𝓞 K) V) (A0 : Submodule (𝓞 K) V) (G : ℕ),
      A0.FG → 0 < G → (∀ s t, s ≠ t → OrthAt b X (A s) (A t)) → (∀ s, A s ≤ A0) →
      (∀ x ∈ A0, (G : 𝓞 K) • x ∈ ⨆ s, A s) →
      Formalism.HN.rkK A0 = ∑ s, Formalism.HN.rkK (A s) ∧
      ∑ s, degD b X (A s) ≤ degD b X A0 ∧
      degD b X A0 ≤ ∑ s, degD b X (A s) + 2 * Real.log G * (Formalism.HN.rkK A0 : ℝ)
def TransferPart : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (A B : Submodule (𝓞 K) V) (n G : ℕ) (x xs : Fin n → V →ₗ[K] V), A.FG → B.FG → A ≠ ⊥ →
      0 < n → 0 < G →
      (∀ i, ∀ a ∈ A, ((G : 𝓞 K) ^ 3) • x i a ∈ B) → (∀ i, ∀ c ∈ B, ((G : 𝓞 K) ^ 3) • xs i c ∈ A) →
      (∀ i v, Formalism.HN.opNormAt b X b X v (x i) ≤ 1) → (∀ i v, Formalism.HN.opNormAt b X b X v (xs i) ≤ 1) →
      (∀ a : Fin n → V, (∀ i, a i ∈ A) → ∑ i, x i (a i) = 0 → a = 0) →
      (∀ c ∈ B, (∀ i, xs i c = 0) → c = 0) →
      Formalism.HN.rkK B = n * Formalism.HN.rkK A →
      |degD b X B - (n : ℝ) * degD b X A| ≤
        (6 * Real.log G + Real.log n) * ((n : ℝ) * (Formalism.HN.rkK A : ℝ))
def TransferMuMax : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (S : Type) [Fintype S] (A B : S → Submodule (𝓞 K) V) (A0 C : Submodule (𝓞 K) V) (G : ℕ)
      (n : S → ℕ) (xs : ∀ s, Fin (n s) → V →ₗ[K] V),
      A0.FG → C.FG → A0 ≠ ⊥ → 0 < G → (∀ s, n s ^ 2 ≤ G) →
      (∀ s t, s ≠ t → OrthAt b X (B s) (B t)) → (∀ s, B s ≤ A0) →
      (∀ x ∈ A0, (G : 𝓞 K) • x ∈ ⨆ s, B s) → (∀ s, A s ≤ C) →
      (∀ s i, ∀ c ∈ B s, ((G : 𝓞 K) ^ 3) • xs s i c ∈ A s) →
      (∀ s i v, Formalism.HN.opNormAt b X b X v (xs s i) ≤ 1) →
      (∀ s, ∀ c ∈ B s, (∀ i, xs s i c = 0) → c = 0) →
      Formalism.HN.muMaxDef b X A0 ≤ Formalism.HN.muMaxDef b X C + 17 / 2 * Real.log G
def LevelCompare : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (R R' : Submodule (𝓞 K) V) (h : ℕ), R.FG → R' ≠ ⊥ → 0 < h → R' ≤ R →
      (∀ x ∈ R, (h : 𝓞 K) • x ∈ R') →
      |Formalism.HN.muDef b (scaleFrame (Real.sqrt h) X) R' - Formalism.HN.muDef b X R| ≤ Real.log h ∧
      |Formalism.HN.muMaxDef b (scaleFrame (Real.sqrt h) X) R' - Formalism.HN.muMaxDef b X R| ≤ Real.log h
def PassageLat : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (S : Type) [Fintype S] (Rs : S → Submodule (𝓞 K) V) (nS : S → ℕ)
      (latticeAtBaseLevel RPs R0 R1 : Submodule (𝓞 K) V) (G h0 h1 : ℕ) (nbar de HH0 : ℝ),
      latticeAtBaseLevel.FG → RPs.FG → R0 ≠ ⊥ → R1 ≠ ⊥ → 0 < h0 → h0 ≤ G → 0 < h1 → h1 ≤ G →
      R0 ≤ latticeAtBaseLevel → (∀ x ∈ latticeAtBaseLevel, (h0 : 𝓞 K) • x ∈ R0) → R1 ≤ RPs → (∀ x ∈ RPs, (h1 : 𝓞 K) • x ∈ R1) →
      (∀ s, Rs s ≤ latticeAtBaseLevel) →
      (Formalism.HN.rkK latticeAtBaseLevel : ℝ) = ∑ s, (Formalism.HN.rkK (Rs s) : ℝ) →
      (Formalism.HN.rkK RPs : ℝ) = ∑ s, (nS s : ℝ) * (Formalism.HN.rkK (Rs s) : ℝ) →
      (∑ s, (nS s : ℝ) * degD b X (Rs s)) - 17 / 2 * Real.log G * (Formalism.HN.rkK RPs : ℝ) ≤
        degD b X RPs →
      degD b X latticeAtBaseLevel ≤ (∑ s, degD b X (Rs s)) + 2 * Real.log G * (Formalism.HN.rkK latticeAtBaseLevel : ℝ) →
      0 < nbar → 0 ≤ de → de ≤ 1 / 3 →
      (∀ s, (1 - de) * nbar ≤ (nS s : ℝ) ∧ (nS s : ℝ) ≤ (1 + de) * nbar) →
      Formalism.HN.muMaxDef b (scaleFrame (Real.sqrt h0) X) R0 ≤ HH0 →
        -Formalism.HN.muDef b (scaleFrame (Real.sqrt h1) X) R1 ≤
          -Formalism.HN.muDef b (scaleFrame (Real.sqrt h0) X) R0 +
            3 * de * (-Formalism.HN.muDef b (scaleFrame (Real.sqrt h0) X) R0 + HH0 + 4 * Real.log G) +
            25 / 2 * Real.log G
end Formalism.BranchingDeterminantCap


