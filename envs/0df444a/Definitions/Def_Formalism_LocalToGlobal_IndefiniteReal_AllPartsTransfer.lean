-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
-- name    : Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:33.34693+00:00
-- url     : https://prove2.me/theorems/901fe934-0084-4376-89f2-5a379bc13b22
-- title:
--   All Parts Transfer
-- statement:
--   Definitions and structural lemmas for All Parts Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/AllPartsTransfer.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TransferStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
namespace Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement Formalism.HN
def CharFacts : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (T : Type) [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T)
    (g : G), IsIntegral ℤ (charOf τ g) ∧
      ∀ σ : K →+* ℂ, σ (charOf τ g⁻¹) = star (σ (charOf τ g)) ∧
        ‖σ (charOf τ g)‖ ≤ (finrank K T : ℝ)
def KeyZero : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [Group G] [Fintype G]
    (T : Type) [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (V : Type) [AddCommGroup V] [Module K V] (ρ : Representation K G V) (a : MonoidAlgebra K G),
    τ.asAlgebraHom a = 0 → eS τ ρ ∘ₗ ρ.asAlgebraHom a = 0
def Schur : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s)), IsGood τ →
    (∀ s, eS (τ s) (τ s) = LinearMap.id) ∧ (∀ s t, s ≠ t → eS (τ s) (τ t) = 0) ∧
      ∀ s, ∑ x : G, charOf (τ s) x⁻¹ * charOf (τ s) x = (Fintype.card G : K)
def DimSq : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s)), IsGood τ →
    ∀ s, finrank K (T s) ^ 2 ≤ Fintype.card G ∧
      ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ), nS (τ s) H χ ^ 2 ≤ Fintype.card G
def IdemE : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s)), IsGood τ →
    ∀ (V : Type) [AddCommGroup V] [Module K V] (ρ : Representation K G V),
      (∀ s, eS (τ s) ρ ∘ₗ eS (τ s) ρ = eS (τ s) ρ) ∧
      (∀ s t, s ≠ t → eS (τ s) ρ ∘ₗ eS (τ t) ρ = 0)
def IdemP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (ρ : Representation K G V),
    (∀ (T : Type) [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T),
      (∀ g : G, eS τ ρ ∘ₗ ρ g = ρ g ∘ₗ eS τ ρ) ∧
      (∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ), eS τ ρ ∘ₗ epP H χ ρ = epP H χ ρ ∘ₗ eS τ ρ) ∧
      ∀ A : Submodule (𝓞 K) V, (∀ g : G, ∀ a ∈ A, ρ g a ∈ A) →
        ∀ a ∈ A, (Fintype.card G : 𝓞 K) • eS τ ρ a ∈ A) ∧
    ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
      epP H χ ρ ∘ₗ epP H χ ρ = epP H χ ρ ∧
      ∀ A : Submodule (𝓞 K) V, (∀ g : G, ∀ a ∈ A, ρ g a ∈ A) →
        ∀ a ∈ A, (Fintype.card G : 𝓞 K) • epP H χ ρ a ∈ A
def CoreData {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
    {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) {n : ℕ}
    (γ δ : Fin n → G) (c : Matrix (Fin n) (Fin n) K) (Γ : Matrix (Fin n) (Fin n) (𝓞 K)) : Prop :=
  c.det ≠ 0 ∧ (∀ i j, ((Γ i j : 𝓞 K) : K) = (Fintype.card G : K) ^ 2 * c i j) ∧
  (∀ i j (σ : K →+* ℂ), ‖σ (c i j)‖ ≤ (finrank K T : ℝ)) ∧
  ∀ (V : Type) [AddCommGroup V] [Module K V] (ρ : Representation K G V),
    (∀ i j, ∀ a : V, epP H₀ χ₀ ρ (eS τ ρ a) = a →
      epP H₀ χ₀ ρ (ρ (δ i) (epP H χ ρ (ρ (γ j) a))) = c i j • a) ∧
    (∀ a : V, epP H χ ρ (eS τ ρ a) = a →
      ∑ j, ∑ i, c⁻¹ j i • epP H χ ρ (ρ (γ j) (epP H₀ χ₀ ρ (ρ (δ i) a))) = a)
def Core : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G]
    (S : Type) (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s))
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
    IsGood τ → M1 τ H₀ χ₀ → ∀ s,
      ∃ (γ δ : Fin (nS (τ s) H χ) → G) (c : Matrix (Fin (nS (τ s) H χ)) (Fin (nS (τ s) H χ)) K)
        (Γ : Matrix (Fin (nS (τ s) H χ)) (Fin (nS (τ s) H χ)) (𝓞 K)),
        CoreData (τ s) H₀ χ₀ H χ γ δ c Γ
def Metric : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V),
    (∀ v, IsUnit (X v).det) → IsUnitaryRep b X ρ →
    (∀ (T : Type) [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T)
      (v : InfinitePlace K) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v (eS τ ρ x) y = Formalism.HermitianLatticesTheory.majAt b X v x (eS τ ρ y)) ∧
    ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G) (v : InfinitePlace K),
      opNormAt b X b X v (epP H χ ρ ∘ₗ ρ g) ≤ 1
def UnitOfNorm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V),
    (∀ (g : G) (v : InfinitePlace K) (x : V),
      Formalism.HermitianLatticesTheory.normAt b X v (ρ g x) = Formalism.HermitianLatticesTheory.normAt b X v x) → IsUnitaryRep b X ρ
def LiftChar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (H : Type) [Group H] [Finite H] (χ : H →* Kˣ),
    ∃ χ' : H →* (𝓞 K)ˣ, ∀ h, (((χ' h : (𝓞 K)ˣ) : 𝓞 K) : K) = ((χ h : Kˣ) : K)
def AllPartsTransfer : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] (G : Type) [Group G]
    [Fintype G] (S : Type) [Fintype S] (T : S → Type) [∀ s, AddCommGroup (T s)]
    [∀ s, Module K (T s)] [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s))
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
    IsGood τ → M1 τ H₀ χ₀ →
      ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
        (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
        (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V),
        (∀ v, IsUnit (X v).det) → IsUnitaryRep b X ρ →
        ∀ A : Submodule (𝓞 K) V, IsGLat ρ A → TransferLatticeConditions τ H₀ χ₀ H χ b X ρ A
def matAct {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {n : ℕ}
    (Γ : Matrix (Fin n) (Fin n) K) : (Fin n → V) →ₗ[K] (Fin n → V) :=
  LinearMap.pi fun i => ∑ j, Γ i j • LinearMap.proj j
def IdxBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    (∀ M N P : Submodule (𝓞 K) V, M.FG → N.FG → P.FG →
      Submodule.span K (M : Set V) = Submodule.span K (N : Set V) →
      Submodule.span K (N : Set V) = Submodule.span K (P : Set V) →
      idxW w M N + idxW w N P = idxW w M P) ∧
    (∀ M N : Submodule (𝓞 K) V, N ≤ M → 0 ≤ idxW w M N) ∧
    (∀ (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
      (φ : V →ₗ[K] W) (M N : Submodule (𝓞 K) V),
      Submodule.span K (M : Set V) = Submodule.span K (N : Set V) →
      Set.InjOn φ (Submodule.span K (M : Set V) : Set V) →
      idxW w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) = idxW w M N) ∧
    (∀ (S : Type) [Fintype S] (M N : S → Submodule (𝓞 K) V), (∀ s, (M s).FG) → (∀ s, (N s).FG) →
      (∀ s, Submodule.span K (M s : Set V) = Submodule.span K (N s : Set V)) →
      iSupIndep (fun s => Submodule.span K (M s : Set V)) →
      idxW w (⨆ s, M s) (⨆ s, N s) = ∑ s, idxW w (M s) (N s)) ∧
    (∀ (n : ℕ) (M N : Submodule (𝓞 K) V), M.FG → N.FG →
      Submodule.span K (M : Set V) = Submodule.span K (N : Set V) →
      idxW w (Submodule.pi Set.univ fun _ : Fin n => M) (Submodule.pi Set.univ fun _ : Fin n => N) =
        n * idxW w M N)
def IdxDet : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (M : Submodule (𝓞 K) V), M.FG →
    (∀ d : 𝓞 K, d ≠ 0 →
      idxW w M (M.map ((((d : K) • LinearMap.id : V →ₗ[K] V)).restrictScalars (𝓞 K))) =
        (rkK M : ℤ) * vW w d) ∧
    ∀ (n : ℕ) (Γ : Matrix (Fin n) (Fin n) (𝓞 K)), Γ.det ≠ 0 →
      idxW w (Submodule.pi Set.univ fun _ : Fin n => M)
        ((Submodule.pi Set.univ fun _ : Fin n => M).map
          ((matAct (V := V) (Γ.map (algebraMap (𝓞 K) K))).restrictScalars (𝓞 K))) =
        (rkK M : ℤ) * vW w Γ.det
def ProdFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ lW w) ∧
    (∀ d : 𝓞 K, d ≠ 0 → {w : HeightOneSpectrum (𝓞 K) | vW w d ≠ 0}.Finite ∧
      meanLog d = ∑ᶠ w : HeightOneSpectrum (𝓞 K), lW w * (vW w d : ℝ)) ∧
    ∀ N : ℕ, 0 < N → meanLog (N : 𝓞 K) = Real.log N
def GammaBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n N : ℕ) (Γ : Matrix (Fin n) (Fin n) (𝓞 K)),
    0 < N → n ^ 2 ≤ N → Γ.det ≠ 0 →
    (∀ i j (σ : K →+* ℂ), ‖σ ((Γ i j : 𝓞 K) : K)‖ ≤ (N : ℝ) ^ 3) → GammaOK Γ (Real.log N)
end Formalism.IndefR.LatticeTransfer


