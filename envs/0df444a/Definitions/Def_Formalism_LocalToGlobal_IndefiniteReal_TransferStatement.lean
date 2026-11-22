-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TransferStatement
-- name    : Formalism_LocalToGlobal_IndefiniteReal_TransferStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:42.932885+00:00
-- url     : https://prove2.me/theorems/c5bc64ce-9818-41c3-8a2a-2813219228b2
-- title:
--   Transfer Statement
-- statement:
--   Definitions and structural lemmas for Transfer Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/TransferStatement.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
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
namespace Formalism.IndefR.TransferLatticeStatement
open Formalism.HN
section Defs
variable {K : Type*} [Field K] {G : Type*} [Group G] [Fintype G]
def charOf {T : Type*} [AddCommGroup T] [Module K T] (τ : Representation K G T) (x : G) : K :=
  LinearMap.trace K T (τ x)
def eS {T V : Type*} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) : V →ₗ[K] V :=
  (charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, charOf τ x⁻¹ • ρ x
def eGood {S : Type*} [Fintype S] {T : S → Type*} [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    {V : Type*} [AddCommGroup V] [Module K V]
    (τ : ∀ s, Representation K G (T s)) (ρ : Representation K G V) : V →ₗ[K] V :=
  ∑ s, eS (τ s) ρ
open Classical in

def epP (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) {V : Type*} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) : V →ₗ[K] V :=
  ((Nat.card H : ℕ) : K)⁻¹ • ∑ h : H, ((((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) • ρ (h : G)
def nS {T : Type*} [AddCommGroup T] [Module K T] (τ : Representation K G T) (H : Subgroup G)
    (χ : H →* (𝓞 K)ˣ) : ℕ :=
  finrank K (LinearMap.range (epP H χ τ))
def IsGood {S : Type*} {T : S → Type*} [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    (τ : ∀ s, Representation K G (T s)) : Prop :=
  (∀ s, Nontrivial (T s)) ∧
  (∀ s (W : Submodule K (T s)), (∀ g : G, ∀ w ∈ W, τ s g w ∈ W) → W = ⊥ ∨ W = ⊤) ∧
  (∀ s (f : T s →ₗ[K] T s), (∀ g : G, f ∘ₗ τ s g = τ s g ∘ₗ f) → ∃ c : K, f = c • LinearMap.id) ∧
  (∀ s t, charOf (τ s) = charOf (τ t) → s = t)
def M1 {S : Type*} {T : S → Type*} [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    (τ : ∀ s, Representation K G (T s)) (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) : Prop :=
  ∀ s, nS (τ s) H₀ χ₀ = 1
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def cut (A : Submodule (𝓞 K) V) (φ : V →ₗ[K] V) : Submodule (𝓞 K) V :=
  A ⊓ (LinearMap.range φ).restrictScalars (𝓞 K)
def IsGLat (ρ : Representation K G V) (A : Submodule (𝓞 K) V) : Prop :=
  A.FG ∧ Submodule.span K (A : Set V) = ⊤ ∧ ∀ g : G, ∀ a ∈ A, ρ g a ∈ A
def IsUnitaryRep [NumberField K] [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V) : Prop :=
  ∀ (v : InfinitePlace K) (g : G) (x y : V),
    Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g y) = Formalism.HermitianLatticesTheory.majAt b X v x y
def degT [NumberField K] [StarRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (M : Submodule (𝓞 K) V) : ℝ :=
  (rkK M : ℝ) * muDef b X M
def lenW [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) : ℕ :=
  (Module.length (Localization.AtPrime w.asIdeal)
    (LocalizedModule w.asIdeal.primeCompl (M ⧸ N.comap M.subtype))).toNat
def idxW [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) : ℤ :=
  (lenW w M N : ℤ) - lenW w N M
end Defs
section Places
variable {K : Type*} [Field K] [NumberField K]
open Classical in

def vW (w : HeightOneSpectrum (𝓞 K)) (d : 𝓞 K) : ℕ :=
  (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {d})).factors
def lW (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (finrank ℚ K : ℝ)
def meanLog (d : 𝓞 K) : ℝ :=
  (1 / (finrank ℚ K : ℝ)) * ∑ σ : K →+* ℂ, Real.log ‖σ (d : K)‖
end Places
section Parts
variable {K : Type*} [Field K] [NumberField K] [StarRing K] {G : Type*} [Group G] [Fintype G]
  {S : Type*} [Fintype S] {T : S → Type*} [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
def TransferLatticeConditions (τ : ∀ s, Representation K G (T s)) (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ)
    (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (ρ : Representation K G V) (A : Submodule (𝓞 K) V) : Prop :=
  let la : ℝ := Real.log (Fintype.card G)
  let n : S → ℕ := fun s => nS (τ s) H χ
  let APs : S → Submodule (𝓞 K) V := fun s => cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)
  let AP0 : Submodule (𝓞 K) V := cut A (epP H χ ρ ∘ₗ eGood τ ρ)
  let As : S → Submodule (𝓞 K) V := fun s => cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)
  let A00 : Submodule (𝓞 K) V := cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)
  let r : S → ℕ := fun s => rkK (As s)
  let rk : ℕ := ∑ s, n s * r s

  ((∀ s, rkK (APs s) = n s * r s) ∧ rkK AP0 = rk) ∧

  ((⨆ s, APs s) ≤ AP0 ∧
    (∀ a ∈ AP0, (Fintype.card G : 𝓞 K) • a ∈ ⨆ s, APs s) ∧
    (∀ s t, s ≠ t → ∀ x ∈ APs s, ∀ y ∈ APs t, ∀ v, Formalism.HermitianLatticesTheory.majAt b X v x y = 0) ∧
    0 ≤ degT b X AP0 - ∑ s, degT b X (APs s) ∧
    degT b X AP0 - ∑ s, degT b X (APs s) ≤ 2 * la * (rk : ℝ) ∧
    0 ≤ degT b X A00 - ∑ s, degT b X (As s) ∧
    degT b X A00 - ∑ s, degT b X (As s) ≤ 2 * la * ∑ s, (r s : ℝ)) ∧

  (∀ s, |degT b X (APs s) - (n s : ℝ) * degT b X (As s)| ≤
        (6 * la + Real.log (n s)) * ((n s : ℝ) * r s) ∧
      (6 * la + Real.log (n s)) * ((n s : ℝ) * r s) ≤ 6.5 * la * ((n s : ℝ) * r s)) ∧

  (|degT b X AP0 - ∑ s, (n s : ℝ) * degT b X (As s)| ≤ 8.5 * la * (rk : ℝ) ∧
    8.5 * la * (rk : ℝ) ≤ 10 * la * (rk : ℝ)) ∧

  (AP0 ≠ ⊥ →
    muMaxDef b X AP0 ≤ muMaxDef b X A00 + 8.5 * la ∧
    muMaxDef b X A00 + 8.5 * la ≤ muMaxDef b X A00 + 10 * la)
def GammaOK {n : ℕ} (Γ : Matrix (Fin n) (Fin n) (𝓞 K)) (la : ℝ) : Prop :=
  Γ.det ≠ 0 ∧
  meanLog Γ.det = ∑ᶠ w : HeightOneSpectrum (𝓞 K), lW w * (vW w Γ.det : ℝ) ∧
  ∑ᶠ w : HeightOneSpectrum (𝓞 K), lW w * (vW w Γ.det : ℝ) ≤
    (n : ℝ) * (6 * la + 1 / 2 * Real.log n) ∧
  (n : ℝ) * (6 * la + 1 / 2 * Real.log n) ≤ 6.25 * (n : ℝ) * la
def LatticeGramTransferCondition (τ : ∀ s, Representation K G (T s)) (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ)
    (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (ρ : Representation K G V)
    (Γ : ∀ s, Matrix (Fin (nS (τ s) H χ)) (Fin (nS (τ s) H χ)) (𝓞 K))
    (A B : Submodule (𝓞 K) V) : Prop :=
  let la : ℝ := Real.log (Fintype.card G)
  let n : S → ℕ := fun s => nS (τ s) H χ
  let r : S → ℕ := fun s => rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))
  let rk : ℕ := ∑ s, n s * r s
  let de : HeightOneSpectrum (𝓞 K) → ℝ := fun w =>
    (rk : ℝ)⁻¹ * ∑ s, ((n s : ℝ) * r s) *
      ((vW w (Γ s).det : ℝ) / n s + (vW w (Fintype.card G : 𝓞 K) : ℝ))
  (∀ w : HeightOneSpectrum (𝓞 K),
    |((idxW w (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) (cut B (epP H χ ρ ∘ₗ eGood τ ρ)) : ℤ) : ℝ) -
        ∑ s, (n s : ℝ) * ((idxW w (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))
          (cut B (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) : ℤ) : ℝ)| ≤ de w * rk ∧
      0 ≤ de w) ∧
  ∑ᶠ w : HeightOneSpectrum (𝓞 K), lW w * de w ≤ 7.25 * la ∧
  7.25 * la ≤ 8 * la
end Parts
def Lemma4 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (S : Type) [Fintype S] (T : S → Type) [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)]
    [∀ s, FiniteDimensional K (T s)] (τ : ∀ s, Representation K G (T s))
    (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ),
    IsGood τ → M1 τ H₀ χ₀ →
    ∃ Γ : ∀ s, Matrix (Fin (nS (τ s) H χ)) (Fin (nS (τ s) H χ)) (𝓞 K),
      (∀ s, GammaOK (Γ s) (Real.log (Fintype.card G))) ∧
      ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
        (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
        (X : InfinitePlace K → Matrix ι ι ℂ) (ρ : Representation K G V),
        (∀ v, IsUnit (X v).det) → IsUnitaryRep b X ρ →
        ∀ A B : Submodule (𝓞 K) V, IsGLat ρ A → IsGLat ρ B →
          TransferLatticeConditions τ H₀ χ₀ H χ b X ρ A ∧ LatticeGramTransferCondition τ H₀ χ₀ H χ ρ Γ A B
end Formalism.IndefR.TransferLatticeStatement


