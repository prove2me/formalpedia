-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose
-- name    : Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:53:34.578808+00:00
-- url     : https://prove2.me/theorems/bc46fc04-95f8-4836-88de-2ac9dbd070ec
-- title:
--   Gram CEq Transpose
-- statement:
--   Definitions and structural lemmas for Gram CEq Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/GramCEqTranspose.lean

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
open NumberField IsDedekindDomain Module
open scoped InnerProductSpace Matrix
namespace Formalism.IndefR.Arith
section Data
variable (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable (WL : Type) [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
variable (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable (G0 : Type) [Group G0]
structure FormsL where

  WK : Submodule Ks WL

  Pt : HeightOneSpectrum (𝓞 Ks) → Type

  nrm : ∀ lp, Pt lp → WK → ℝ
  nrm_nonneg : ∀ lp y f, 0 ≤ nrm lp y f
  nrm_zero : ∀ lp y, nrm lp y 0 = 0
  nrm_add : ∀ lp y f g, nrm lp y (f + g) ≤ max (nrm lp y f) (nrm lp y g)
  nrm_smul : ∀ lp y (a : Ks) f, nrm lp y (a • f) = FinitePlace.mk lp a * nrm lp y f

  towKs : IsScalarTower Ks LL WL

  ρ : G0 →* (WL →ₗ[LL] WL)

  chi : G0 →* LLˣ

  j : ∀ σ : LL →+* ℂ, WL →ₛₗ[σ] W σ
end Data
section Defs
variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)
namespace FormsL
def IsKsForm : Prop :=
  ∃ (n : ℕ) (b : Fin n → WL), (∀ i, b i ∈ A.WK) ∧ LinearIndependent Ks b ∧
    Submodule.span Ks (Set.range b) = A.WK ∧ LinearIndependent LL b ∧ Submodule.span LL (Set.range b) = ⊤
def MK : Submodule (𝓞 Ks) WL where
  carrier := {f | ∃ h : f ∈ A.WK, ∀ lp (y : A.Pt lp), A.nrm lp y ⟨f, h⟩ ≤ 1}
  zero_mem' := ⟨A.WK.zero_mem, fun lp y => by
    rw [show (⟨0, A.WK.zero_mem⟩ : A.WK) = 0 from rfl, A.nrm_zero]; exact zero_le_one⟩
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨A.WK.add_mem hf hg, fun lp y => ?_⟩
    have := A.nrm_add lp y ⟨f, hf⟩ ⟨g, hg⟩
    exact this.trans (max_le (hf' lp y) (hg' lp y))
  smul_mem' := by
    rintro a f ⟨hf, hf'⟩
    have hs : a • f = ((a : Ks)) • f := (algebraMap_smul Ks a f).symm
    have hm : a • f ∈ A.WK := by rw [hs]; exact A.WK.smul_mem _ hf
    refine ⟨hm, fun lp y => ?_⟩
    have h1 : (⟨a • f, hm⟩ : A.WK) = (a : Ks) • ⟨f, hf⟩ := Subtype.ext hs
    rw [h1, A.nrm_smul]
    have h2 : FinitePlace.mk lp (a : Ks) ≤ 1 := by
      rw [FinitePlace.mk_apply]; exact FinitePlace.norm_le_one Ks (v := lp) a
    calc FinitePlace.mk lp (a : Ks) * A.nrm lp y ⟨f, hf⟩ ≤ 1 * 1 :=
          mul_le_mul h2 (hf' lp y) (A.nrm_nonneg lp y _) zero_le_one
      _ = 1 := one_mul 1
def typeP (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) : Submodule LL WL where
  carrier := {F | ∀ p : J0, A.ρ p F = ((A.chi p * lam0 p : LLˣ) : LL) • F}
  zero_mem' := fun p => by simp
  add_mem' := fun {F G} hF hG p => by
    show A.ρ p (F + G) = _
    rw [map_add, hF p, hG p, smul_add]
  smul_mem' := fun a F hF p => by
    show A.ρ p (a • F) = _
    rw [LinearMap.map_smul, hF p, smul_comm]
def eOp (eC : G0 → LL) : WL →ₗ[LL] WL := ∑ g, (eC g * ((A.chi g)⁻¹ : LLˣ)) • A.ρ g
def good (eC : G0 → LL) : Submodule LL WL := LinearMap.range (A.eOp eC)
def Wgood (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) : Submodule LL WL :=
  A.typeP J0 lam0 ⊓ A.good eC
def Mall (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) : Submodule (𝓞 LL) WL :=
  Submodule.span (𝓞 LL) (A.MK : Set WL) ⊓ (A.typeP J0 lam0).restrictScalars (𝓞 LL)
def Mj (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) : Submodule (𝓞 LL) WL :=
  A.Mall J0 lam0 ⊓ (A.good eC).restrictScalars (𝓞 LL)
def pet (σ : LL →+* ℂ) (x y : WL) : ℂ := ⟪A.j σ y, A.j σ x⟫_ℂ
def nrmAt (σ : LL →+* ℂ) (x : WL) : ℝ := ‖A.j σ x‖
def gram (σ : LL →+* ℂ) {n : ℕ} (b : Fin n → WL) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => A.pet σ (b i) (b k)
def gramC (σ : LL →+* ℂ) {n : ℕ} (b : Fin n → WL) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => ⟪A.j σ (b i), A.j σ (b k)⟫_ℂ
open Classical in

def gramV (pos : (LL →+* ℂ) → Prop) (σ : LL →+* ℂ) {n : ℕ} (b : Fin n → WL) : Matrix (Fin n) (Fin n) ℂ :=
  if pos σ then A.gramC σ b else (A.gramC ((starRingEnd ℂ).comp σ) b)ᵀ
def IsFrameAt (pos : (LL →+* ℂ) → Prop) (σ : LL →+* ℂ) {n : ℕ} (b : Fin n → WL) (X : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = A.gramV pos σ b
def Mcoord (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) {d : ℕ} (b : Fin d → WL) :
    Submodule (𝓞 LL) (Fin d → LL) :=
  (A.Mj J0 lam0 eC).comap ((Fintype.linearCombination LL b).restrictScalars (𝓞 LL))
end FormsL
end Defs
section EEMetric
variable {LL : Type} [Field LL]
variable {QL : Type} [AddCommGroup QL] [Module LL QL]
variable {Ix J : Type} [Fintype Ix] [Fintype J]
def eeNormSq (kap : (LL →+* ℂ) → ℝ) (lam : (LL →+* ℂ) → J → Ix → ℝ) (nq : (LL →+* ℂ) → QL → ℝ)
    (prj : Ix → QL →ₗ[LL] QL) (σ : LL →+* ℂ) (F : QL) : ℝ :=
  ∑ c, kap σ * (∏ j, lam σ j c) * nq σ (prj c F) ^ 2
end EEMetric
section Statements
variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)
namespace FormsL
def UnifAt (actC : ∀ σ, G0 →* (W σ →ₗ[ℂ] W σ)) (σ : LL →+* ℂ) : Prop :=
  (∀ (n : ℕ) (b : Fin n → WL), LinearIndependent LL b → LinearIndependent ℂ (fun i => A.j σ (b i))) ∧
    Submodule.span ℂ (Set.range (A.j σ)) = ⊤ ∧
    ∀ g x, A.j σ (A.ρ g x) = σ ((A.chi g : LLˣ) : LL) • actC σ g (A.j σ x)
def PosOK (pos : (LL →+* ℂ) → Prop) (σ₀ : LL →+* ℂ) : Prop :=
  pos σ₀ ∧ ∀ σ, (pos σ ∨ pos ((starRingEnd ℂ).comp σ)) ∧ ¬ (pos σ ∧ pos ((starRingEnd ℂ).comp σ))
def UnifAll (pos : (LL →+* ℂ) → Prop) (actC : ∀ σ, G0 →* (W σ →ₗ[ℂ] W σ)) : Prop :=
  ∀ σ, pos σ → A.UnifAt actC σ
def ChiKs : Prop :=
  ∀ g, ((A.chi g : LLˣ) : LL) ∈ Set.range (algebraMap Ks LL)
def HeckeRat (pos : (LL →+* ℂ) → Prop) {T : Type} (hL : T → WL →ₗ[LL] WL) (hC : ∀ σ, T → W σ →ₗ[ℂ] W σ) :
    Prop :=
  ∀ σ, pos σ → ∀ t x, A.j σ (hL t x) = hC σ t (A.j σ x)
def GalA : Prop :=
  ∀ (σ : LL →+* ℂ) (x : WL), A.nrmAt ((starRingEnd ℂ).comp σ) x = A.nrmAt σ x
def GalE (pos : (LL →+* ℂ) → Prop) (eC : G0 → LL) (eAn : ∀ σ, W σ →ₗ[ℂ] W σ) : Prop :=
  ∀ σ, pos σ → ∀ x, A.j σ (A.eOp eC x) = eAn σ (A.j σ x)
def GalD (pos : (LL →+* ℂ) → Prop) {XL : Type} [AddCommGroup XL] [Module LL XL] {X : (LL →+* ℂ) → Type}
    [∀ σ, AddCommGroup (X σ)] [∀ σ, Module ℂ (X σ)] (jX : ∀ σ, XL →ₛₗ[σ] X σ) (thL : XL →ₗ[LL] WL)
    (thC : ∀ σ, X σ →ₗ[ℂ] W σ) (actC : ∀ σ, G0 →* (W σ →ₗ[ℂ] W σ)) : Prop :=
  ∀ σ, pos σ → ∃ z ∈ Subgroup.center G0, ∃ κ : ℂ, (∃ n : ℕ, 0 < n ∧ κ ^ n = 1) ∧
    ∀ x, A.j σ (thL x) = κ • actC σ z (thC σ (jX σ x))
def RatTheta {XL : Type} [AddCommGroup XL] [Module LL XL] {X : (LL →+* ℂ) → Type}
    [∀ σ, AddCommGroup (X σ)] [∀ σ, Module ℂ (X σ)] (jX : ∀ σ, XL →ₛₗ[σ] X σ) (thL : XL →ₗ[LL] WL)
    (thC : ∀ σ, X σ →ₗ[ℂ] W σ) (σ₀ : LL →+* ℂ) : Prop :=
  ∀ x, A.j σ₀ (thL x) = thC σ₀ (jX σ₀ x)
def ThetaGood {XL : Type} [AddCommGroup XL] [Module LL XL] (thL : XL →ₗ[LL] WL) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) {T : Type} (hX : T → XL →ₗ[LL] XL) (hL : T → WL →ₗ[LL] WL) : Prop :=
  (∀ x, thL x ∈ A.typeP J0 lam0) ∧ ∀ t x, thL (hX t x) = hL t (thL x)
def ScalarAt {XL : Type} [AddCommGroup XL] [Module LL XL] {X : (LL →+* ℂ) → Type}
    [∀ σ, NormedAddCommGroup (X σ)] [∀ σ, InnerProductSpace ℂ (X σ)] (jX : ∀ σ, XL →ₛₗ[σ] X σ)
    (thL : XL →ₗ[LL] WL) {Ix : Type} (partX : Ix → Submodule LL XL) (lam : (LL →+* ℂ) → Ix → ℝ)
    (σ : LL →+* ℂ) : Prop :=
  ∀ c, ∀ x ∈ partX c, ∀ y, A.pet σ (thL x) (thL y) = ((lam σ c : ℝ) : ℂ) * ⟪jX σ y, jX σ x⟫_ℂ
def GalDBound (pos : (LL →+* ℂ) → Prop) {Ix : Type} (lam : (LL →+* ℂ) → Ix → ℝ) (S C : ℝ) : Prop :=
  ∀ σ, pos σ → ∀ c, 0 < lam σ c ∧ |Real.log (lam σ c) - S| ≤ C
def MKFull : Prop :=
  (A.MK : Submodule (𝓞 Ks) WL).FG ∧ Submodule.span Ks (A.MK : Set WL) = A.WK
def MKStable : Prop :=
  ∀ g f, (f ∈ A.WK → A.ρ g f ∈ A.WK) ∧ (f ∈ A.MK → A.ρ g f ∈ A.MK)
def EIdem (eC : G0 → LL) : Prop :=
  A.eOp eC ∘ₗ A.eOp eC = A.eOp eC ∧ (∀ g, A.eOp eC ∘ₗ A.ρ g = A.ρ g ∘ₗ A.eOp eC) ∧
    ∀ g, eC g ∈ Set.range (algebraMap Ks LL)
def ActUnitary (pos : (LL →+* ℂ) → Prop) (actC : ∀ σ, G0 →* (W σ →ₗ[ℂ] W σ)) : Prop :=
  ∀ σ, pos σ → ∀ g (x y : W σ), ⟪actC σ g x, actC σ g y⟫_ℂ = ⟪x, y⟫_ℂ
def RankMj (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) (D : ℕ) : Prop :=
  finrank LL (A.Wgood J0 lam0 eC) = D
def Igeo (actC : ∀ σ, G0 →* (W σ →ₗ[ℂ] W σ)) (σ₀ : LL →+* ℂ) : Prop :=
  A.UnifAt actC σ₀ ∧ A.IsKsForm ∧ A.MKFull ∧ A.MKStable
end FormsL
end Statements
end Formalism.IndefR.Arith


