-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
-- name    : Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:35.363994+00:00
-- url     : https://prove2.me/theorems/6c6ece17-d018-4f0e-a01c-a96f3b1f369b
-- title:
--   Det Index Product Hyperbolic Inequality
-- statement:
--   Definitions and structural lemmas for Det Index Product Hyperbolic Inequality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/DetIndexProductHyperbolicInequality.lean

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
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
namespace Formalism.HermitianLatticeCounting.LocalIntegralStructure
abbrev TorsionIndex : Prop := Formalism.SLP.TorsionIndex
abbrev TorsionIndexEq : Prop := Formalism.SLP.TorsionIndexEq
abbrev DetIndexSqInequality : Prop := Formalism.SLP.DetIndexSqInequality
abbrev DetIndexSqInequalityDiv : Prop := Formalism.SLP.DetIndexSqInequalityDiv
abbrev QuotOrderO : Prop := Formalism.SLP.QuotOrderO
abbrev BBVanish : Prop := Formalism.SLP.BBVanish
abbrev BBBound : Prop := Formalism.SLP.BBBound
abbrev BBPr : Prop := Formalism.SLP.BBPr
abbrev RadicalSub : Prop := Formalism.SLP.RadicalSub
abbrev RadicalRank : Prop := Formalism.SLP.RadicalRank
abbrev RadNormal : Prop := Formalism.SLP.RadNormal
abbrev PsiGeN : Prop := Formalism.SLP.PsiGeN
abbrev RadicalEq : Prop := Formalism.SLP.RadicalEq
abbrev SesqDet : Prop := Formalism.SLP.SesqDet
abbrev IdealNormBound : Prop := Formalism.SLP.IdealNormBound
abbrev ElementPlaceBound : Prop := Formalism.SLP.ElementPlaceBound
abbrev DenomNorm : Prop := Formalism.SLP.DenomNorm
abbrev DetIndexProductInequality : Prop := Formalism.SLP.DetIndexProductInequality
abbrev Polarise : Prop := Formalism.SLP.GlobalBoundRefinements.Polarise
abbrev EntriesOfSignaturePreserving : Prop := Formalism.SLP.GlobalBoundRefinements.EntriesOfSignaturePreserving
abbrev AlHyp : Prop := Formalism.SLP.GlobalBoundRefinements.AlHyp
abbrev ProdPlacesHyperbolicInequality : Prop := Formalism.SLP.GlobalBoundRefinements.ProdPlacesHyperbolicInequality
abbrev DetIndexProductHyperbolicInequality : Prop := Formalism.SLP.GlobalBoundRefinements.DetIndexProductHyperbolicInequality
abbrev FormCoeff : Prop := Formalism.SLP.GlobalBoundRefinements.FormCoeff
abbrev RootUnityModT : Prop := Formalism.SLP.GlobalBoundRefinements.RootUnityModT
abbrev RootUnityTriv : Prop := Formalism.SLP.GlobalBoundRefinements.RootUnityTriv
abbrev ThmBEntry : Prop := Formalism.SLP.GlobalBoundRefinements.ThmBEntry
abbrev SEntry : Prop := Formalism.SLP.GlobalBoundRefinements.SEntry
abbrev ThmBNorm : Prop := Formalism.SLP.GlobalBoundRefinements.ThmBNorm
def perpR {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K}
    (B : V →ₗ[K] V →ₛₗ[σ] K) (A : Submodule K V) : Submodule K V :=
  ⨅ a : A, LinearMap.ker (B a)
def PerpCompl : Prop :=
  ∀ (K U : Type) [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (σ : K →+* K), (∀ x, σ (σ x) = x) →
    ∀ (B : U →ₗ[K] U →ₛₗ[σ] K), (∀ x : U, (∀ y : U, B y x = 0) → x = 0) →
    (∀ x : U, (∀ y : U, B x y = 0) → x = 0) →
    ∀ (r : ℕ) (A A' : Submodule K U), finrank K U = 2 * (r + 1) →
      finrank K A = r + 1 → finrank K A' = r + 1 → A ⊔ A' = ⊤ →
      finrank K (perpR B A) = r + 1 ∧ finrank K (perpR B A') = r + 1 ∧
        IsCompl (perpR B A) (perpR B A')
def CofactorVec : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R),
    (∀ a : Fin (r + 1), ∑ b, Z.adjugate (Fin.last r) b * Z b a =
        if a = Fin.last r then Z.det else 0) ∧
      Z.adjugate (Fin.last r) (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det
def CofactorNorms : Prop :=
  ∀ (T T' : ℝ) (t D Dr : ℂ), 0 < T → 0 < T' →
    let al := t * D / (T : ℂ)
    let al' := t * Dr
    let nn := T * ‖al‖ ^ 2 - T' * ‖al'‖ ^ 2
    let G := ‖D‖ ^ 2 - T * T' * ‖Dr‖ ^ 2
    nn = ‖t‖ ^ 2 * G / T ∧
      (0 < nn → 0 < G ∧
        T' * ‖al'‖ ^ 2 / nn = T * T' * ‖Dr‖ ^ 2 / G ∧
        (Dr ≠ 0 →
          let ch := ‖D / Dr‖ / Real.sqrt (T * T')
          let sh := Real.sqrt (ch ^ 2 - 1)
          1 < ch ∧ T * T' * ‖Dr‖ ^ 2 / G = 1 / sh ^ 2) ∧
        (Dr = 0 → T' * ‖al'‖ ^ 2 / nn = 0))
def SignaturePreservingEntryNorms : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (T T' : ℝ) (D Dr : ℂ),
    M.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * M = Formalism.SLP.GlobalBoundRefinements.J → 0 < T → 0 < T' →
    0 < ‖D‖ ^ 2 - T * T' * ‖Dr‖ ^ 2 →
    ‖M 1 0‖ ^ 2 = T * T' * ‖Dr‖ ^ 2 / (‖D‖ ^ 2 - T * T' * ‖Dr‖ ^ 2) →
    (Dr ≠ 0 →
      let ch := ‖D / Dr‖ / Real.sqrt (T * T')
      let sh := Real.sqrt (ch ^ 2 - 1)
      ‖M 1 0‖ = 1 / sh ∧ ‖M 0 1‖ = 1 / sh ∧ ‖M 0 0‖ = ch / sh ∧ ‖M 1 1‖ = ch / sh) ∧
    (Dr = 0 → M 1 0 = 0 ∧ M 0 1 = 0 ∧ ‖M 0 0‖ = 1 ∧ ‖M 1 1‖ = 1)
def AlHypGen : Prop :=
  ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (u u' : ℂ),
    M.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * M = Formalism.SLP.GlobalBoundRefinements.J → ‖u‖ = ‖u'‖ →
    ‖M 0 0 * u + M 0 1 * u'‖ ≤ ‖u‖ * (‖M 0 0‖ + ‖M 1 0‖)
def ThmBEntryGen : Prop :=
  ∀ (M N : Matrix (Fin 2) (Fin 2) ℂ),
    M.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * M = Formalism.SLP.GlobalBoundRefinements.J →
    N.conjTranspose * Formalism.SLP.GlobalBoundRefinements.J * N = Formalism.SLP.GlobalBoundRefinements.J →
    ‖(M * N⁻¹) 1 0‖ ≤ ‖M 1 0‖ * ‖N 0 0‖ + ‖M 0 0‖ * ‖N 1 0‖
def IsInt {E : Type*} [Field E] [NumberField E] (x : E) : Prop :=
  ∃ y : 𝓞 E, (y : E) = x
def LocIn {E : Type*} [Field E] [NumberField E] (P : Ideal (𝓞 E)) (x : E) (N : ℕ) : Prop :=
  ∃ y z : 𝓞 E, y ∉ P ∧ (y : E) * x = (N : E) * (z : E)
def ZZ {E : Type*} [Field E] [NumberField E] (g : ℕ) : Set (E × E) :=
  {p | IsInt p.1 ∧ IsInt p.2 ∧ ∃ w : 𝓞 E, p.1 + p.2 = (g : E) * (w : E)}
def ZZgPreserve : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (a b c d : E),
    (∀ p ∈ (ZZ g : Set (E × E)), (a * p.1 + b * p.2, c * p.1 + d * p.2) ∈ (ZZ g : Set (E × E))) →
    IsInt ((g : E) * a) ∧ IsInt ((g : E) * b) ∧ IsInt ((g : E) * c) ∧ IsInt ((g : E) * d) ∧
      IsInt (a - b) ∧ IsInt (c - d)
def LocalCongr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (P : Ideal (𝓞 E)) (T T' : ℕ) (a b c d : E),
    P.IsPrime → 0 < T → 0 < T' →
    (∀ u v : E, LocIn P ((T : E) * u) 1 → LocIn P ((T' : E) * v) 1 →
      LocIn P ((a - 1) * u + b * v) 1 ∧ LocIn P (c * u + (d - 1) * v) 1) →
    LocIn P (a - 1) T ∧ LocIn P c T ∧ LocIn P b T' ∧ LocIn P (d - 1) T'
def SInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (T T' g : ℕ) (s b c : E),
    0 < T → 0 < T' →
    s = (T' : E) * c * σ c / (T : E) → s = (T : E) * b * σ b / (T' : E) →
    IsInt ((g : E) * b) → IsInt ((g : E) * c) →
    (∀ P : Ideal (𝓞 E), P.IsPrime → (T : 𝓞 E) ∈ P → LocIn P c T) →
    (∀ P : Ideal (𝓞 E), P.IsPrime → (T' : 𝓞 E) ∈ P → LocIn P b T') →
    ∃ β : 𝓞 E, (g : E) ^ 2 * s = (T : E) * (T' : E) * (β : E)
def CMRoot : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (q : ℝ) (x : InfinitePlace E → ℝ),
    (∀ w : InfinitePlace E, w.IsComplex) → 0 < q → (∀ w, 0 ≤ x w) →
    q ^ finrank ℚ E ≤ ∏ w : InfinitePlace E, (x w ^ 2) ^ w.mult →
    q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2) ≤ ∏ w : InfinitePlace E, x w
def ThmB : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E),
    (∀ (φ : E →+* ℂ) (x : E), φ (σ x) = starRingEnd ℂ (φ x)) →
    (∀ w : InfinitePlace E, w.IsComplex) →
    ∀ (T T' g : ℕ) (a b c d : E) (x : InfinitePlace E → ℝ), 3 ≤ T → 3 ≤ T' → 1 ≤ g →
    (∀ (φ : E →+* ℂ) (u v : ℂ),
      T * ‖φ a * u + φ b * v‖ ^ 2 - T' * ‖φ c * u + φ d * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2) →
    (∀ p ∈ (ZZ g : Set (E × E)), (a * p.1 + b * p.2, c * p.1 + d * p.2) ∈ (ZZ g : Set (E × E))) →
    (∀ P : Ideal (𝓞 E), P.IsPrime → ((T : 𝓞 E) ∈ P ∨ (T' : 𝓞 E) ∈ P) →
      LocIn P (a - 1) T ∧ LocIn P c T ∧ LocIn P b T' ∧ LocIn P (d - 1) T') →
    (∀ w : InfinitePlace E, 0 ≤ x w) →
    (∀ w : InfinitePlace E, (T' : ℝ) * w c ^ 2 / T ≤ x w ^ 2) →
    (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨
      ((T : ℝ) * T' / (g : ℝ) ^ 2) ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2) ≤
        ∏ w : InfinitePlace E, x w
def ScalarRatio : Prop :=
  ∀ (K : Type) [Field K] (T t₁ t₂ D₁ D₂ R₁ R₂ : K), T ≠ 0 → t₁ ≠ 0 → t₂ ≠ 0 → D₁ ≠ 0 → D₂ ≠ 0 →
    t₁ * (D₁ / T) = t₂ * (D₂ / T) → t₁ * R₁ = t₂ * R₂ →
    t₁ * D₁ = t₂ * D₂ ∧ t₁ * R₁ = t₂ * R₂ ∧ R₁ / D₁ = R₂ / D₂ ∧ t₁ = (D₂ / D₁) * t₂
end Formalism.HermitianLatticeCounting.LocalIntegralStructure


