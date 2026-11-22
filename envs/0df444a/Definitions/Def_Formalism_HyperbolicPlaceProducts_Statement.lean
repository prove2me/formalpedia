-- Prove2me | Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
-- name    : Formalism_HyperbolicPlaceProducts_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:25.567799+00:00
-- url     : https://prove2.me/theorems/eecd22a9-e25b-4d9e-979f-5455ced28500
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.SLP
def TorsionIndexEq : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (g : ℕ),
    Nat.card A = Nat.card (nsmulAddMonoidHom g : A →+ A).range *
      Nat.card (nsmulAddMonoidHom g : A →+ A).ker
def TorsionIndex : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (g : ℕ) (K : AddSubgroup A),
    (∀ x ∈ K, g • x = 0) →
    Nat.card (nsmulAddMonoidHom g : A →+ A).range * Nat.card K ≤ Nat.card A
def FreeQuotCard : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (g : ℕ),
    Nat.card (X ⧸ (nsmulAddMonoidHom g : X →+ X).range) = g ^ finrank ℤ X
def DetIndexSqInequality : Prop :=
  ∀ (detTh detLa GG i cardB cardGB g : ℝ) (f r : ℕ),
    0 < detLa → 0 < cardB → 0 < g → 0 ≤ i →
    detTh = detLa * i → detTh * cardB = GG → i ≤ cardGB →
    cardGB ≤ cardB / g ^ (2 * f * (r + 1)) →
    detLa * i ^ 2 ≤ GG / g ^ (2 * f * (r + 1))
def DetIndexSqInequalityDiv : Prop :=
  ∀ (detTh detLa GG i cardB cardGB g N : ℝ) (f r : ℕ),
    0 < detLa → 0 < cardB → 0 < g → 0 ≤ i → 0 < N →
    detTh = detLa * i → detTh * cardB = GG → i * N ≤ cardGB →
    cardGB ≤ cardB / g ^ (2 * f * (r + 1)) →
    detLa * i ^ 2 ≤ GG / (g ^ (2 * f * (r + 1)) * N)
def QuotOrderO : Prop :=
  ∀ (R A : Type) [CommRing R] [AddCommGroup A] [Module R A] [Finite A] (K : Submodule R A) (c : A)
    (I : Ideal R), (∀ r : R, r • c ∈ K → r ∈ I) → Nat.card K * Nat.card (R ⧸ I) ≤ Nat.card A
def GInj : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [AddCommGroup B] [Finite B] (g : ℕ) (φ : A →+ B),
    Function.Injective φ →
    Nat.card (nsmulAddMonoidHom g : A →+ A).range ≤ Nat.card (nsmulAddMonoidHom g : B →+ B).range
section Place
variable {𝕜 : Type*} [RCLike 𝕜]
  {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
  [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
def herm {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (x y : V) : 𝕜 :=
  inner 𝕜 y x
def Ph (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') : Submodule 𝕜 W :=
  (LinearMap.ker (φ₁.toLinearMap.comp (Submodule.inclusion (inf_le_left : D₁ ⊓ D₂ ≤ D₁)) -
      φ₂.toLinearMap.comp (Submodule.inclusion (inf_le_right : D₁ ⊓ D₂ ≤ D₂)))).map
    (D₁ ⊓ D₂).subtype
def bb (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') (x₁ : D₁) (x₂ : D₂) :
    𝕜 :=
  herm (x₁ : W) (x₂ : W) - herm (φ₁ x₁) (φ₂ x₂)
def radL (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') : Set W :=
  {x | ∃ hx : x ∈ D₁, ∀ y : D₂, bb D₁ D₂ φ₁ φ₂ ⟨x, hx⟩ y = 0}
def radR (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') : Set W :=
  {y | ∃ hy : y ∈ D₂, ∀ x : D₁, bb D₁ D₂ φ₁ φ₂ x ⟨y, hy⟩ = 0}
end Place
def BBVanish : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
    (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') (x₁ : D₁) (x₂ : D₂),
    ((x₁ : W) ∈ Ph D₁ D₂ φ₁ φ₂ ∨ (x₂ : W) ∈ Ph D₁ D₂ φ₁ φ₂) → bb D₁ D₂ φ₁ φ₂ x₁ x₂ = 0
def BBBound : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 W] [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
    (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') (x₁ : D₁) (x₂ : D₂),
    ‖bb D₁ D₂ φ₁ φ₂ x₁ x₂‖ ≤
      2 * ‖(Ph D₁ D₂ φ₁ φ₂)ᗮ.starProjection (x₁ : W)‖ *
        ‖(Ph D₁ D₂ φ₁ φ₂)ᗮ.starProjection (x₂ : W)‖
def BBPr : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 W] [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
    (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') (x₁ : D₁) (x₂ : D₂),
    ∃ (h₁ : (Ph D₁ D₂ φ₁ φ₂)ᗮ.starProjection (x₁ : W) ∈ D₁)
      (h₂ : (Ph D₁ D₂ φ₁ φ₂)ᗮ.starProjection (x₂ : W) ∈ D₂),
      bb D₁ D₂ φ₁ φ₂ x₁ x₂ = bb D₁ D₂ φ₁ φ₂ ⟨_, h₁⟩ ⟨_, h₂⟩
def RadicalSub : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
    (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W'),
    (Ph D₁ D₂ φ₁ φ₂ : Set W) ⊆ radL D₁ D₂ φ₁ φ₂ ∧ (Ph D₁ D₂ φ₁ φ₂ : Set W) ⊆ radR D₁ D₂ φ₁ φ₂
def RadicalRank : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 W] [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
    (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W'),
    finrank 𝕜 W ≤ finrank 𝕜 D₂ + 1 →
    finrank 𝕜 (Submodule.span 𝕜 (radL D₁ D₂ φ₁ φ₂)) ≤ finrank 𝕜 (Ph D₁ D₂ φ₁ φ₂) + 1
def RadNormal : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 W] [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
    [FiniteDimensional 𝕜 W']
    (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') (x : D₁),
    (x : W) ∈ radL D₁ D₂ φ₁ φ₂ →
    ∃ hx : D₂.starProjection (x : W) ∈ D₂,
      φ₂ ⟨_, hx⟩ = (LinearMap.range φ₂.toLinearMap).starProjection (φ₁ x) ∧
      ‖(x : W) - D₂.starProjection (x : W)‖ =
        ‖φ₁ x - (LinearMap.range φ₂.toLinearMap).starProjection (φ₁ x)‖ ∧
      ((x : W) - D₂.starProjection (x : W) = 0 ↔ (x : W) ∈ Ph D₁ D₂ φ₁ φ₂)
def PsiGeN : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 W] [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
    (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W') (x : W),
    ‖x - D₂.starProjection x‖ ≤ ‖(Ph D₁ D₂ φ₁ φ₂)ᗮ.starProjection x‖
def RadicalEq : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (W W' : Type) [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 W] [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']
    (D₁ D₂ : Submodule 𝕜 W) (φ₁ : D₁ →ₗᵢ[𝕜] W') (φ₂ : D₂ →ₗᵢ[𝕜] W'),
    finrank 𝕜 D₁ = finrank 𝕜 D₂ →
    finrank 𝕜 (Submodule.span 𝕜 (radL D₁ D₂ φ₁ φ₂)) =
      finrank 𝕜 (Submodule.span 𝕜 (radR D₁ D₂ φ₁ φ₂))
def SesqDet : Prop :=
  ∀ (V₁ V₂ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ), (∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖) →
    ∀ (m : ℕ) (u : Fin m → V₁) (w : Fin m → V₂),
      ‖(Matrix.of fun i j => B (u i) (w j)).det‖ ^ 2 ≤
        c ^ (2 * m) * ‖(Matrix.gram ℂ u).det‖ * ‖(Matrix.gram ℂ w).det‖
def IdealNormBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g m : ℕ) (I : Ideal (NumberField.RingOfIntegers E)),
    I ≠ ⊥ → I ≤ Ideal.span {(g : NumberField.RingOfIntegers E)} ^ m →
    g ^ (m * finrank ℚ E) ≤ Ideal.absNorm I
def ElementPlaceBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g m : ℕ) (α : NumberField.RingOfIntegers E), α ≠ 0 →
    α ∈ Ideal.span {(g : NumberField.RingOfIntegers E)} ^ m →
    (g : ℝ) ^ (m * finrank ℚ E) ≤ ∏ w : NumberField.InfinitePlace E, w (α : E) ^ w.mult
def DenomNorm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (α : E) (rr : Ideal (NumberField.RingOfIntegers E)),
    α ≠ 0 → rr ≠ ⊥ → (∀ x ∈ rr, ∃ y : NumberField.RingOfIntegers E, (y : E) = α * (x : E)) →
    1 ≤ |Algebra.norm ℚ α| * (Ideal.absNorm rr : ℚ)
def DetIndexProductInequality : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ i₁ i₂ G0₁ G0₂ g : ℝ) (e f : ℕ),
    0 < dPs₁ → 0 < dPs₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    detM = dLa₁ / dPs₁ → detM = dLa₂ / dPs₂ →
    dLa₁ * i₁ ^ 2 ≤ G0₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dPs₁ * dPs₂ →
    detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂)
def AlDetail : Prop :=
  ∀ (a a' D Dr : ℂ) (T T' G : ℝ) (al : ℂ), 0 < T * T' →
    G = ‖D‖ ^ 2 - T * T' * ‖Dr‖ ^ 2 → 0 < G →
    ‖a'‖ ^ 2 * T' = ‖a‖ ^ 2 * T → a ≠ 0 →
    al = (a * D - a' * (T' : ℂ) * (starRingEnd ℂ) Dr) / (G : ℂ) →
    ‖a' * (T' : ℂ) * Dr‖ < ‖a * D‖ ∧ al ≠ 0 ∧ ‖al‖ ≤ 2 * ‖a‖ * ‖D‖ / G
def AlTheta : Prop :=
  ∀ (al a n D : ℂ) (T G th : ℝ), 0 < T → 0 < G → D ≠ 0 →
    ‖al‖ ≤ 2 * ‖a‖ * ‖D‖ / G → ‖a‖ = ‖n‖ * Real.sqrt (G / T) → th = Real.sqrt G / ‖D‖ →
    Real.sqrt T * ‖al‖ * th ≤ 2 * ‖n‖
def ProductOverPlacesInequality : Prop :=
  ∀ (ι : Type) [Fintype ι] (T al th n : ι → ℝ) (Nr : ℝ),
    (∀ v, 0 < T v) → (∀ v, 0 ≤ al v) → (∀ v, 0 ≤ th v) →
    (∀ v, Real.sqrt (T v) * al v * th v ≤ 2 * n v) → 0 < Nr → 1 ≤ (∏ v, al v ^ 2) * Nr →
    (∏ v, T v) * (∏ v, th v) ^ 2 / Nr ≤ 4 ^ Fintype.card ι * ∏ v, n v ^ 2
def DetIndexProductInequalityOfPlaces : Prop :=
  ∀ (detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT th₁ th₂ Nr₁ Nr₂ : ℝ) (e f : ℕ),
    0 < P₁ → 0 < P₂ → 0 < dQ₁ → 0 < dQ₂ → 0 < g → 0 ≤ i₁ → 0 ≤ i₂ → 0 ≤ dLa₁ → 0 ≤ dLa₂ →
    0 < NT → 0 < th₁ → 0 < th₂ → 0 < Nr₁ → 0 < Nr₂ →
    detM = dLa₁ / dPs₁ → detM = dLa₂ / dPs₂ → dPs₁ = P₁ * dQ₁ → dPs₂ = P₂ * dQ₂ →
    dLa₁ * i₁ ^ 2 ≤ G0₁ / Nr₁ → dLa₂ * i₂ ^ 2 ≤ G0₂ / Nr₂ →
    NT * th₂ ^ 2 / Nr₂ ≤ 4 ^ f * P₁ → NT * th₁ ^ 2 / Nr₁ ≤ 4 ^ f * P₂ →
    g ^ (2 * f * e) ≤ 4 ^ (e * f) * dQ₁ * dQ₂ →
    detM * i₁ * i₂ ≤ 2 ^ (2 * f) * (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) / (NT * th₁ * th₂)
def SubgroupIndexCount : Prop :=
  ∀ (n j : ℕ), 1 ≤ j →
    {H : AddSubgroup (Fin n → ℤ) | H.index = j}.Finite ∧
      {H : AddSubgroup (Fin n → ℤ) | H.index = j}.ncard ≤ j ^ n
def SubmoduleCount : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup M]
    [Module R M] [Finite M] (e : ℕ) (v : Fin e → M), Submodule.span R (Set.range v) = ⊤ →
    Nat.card (Submodule R M) ≤ Nat.card M ^ e
def SubmoduleCountDed : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M]
    [Module R M] [Finite M] (e : ℕ) (v : Fin e → M), Submodule.span R (Set.range v) = ⊤ →
    Nat.card (Submodule R M) ≤ Nat.card M ^ e
def HomKerCount : Prop :=
  ∀ (R Q M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup Q] [Module R Q]
    [AddCommGroup M] [Module R M] [Finite M] (K : Submodule R Q) (e : ℕ) (v : Fin e → M),
    Submodule.span R (Set.range v) = ⊤ →
    Nat.card {φ : Q →ₗ[R] M // LinearMap.ker φ = K} ≤ Nat.card M ^ e
def SubmoduleIndexCountO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (NumberField.RingOfIntegers E) M] [Module.Finite (NumberField.RingOfIntegers E) M]
    [Module.Projective (NumberField.RingOfIntegers E) M] (j : ℕ), 1 ≤ j →
    {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.Finite ∧
      {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.ncard ≤
        finrank ℚ E ^ (Nat.primeFactorsList j).length *
          j ^ finrank (NumberField.RingOfIntegers E) M
def OmegaPow : Prop :=
  ∀ n j : ℕ, 1 ≤ n → 1 ≤ j →
    (n : ℝ) ^ (Nat.primeFactorsList j).length ≤ (j : ℝ) ^ Real.logb 2 n
end Formalism.SLP


