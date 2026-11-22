-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
-- name    : Formalism_QuotientMetricDivisors_RatHermLcvTwist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:37.885009+00:00
-- url     : https://prove2.me/theorems/233c42b9-0e60-4727-9e3c-f7e8cb860b8f
-- title:
--   Rat Herm Lcv Twist
-- statement:
--   Definitions and structural lemmas for Rat Herm Lcv Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/RatHermLcvTwist.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
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
namespace Formalism.DivisionValues
def IsHermAt {K : Type} [Field K] [NumberField K] (v0 : InfinitePlace K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ v : InfinitePlace K, IsUnit (X v).det) ∧
    ((X v0)⁻¹).conjTranspose * (X v0)⁻¹ = H.map v0.embedding
def cmMax (K : Type) [Field K] [StarRing K] : Subfield K where
  carrier := {a | ∀ σ : K →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)}
  mul_mem' := by
    intro a b ha hb σ
    rw [star_mul', map_mul, map_mul, map_mul, ha σ, hb σ]
  one_mem' := by intro σ; simp
  add_mem' := by
    intro a b ha hb σ
    rw [star_add, map_add, map_add, map_add, ha σ, hb σ]
  zero_mem' := by intro σ; simp
  neg_mem' := by
    intro a ha σ
    rw [star_neg, map_neg, map_neg, map_neg, ha σ]
  inv_mem' := by
    intro a ha σ
    rw [star_inv₀, map_inv₀, map_inv₀, map_inv₀, ha σ]
def twist {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) : K →+* ℂ :=
  (starRingEnd ℂ).comp (σ.comp (starRingEnd K))
def embSpan {K : Type} [Field K] {n : ℕ} (σ : K →+* ℂ) (Z : Submodule K (Fin n → K)) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun z i => σ (z i)) '' (Z : Set (Fin n → K)))
def comb {K : Type} [Field K] {n d : ℕ} (z : Fin d → Fin n → K) (x : Fin d → K) : Fin n → K :=
  ∑ a, x a • z a
def gramMat {K : Type} [Field K] [StarRing K] {n d : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (z : Fin d → Fin n → K) : Matrix (Fin d) (Fin d) K :=
  Matrix.of fun a b => star (z a) ⬝ᵥ H.mulVec (z b)
def JwGramW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (H : Matrix (Fin d) (Fin d) K),
    (∀ i j, H j i = star (H i j)) → H.det ≠ 0 →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K), IsLocBasis T w f →
      jw H w T = - vw w (gramR H f)
def JwConjW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (H : Matrix (Fin d) (Fin d) K),
    (∀ i j, H j i = star (H i j)) → H.det ≠ 0 →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
    ∀ w : HeightOneSpectrum (𝓞 K), jw H (conjPl w) T = jw H w T
def StepBW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
      (XT : ∀ j, Tup → InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K)), (∀ j t, Submodule.IsLattice K (T j t)) →
    ∀ (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρ : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρ t) = (ρr t : ℂ)) → ρ μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρ (μ w)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (G : Tup → HeightOneSpectrum (𝓞 K) → K)
      (e : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t w, IsLocBasis (abelian₂ t) w (e t w)) →
    (∀ t w, v0.embedding (G t w) = (gram (XQ t) v0 (e t w)).det) →
    (lcv (XQ μ0) (abelian₂ μ0) ≤ ∑ᶠ w, lw w * (vw w (G μ0 w) : ℝ)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))).Finite ∧
      lcv XE R ≤ (D : ℝ) * meanLog κ + ∑ j, lcv (XW j) (M j) +
        ∑ᶠ w, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
          ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))
def StepBRW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
      (XT : ∀ j, Tup → InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K)), (∀ j t, Submodule.IsLattice K (T j t)) →
    ∀ (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρ : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρ t) = (ρr t : ℂ)) → ρ μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρ (μ w)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (G : Tup → HeightOneSpectrum (𝓞 K) → K)
      (e : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t w, IsLocBasis (abelian₂ t) w (e t w)) →
    (∀ t w, v0.embedding (G t w) = (gram (XQ t) v0 (e t w)).det) →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec → IsQuotMetric P H (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat P Mt →
    (∀ w, G μ0 w = gramR (quotGram P H) (e μ0 w)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      (Function.support fun w => lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
        ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
         (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))).Finite ∧
      lcv XE R ≤ (D : ℝ) * meanLog κ + ∑ j, lcv (XW j) (M j) +
        ∑ᶠ w, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j,
          ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
           (jw (HT j (μ w)) w (T j (μ w)) : ℝ)))
def BoundsChainW : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (D : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ v, IsUnit (XE v).det) →
    ∀ (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (XQ : Tup → InfinitePlace K → Matrix (Fin D) (Fin D) ℂ), (∀ t v, IsUnit (XQ t v).det) →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ), (∀ j v, IsUnit (XW j v).det) →
    ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K)), (∀ j, Submodule.IsLattice K (M j)) →
    ∀ (HT : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
      (XT : ∀ j, Tup → InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
      (∀ j, IsRatHerm K0 (HT j μ0) (XT j μ0)) → (∀ j t, IsHermAt v0 (HT j t) (XT j t)) →
    ∀ (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K)), (∀ j t, Submodule.IsLattice K (T j t)) →
    ∀ (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K), (∀ j t, IsUnit (θ j t).det) →
    ∀ (κ : InfinitePlace K → ℝ), (∀ v, 0 < κ v) →
    ∀ (ρ : Tup → K) (ρr : Tup → ℝ), (∀ t, v0.embedding (ρ t) = (ρr t : ℂ)) → ρ μ0 = 1 →
    (∀ t, 0 < ρr t) → (∀ w, vw w (ρ (μ w)) = 0) →
    (∀ v, detRatio (XQ μ0) XE (ι μ0) v = κ v ^ D * ∏ j, detRatio (XT j μ0) (XW j) (θ j μ0) v) →
    (∀ t, detRatio (XQ t) XE (ι t) v0 =
      (κ v0 * ρr t) ^ D * ∏ j, detRatio (XT j t) (XW j) (θ j t) v0) →
    ∀ (G : Tup → HeightOneSpectrum (𝓞 K) → K)
      (e : Tup → HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K),
    (∀ t w, IsLocBasis (abelian₂ t) w (e t w)) →
    (∀ t w, v0.embedding (G t w) = (gram (XQ t) v0 (e t w)).det) →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec → IsQuotMetric P H (XQ μ0) →
    ∀ Mt : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K Mt → abelian₂ μ0 = matLat P Mt →
    (∀ w, G μ0 w = gramR (quotGram P H) (e μ0 w)) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 K))),
    (∀ w ∉ S, lw w * ((vw w (G (μ w) w) : ℝ) + ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) + (jw (HT j (μ w)) w (T j (μ w)) : ℝ))) = 0) →
    ∀ (LG E3 : ℝ) (L E1 E2 : J → ℝ) (ell g : HeightOneSpectrum (𝓞 K) → ℝ)
      (F err Jx η : HeightOneSpectrum (𝓞 K) → J → ℝ),
    0 < D →
    (∀ w ∈ S, (vw w (G (μ w) w) : ℝ) ≤ (D : ℝ) * g w) → ∑ w ∈ S, lw w * g w ≤ LG →
    (∀ j, lcv (XW j) (M j) / D ≤ L j) →
    (∀ w ∈ S, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
        (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
      (∑ j, (2 * F w j + err w j) + 2 / ell w ^ 2) * D) →
    (∀ w ∈ S, ∀ j, (jw (HT j (μ w)) w (T j (μ w)) : ℝ) ≤ Jx w j * D + η w j) →
    (∀ j, ∑ w ∈ S, lw w * (err w j + Jx w j) ≤ E1 j) →
    (∀ j, ∑ w ∈ S, lw w * η w j / D ≤ E2 j) →
    ∑ w ∈ S, lw w * (2 / ell w ^ 2) ≤ E3 →
      lcv XE R / D ≤ meanLog κ + ∑ j, L j + 2 * ∑ j, ∑ w ∈ S, lw w * F w j + LG +
        ∑ j, (E1 j + E2 j) + E3
def CmMaxSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    IsCMSub (cmMax K) ∧ (∀ K0 : Subfield K, IsCMSub K0 → K0 ≤ cmMax K) ∧
    (∀ a ∈ cmMax K, star a ∈ cmMax K) ∧
    ∀ a : K, a ∈ cmMax K ↔ ∀ σ : K →+* ℂ, twist σ a = σ a
def DescentCM : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ) (Z : Submodule K (Fin n → K)),
    (∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z) →
    ∃ (d : ℕ) (z : Fin d → Fin n → K), LinearIndependent K z ∧
      Submodule.span K (Set.range z) = Z ∧ ∀ a i, z a i ∈ cmMax K
def DescentCMConv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (z : Fin d → Fin n → K),
    (∀ a i, z a i ∈ cmMax K) →
    ∀ σ : K →+* ℂ, embSpan σ (Submodule.span K (Set.range z)) =
      embSpan (twist σ) (Submodule.span K (Set.range z))
def RestrictRatHerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    (∀ a ∈ K0, star a ∈ K0) →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    IsRatHerm K0 H X →
    ∀ (d : ℕ) (z : Fin d → Fin n → K), LinearIndependent K z → (∀ a i, z a i ∈ K0) →
    ∃ XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, IsRatHerm K0 (gramMat H z) XT ∧
      (∀ (v : InfinitePlace K) (x y : Fin d → K),
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v x y =
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (comb z x) (comb z y)) ∧
      ∀ x y : Fin d → K, hform (gramMat H z) x y = hform H (comb z x) (comb z y)
def RestrictHermAt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K) (v0 : InfinitePlace K),
    IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    IsRatHerm K0 H X →
    ∀ (d : ℕ) (z : Fin d → Fin n → K), LinearIndependent K z →
    ∃ XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, IsHermAt v0 (gramMat H z) XT ∧
      (∀ (v : InfinitePlace K) (x y : Fin d → K),
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v x y =
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (comb z x) (comb z y)) ∧
      ∀ x y : Fin d → K, hform (gramMat H z) x y = hform H (comb z x) (comb z y)
def RatHermLcvTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    IsRatHerm K0 H X →
    ∀ Z : Submodule K (Fin n → K), (∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z) →
    ∃ (d : ℕ) (z : Fin d → Fin n → K) (XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
      LinearIndependent K z ∧ Submodule.span K (Set.range z) = Z ∧
      IsRatHerm (cmMax K) (gramMat H z) XT ∧
      (∀ (v : InfinitePlace K) (x y : Fin d → K),
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v x y =
          Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (comb z x) (comb z y)) ∧
      (∀ x y : Fin d → K, hform (gramMat H z) x y = hform H (comb z x) (comb z y)) ∧
      ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
        (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
          lw w * (jw (gramMat H z) w T : ℝ)).Finite ∧
        lcv XT T = - ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (jw (gramMat H z) w T : ℝ)
end Formalism.DivisionValues


