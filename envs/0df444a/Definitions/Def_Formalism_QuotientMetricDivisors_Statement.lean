-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_Statement
-- name    : Formalism_QuotientMetricDivisors_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:44.726039+00:00
-- url     : https://prove2.me/theorems/294787e3-f9ee-468c-acde-12b51c7c5000
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/Statement.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HermitianLattices_StatementLat
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
section Defs
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (K) in

def cO : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (starRingAut (R := K))
def conjPl (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.map (cO K)
  isPrime := Ideal.map_isPrime_of_equiv _
  ne_bot := by
    intro h
    apply w.ne_bot
    exact (Ideal.map_eq_bot_iff_of_injective (cO K).injective).mp h
def vw (w : HeightOneSpectrum (𝓞 K)) (a : K) : ℤ :=
  FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a)
def lw (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (finrank ℚ K : ℝ)
def lcv {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (L : Submodule (𝓞 K) (Fin d → K)) : ℝ :=
  (2 / (finrank ℚ K : ℝ)) * Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X L)
def gram {d m : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (e : Fin m → Fin d → K) : Matrix (Fin m) (Fin m) ℂ :=
  Formalism.HN.gramPl (Pi.basisFun K (Fin d)) X v e
def detRatio {d d' : ℕ} (XS : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (XT : InfinitePlace K → Matrix (Fin d') (Fin d') ℂ) (φ : Matrix (Fin d') (Fin d) K)
    (v : InfinitePlace K) : ℝ :=
  (gram XT v (fun i => φ.mulVec (Pi.single i 1))).det.re /
    (gram XS v (fun i => (Pi.single i 1 : Fin d → K))).det.re
def hform {n : ℕ} (H : Matrix (Fin n) (Fin n) K) :
    (Fin n → K) →ₗ⋆[K] (Fin n → K) →ₗ[K] K :=
  Matrix.toLinearMapₛₗ₂' K (starRingEnd K) (RingHom.id K) H
def IsCMSub (K0 : Subfield K) : Prop :=
  ∀ (σ : K →+* ℂ) (a : K), a ∈ K0 → σ (star a) = starRingEnd ℂ (σ a)
def IsConjAt (v0 : InfinitePlace K) : Prop :=
  ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a)
def IsRatHerm (K0 : Subfield K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j, H i j ∈ K0) ∧ ∀ v : InfinitePlace K,
    IsUnit (X v).det ∧ ((X v)⁻¹).conjTranspose * (X v)⁻¹ = H.map v.embedding
def IsQuotMetric {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K)
    (XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ v : InfinitePlace K, IsUnit (XQ v).det ∧
    ((XQ v)⁻¹).conjTranspose * (XQ v)⁻¹ =
      ((P.map v.embedding) * (H.map v.embedding)⁻¹ * (P.map v.embedding).conjTranspose)⁻¹
def quotGram {n D : ℕ} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin D) (Fin D) K :=
  (P * H⁻¹ * P.conjTranspose)⁻¹
def gramR {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K) (e : Fin m → Fin D → K) : K :=
  (Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b)).det
def IsLocBasis {D : ℕ} (L : Submodule (𝓞 K) (Fin D → K)) (w : HeightOneSpectrum (𝓞 K))
    (e : Fin D → Fin D → K) : Prop :=
  LinearIndependent K e ∧
    Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range e)) =
      Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal L
def matLat {d d' : ℕ} (φ : Matrix (Fin d') (Fin d) K) (L : Submodule (𝓞 K) (Fin d → K)) :
    Submodule (𝓞 K) (Fin d' → K) :=
  L.map ((Matrix.mulVecLin φ).restrictScalars (𝓞 K))
def idx {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) (Fin d → K)) : ℤ :=
  Formalism.HermitianLatticesTheory.lidx w.asIdeal A B
def jw {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (w : HeightOneSpectrum (𝓞 K))
    (A : Submodule (𝓞 K) (Fin d → K)) : ℤ :=
  Formalism.HermitianLatticesTheory.jIdx (hform H) w.asIdeal A
def meanLog (κ : InfinitePlace K → ℝ) : ℝ :=
  (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (κ v)
end Defs
def GramDeterminantQuotientMetric : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n D : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ e : Fin D → Fin D → K,
      star (gramR (quotGram P H) e) = gramR (quotGram P H) e ∧
      v0.embedding (gramR (quotGram P H) e) = (gram XQ v0 e).det
def LemmaRa : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n D : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ M : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K M →
    ∀ (l g : ℕ), 0 < l → (∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H) M, ((l : 𝓞 K) ^ g) • x ∈ M) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (e : Fin D → Fin D → K), IsLocBasis (matLat P M) w e →
      vw w (gramR (quotGram P H) e) ≤ (g : ℤ) * (D : ℤ) * vw w (l : K)
def LemmaRb : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n D : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ P : Matrix (Fin D) (Fin n) K, Function.Surjective P.mulVec →
    ∀ XQ : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, IsQuotMetric P H XQ →
    ∀ M : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K M →
    ∀ e : HeightOneSpectrum (𝓞 K) → Fin D → Fin D → K, (∀ w, IsLocBasis (matLat P M) w (e w)) →
      (Function.support fun w => lw w * (vw w (gramR (quotGram P H) (e w)) : ℝ)).Finite ∧
      lcv XQ (matLat P M) ≤ ∑ᶠ w, lw w * (vw w (gramR (quotGram P H) (e w)) : ℝ)
def SpecDet : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K) (D : ℕ)
    (XQ XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ),
    (∀ u, IsUnit (XQ u).det) → (∀ u, IsUnit (XE u).det) →
    ∀ ι : Matrix (Fin D) (Fin D) K, IsUnit ι.det →
    ∀ (J : Type) [Fintype J] (d : J → ℕ)
      (XT XW : ∀ j, InfinitePlace K → Matrix (Fin (d j)) (Fin (d j)) ℂ),
    (∀ j u, IsUnit (XT j u).det) → (∀ j u, IsUnit (XW j u).det) →
    ∀ θ : ∀ j, Matrix (Fin (d j)) (Fin (d j)) K, (∀ j, IsUnit (θ j).det) →
    ∀ (Ix : Type) [Fintype Ix] (Qp : Ix → Submodule K (Fin D → K))
      (Tq : ∀ j, Ix → Submodule K (Fin (d j) → K)),
    iSupIndep Qp → (⨆ p, Qp p) = ⊤ → (∀ j, iSupIndep (Tq j)) → (∀ j, (⨆ p, Tq j p) = ⊤) →
    (∀ j p, finrank K (Qp p) = finrank K (Tq j p)) →
    ∀ (s : ℝ) (lam : J → Ix → ℝ),
    (∀ p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v (ι.mulVec x) (ι.mulVec y) =
        ((s * ∏ j, lam j p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XQ v x y) →
    (∀ j p, ∀ x ∈ Tq j p, ∀ y : Fin (d j) → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (d j))) (XW j) v ((θ j).mulVec x) ((θ j).mulVec y) =
        ((lam j p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (d j))) (XT j) v x y) →
      detRatio XQ XE ι v = s ^ D * ∏ j, detRatio (XT j) (XW j) (θ j) v
def StepB : Prop :=
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
      (∀ j t, IsRatHerm K0 (HT j t) (XT j t)) →
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
end Formalism.DivisionValues


