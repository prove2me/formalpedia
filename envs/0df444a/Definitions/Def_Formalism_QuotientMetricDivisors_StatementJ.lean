-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_StatementJ
-- name    : Formalism_QuotientMetricDivisors_StatementJ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:44.022612+00:00
-- url     : https://prove2.me/theorems/f68bbe70-f72e-42f9-a03e-a6cd0b13aef4
-- title:
--   Statement J
-- statement:
--   Definitions and structural lemmas for Statement J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/StatementJ.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
import Definitions.Def_Formalism_LogFactorialIndices_StatementSize
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
def StepBR : Prop :=
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
def DivAssembly : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (muC mu0 Lpass logκ Fo Eb hu hP mlam e6 eP logOm logT kk : ℝ)
    (hK eK pq : J → ℝ) (a : Pl → ℝ) (w phν nν fa eE δ : J → Pl → ℝ),
    muC ≤ mu0 + Lpass →
    mu0 ≤ logκ + ∑ j, ∑ ρ, pq j * w j ρ * logOm + 2 * Fo + Eb →
    hu = hP + ∑ j, hK j - mlam - logκ →
    (∀ j, hK j ≤ ∑ ρ, (phν j ρ - nν j ρ * logOm) + eK j) →
    ∑ j, ∑ ρ, fa j ρ - e6 ≤ mlam →
    hP ≤ -(∑ t ∈ TT, a t * logT) + eP →
    (∀ j ρ, phν j ρ - fa j ρ ≤ (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) else 0) + eE j ρ) →
    (∀ j ρ, nν j ρ = (if ρ ∈ TT then a ρ else 0) + kk * w j ρ + δ j ρ) →
      muC + hu - 2 * Fo ≤
        ∑ t ∈ TT, ((Fintype.card J : ℝ) * (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) - a t * logT) +
        (Lpass + Eb + ∑ j, eK j + e6 + eP + ∑ j, ∑ ρ, eE j ρ) +
        ∑ j, ∑ ρ, |pq j - kk| * |w j ρ| * |logOm| + ∑ j, ∑ ρ, |δ j ρ| * |logOm|
end Formalism.DivisionValues


