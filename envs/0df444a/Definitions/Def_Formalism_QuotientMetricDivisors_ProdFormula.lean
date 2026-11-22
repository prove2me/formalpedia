-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
-- name    : Formalism_QuotientMetricDivisors_ProdFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:41:39.841095+00:00
-- url     : https://prove2.me/theorems/89c1b157-4764-4a8d-a8fd-48c395ee41b6
-- title:
--   Prod Formula
-- statement:
--   Definitions and structural lemmas for Prod Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/ProdFormula.lean

import Mathlib
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
namespace Formalism.DivisionValues
def ProdFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (a : K), a ≠ 0 →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)).Finite ∧
    (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ =
      ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w a : ℝ)
def DetCS : Prop :=
  ∀ (n D : ℕ) (Hc : Matrix (Fin n) (Fin n) ℂ), Hc.PosDef →
    ∀ A B : Matrix (Fin D) (Fin n) ℂ,
      ‖(A * Hc * Bᴴ).det‖ ^ 2 ≤ (A * Hc * Aᴴ).det.re * (B * Hc * Bᴴ).det.re
def LcvBasis : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) =>
        lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)).Finite ∧
      lcv X L = (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (gram X v e).det.re +
        2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w (Submodule.span (𝓞 K) (Set.range e)) L : ℝ)
def IdxChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (L : Submodule (𝓞 K) (Fin d → K)), Submodule.IsLattice K L →
    ∀ e : Fin d → Fin d → K, LinearIndependent K e →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (γ : Matrix (Fin d) (Fin d) K),
      IsLocBasis L w (fun i => ∑ k, γ k i • e k) →
      idx w (Submodule.span (𝓞 K) (Set.range e)) L = vw w γ.det ∧
      idx (conjPl w) (Submodule.span (𝓞 K) (Set.range e)) L = vw (conjPl w) γ.det
def ValBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ a b : K, a ≠ 0 → b ≠ 0 → vw w (a * b) = vw w a + vw w b) ∧
    (∀ a : K, vw w (star a) = vw (conjPl w) a) ∧
    lw (conjPl w) = lw w ∧ conjPl (conjPl w) = w ∧ vw w 1 = 0 ∧
    (∀ a : K, vw w a⁻¹ = - vw w a) ∧
    (∀ a : 𝓞 K, 0 ≤ vw w (a : K))
def GramChange : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (D m : ℕ) (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) (γ : Matrix (Fin m) (Fin m) K),
      gramR Γ (fun i => ∑ k, γ k i • e k) = star γ.det * γ.det * gramR Γ e
def ImageLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ)
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (XS v).det) →
    (∀ v, IsUnit (XT v).det) →
    ∀ φ : Matrix (Fin d) (Fin d) K, IsUnit φ.det →
    ∀ L : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K L →
      lcv XT (matLat φ L) = lcv XS L + (2 / (finrank ℚ K : ℝ)) * ∑ v, Real.log (detRatio XS XT φ v)
def IdxLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ A B : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K A → Submodule.IsLattice K B →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (idx w A B : ℝ)).Finite ∧
      lcv X B = lcv X A + 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (idx w A B : ℝ)
def RatHermLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (jw H w T : ℝ)).Finite ∧
      lcv X T = - ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (jw H w T : ℝ)
def JwGram : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (f : Fin d → Fin d → K), IsLocBasis T w f →
      jw H w T = - vw w (gramR H f)
def FinsumConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (f : HeightOneSpectrum (𝓞 K) → ℝ),
    ∑ᶠ w, f (conjPl w) = ∑ᶠ w, f w
def LocBasisEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (L : Submodule (𝓞 K) (Fin d → K)),
    Submodule.IsLattice K L → ∀ w : HeightOneSpectrum (𝓞 K), ∃ f : Fin d → Fin d → K, IsLocBasis L w f
end Formalism.DivisionValues


