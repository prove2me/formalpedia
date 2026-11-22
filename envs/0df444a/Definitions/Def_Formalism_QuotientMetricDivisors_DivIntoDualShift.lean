-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
-- name    : Formalism_QuotientMetricDivisors_DivIntoDualShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:50:02.135418+00:00
-- url     : https://prove2.me/theorems/391bd144-980f-40e0-8546-533859464ab1
-- title:
--   Div Into Dual Shift
-- statement:
--   Definitions and structural lemmas for Div Into Dual Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/DivIntoDualShift.lean

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
open scoped Matrix nonZeroDivisors
noncomputable section
namespace Formalism.DivisionValues
section Defs
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def smulLat {d : ℕ} (a : K) (N : Submodule (𝓞 K) (Fin d → K)) : Submodule (𝓞 K) (Fin d → K) :=
  N.map ((LinearMap.lsmul K (Fin d → K) a).restrictScalars (𝓞 K))
def IsShiftAt {d : ℕ} (w : HeightOneSpectrum (𝓞 K)) (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ) :
    Prop :=
  ∃ a : K, a ≠ 0 ∧ vw w a = -s ∧
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N)
def IsShift {d : ℕ} (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℤ) : Prop :=
  ∀ w, IsShiftAt w N N' (σ w)
def shiftIdeal (σ : HeightOneSpectrum (𝓞 K) → ℤ) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-σ w)
def Above (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) : Prop := (p : 𝓞 K) ∈ w.asIdeal
end Defs
def ShiftAtIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ),
    (∃ a : K, a ≠ 0 ∧ vw w a = -s) ∧
    (IsShiftAt w N N' s ↔ ∀ a : K, a ≠ 0 → vw w a = -s →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N))
def ShiftIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N N' : Submodule (𝓞 K) (Fin d → K)), Submodule.IsLattice K N →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (s : ℤ), IsShiftAt w N N' s →
      idx w N N' = -((d : ℤ) * s)
def MuLcv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ N : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K N →
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N = -(lcv X N) / d
def ShiftMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), (∀ v, IsUnit (X v).det) →
    ∀ N N' : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K N → Submodule.IsLattice K N' →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, IsShift N N' σ →
      lcv X N' = lcv X N - 2 * (d : ℝ) * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ) ∧
      (0 < d → (Function.support σ).Finite ∧
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' =
          Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
            2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w : ℝ))
def ShiftEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ)
    (N : Submodule (𝓞 K) (Fin d → K)), Submodule.IsLattice K N →
    ∀ σ : HeightOneSpectrum (𝓞 K) → ℤ, (Function.support σ).Finite →
      IsShift N (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) σ ∧
      Submodule.IsLattice K (Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N) ∧
      ∀ N' : Submodule (𝓞 K) (Fin d → K), IsShift N N' σ →
        N' = Formalism.HermitianLatticesTheory.idealSmul (shiftIdeal σ : Submodule (𝓞 K) K) N
def LwSumPrime : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (p : ℕ), p.Prime →
    {w : HeightOneSpectrum (𝓞 K) | Above p w}.Finite ∧
    (∃ w : HeightOneSpectrum (𝓞 K), Above p w) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), Above p w ↔ 0 < vw w (p : K)) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), 0 < lw w) ∧
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (vw w (p : K) : ℝ) = Real.log p ∧
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w ≤ Real.log p ∧
    ∀ e : ℤ, (∀ w : HeightOneSpectrum (𝓞 K), Above p w → vw w (p : K) = e) →
      ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w = Real.log p / e
def RoundingSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (σ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
    (∀ w, ((⌊σ w⌋ : ℤ) : ℝ) ≠ σ w → ∃ p ∈ S, Above p w) →
      (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (σ w - (⌊σ w⌋ : ℤ))).Finite ∧
      0 ≤ 2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w - (⌊σ w⌋ : ℤ)) ∧
      2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * (σ w - (⌊σ w⌋ : ℤ)) ≤
        ∑ p ∈ S, 2 * ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w ∧
      ∑ p ∈ S, 2 * ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : Above p w), lw w ≤
        ∑ p ∈ S, 2 * Real.log p
def RoundingCost : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ N N' : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K N → Submodule.IsLattice K N' →
    ∀ (σ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
    (∀ w, ((⌊σ w⌋ : ℤ) : ℝ) ≠ σ w → ∃ p ∈ S, Above p w) →
    IsShift N N' (fun w => ⌊σ w⌋) →
      (Function.support σ).Finite ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' ≤
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
          2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * σ w ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
                2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * σ w) - ∑ p ∈ S, 2 * Real.log p ≤
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N'
def RoundingUp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (d : ℕ), 0 < d →
    ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ N N' : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K N → Submodule.IsLattice K N' →
    ∀ (σ : HeightOneSpectrum (𝓞 K) → ℝ) (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
    (∀ w, ((⌈σ w⌉ : ℤ) : ℝ) ≠ σ w → ∃ p ∈ S, Above p w) →
    IsShift N N' (fun w => ⌈σ w⌉) →
      (Function.support σ).Finite ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
                2 * ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * σ w ≤
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' ∧
      Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N' ≤
        Formalism.HN.muDef (Pi.basisFun K (Fin d)) X N +
          2 * (∑ᶠ w : HeightOneSpectrum (𝓞 K), lw w * σ w) + ∑ p ∈ S, 2 * Real.log p
def RoundingTheta : Prop :=
  ∀ Y : ℝ, 0 ≤ Y → ∑ p ∈ (Finset.range (⌊Y⌋₊ + 1)).filter Nat.Prime, 2 * Real.log p ≤ 3 * Y
def ShiftPairing : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d : ℕ) (w : HeightOneSpectrum (𝓞 K))
    (N N' : Submodule (𝓞 K) (Fin d → K)) (s : ℤ), IsShiftAt w N N' s →
    ∀ f : (Fin d → K) →ₗ[K] K, (∀ φ ∈ N, f φ = 0 ∨ s ≤ vw w (f φ)) →
      ∀ φ ∈ N', f φ = 0 ∨ 0 ≤ vw w (f φ)
def DivIntoDualShift : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (d D : ℕ)
    (R : Submodule (𝓞 K) (Fin D → K)) (B : (Fin d → K) →ₗ[K] (Fin D → K) →ₗ[K] K)
    (n : HeightOneSpectrum (𝓞 K) → ℕ) (M : ∀ w, Submodule (𝓞 K) (Fin (n w) → K))
    (π : ∀ w, Matrix (Fin D) (Fin (n w)) K) (ι : HeightOneSpectrum (𝓞 K) → Matrix (Fin D) (Fin D) K)
    (P : ∀ w, (Fin d → K) →ₗ[K] (Fin (n w) → K) →ₗ[K] K) (ζ : HeightOneSpectrum (𝓞 K) → K),
    (∀ w, ζ w ≠ 0) → (∀ w, vw w (ζ w) = 0) →
    (∀ w (φ : Fin d → K) (F : Fin (n w) → K),
      P w φ F = ζ w * B φ ((ι w).mulVec ((π w).mulVec F))) →
    ∀ (N N' : Submodule (𝓞 K) (Fin d → K)) (σ : HeightOneSpectrum (𝓞 K) → ℝ)
      (τ : HeightOneSpectrum (𝓞 K) → ℤ),
    (∀ w, ∀ φ ∈ N, ∀ F ∈ M w, P w φ F = 0 ∨ σ w ≤ (vw w (P w φ F) : ℝ)) →
    (∀ w, τ w ≤ ⌈σ w⌉) → IsShift N N' τ →
    (∀ w, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι w) (matLat (π w) (M w)))) →
    ∀ φ ∈ N', ∀ x ∈ R, B φ x ∈ Set.range (algebraMap (𝓞 K) K)
end Formalism.DivisionValues


