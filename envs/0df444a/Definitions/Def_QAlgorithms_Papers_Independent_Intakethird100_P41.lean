-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P41
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P41
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:50:07.944869+00:00
-- url     : https://prove2.me/theorems/26344d74-9ff8-469a-92fc-d5b1bd2a3f8e
-- title:
--   Definitions for Entanglement Renyi entropies in holographic theories
-- statement:
--   The objects the formalized statements of *Entanglement Renyi entropies in holographic theories* (arXiv:1006.0047) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `densityPerturbation`: PDF p.7, (2.8): the affine density-operator perturbation, with real parameter.
--   - `IsSupportPreservingPerturbation`: PDF p.7: normalized Hermitian perturbations with unchanged occupied support for small real parameters of both signs. For Hermitian finite matrices, the kernel condition on rho1 is equivalent to image(rho1) being contained in image(rho0). The final condition states equality of occupied supports near zero, rather than assuming an entropy formula.
--   - `occupiedPower`: PDF pp.5,7: spectral powers on occupied support, extended by zero on the kernel. In particular a negative exponent never assigns an infinite value to a zero eigenvalue.
--   - `regulatedRenyiNats`: PDF p.5, (2.1)-(2.2): reuse the accepted natural-log Renyi entropy after reindexing an arbitrary finite basis to Fin(card I). This is only a basis adapter; it preserves the accepted order-zero rank and order-one entropy branches. The theorems below use positive orders.
--   - `mutualRenyiNats`: PDF pp.7-8, (2.7),(2.12): mutual Renyi information from the actual two partial traces.
--   - `centeredPower`: PDF p.8, (2.12): the centered, normalized spectral factor. Subtracting the full identity is harmless off occupied support because the perturbation annihilates it.
--   - `cosecantPowerSum`: PDF p.36, (A.22): the sine sum at k = 2d. The endpoint n = 1 is an empty sum. At n = 0 the definition also returns zero, but the theorem excludes that input.
--   - `binomialDenominator`: PDF p.37, (A.24)-(A.25): polynomial coefficients of ((1+u)^n-1)/(n*u). The coefficient of u^m is (n-1)...(n-m)/(m+1)!. The empty product is one. The variable of each coefficient polynomial represents n, not u.
--   - `sineSumPolynomial`: PDF p.37, (A.24)-(A.25): explicit polynomial obtained from minus the residue at t=1. Removing the Laurent factor u^-1 changes coefficient 2k-1 to coefficient 2k. The inverse uses constant coefficient one, so this is a construction over R[n], not an existence choice or interpolation axiom.
--   - `residueCoefficient`: PDF p.37, (A.24): scalar version of the residue coefficient for an integer n. For n>=1 this denominator series has constant coefficient one.
--   - `scalarPairContinuation`: PDF p.36, (A.22): the specified continuation of the scalar-pair coefficient. For k=2d and t>0 this is t^(1-4d) P_k(t)/2. It is not claimed to be the unique analytic interpolation among arbitrary analytic functions.
-- source:
--   Entanglement Renyi entropies in holographic theories, arXiv:1006.0047v3, https://arxiv.org/abs/1006.0047v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
Statements from Headrick, arXiv:1006.0047v3. PDF page numbers are used throughout.
Section 2.2 is stated on arbitrary finite occupied-support realizations of regulated
systems; no infinite-rank differentiability assertion is made. The CFT and geometric
results without a constructed interface are individually recorded in HARD.md.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P41

open Filter
open QAlgorithms.Papers.Independent.Information100.P56 (entropy)
open scoped Topology

/-- PDF p.7, (2.8): the affine density-operator perturbation, with real parameter. -/
noncomputable def densityPerturbation {I : Type*} [Fintype I]
    (rho0 rho1 : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  rho0 + (t : ℂ) • rho1

/-- PDF p.7: normalized Hermitian perturbations with unchanged occupied support for
small real parameters of both signs. For Hermitian finite matrices, the kernel condition
on rho1 is equivalent to image(rho1) being contained in image(rho0). The final condition
states equality of occupied supports near zero, rather than assuming an entropy formula. -/
def IsSupportPreservingPerturbation {I : Type*} [Fintype I]
    (rho0 rho1 : Matrix I I ℂ) : Prop :=
  QAlgorithms.IsDensityMatrix rho0 ∧ rho1.IsHermitian ∧ rho1.trace = 0 ∧
  (∀ v : I → ℂ, rho0.mulVec v = 0 → rho1.mulVec v = 0) ∧
  ∀ᶠ t : ℝ in 𝓝 0,
    QAlgorithms.IsDensityMatrix (densityPerturbation rho0 rho1 t) ∧
    ∀ v : I → ℂ,
      (densityPerturbation rho0 rho1 t).mulVec v = 0 ↔ rho0.mulVec v = 0

/-- PDF pp.5,7: spectral powers on occupied support, extended by zero on the kernel.
In particular a negative exponent never assigns an infinite value to a zero eigenvalue. -/
noncomputable def occupiedPower {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  cfc (fun x : ℝ => if x = 0 then 0 else Real.rpow x a) rho

/-- PDF p.5, (2.1)-(2.2): reuse the accepted natural-log Renyi entropy after
reindexing an arbitrary finite basis to Fin(card I). This is only a basis adapter;
it preserves the accepted order-zero rank and order-one entropy branches.
The theorems below use positive orders. -/
noncomputable def regulatedRenyiNats {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho : Matrix I I ℂ) : ℝ :=
  QAlgorithms.Papers.Independent.Advance50.P21.renyiNats a
    (Matrix.reindexAlgEquiv ℂ ℂ (Fintype.equivFin I) rho)

/-- PDF pp.7-8, (2.7),(2.12): mutual Renyi information from the actual two partial traces. -/
noncomputable def mutualRenyiNats {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (a : ℝ)
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  regulatedRenyiNats a (QAlgorithms.traceRight rho) +
    regulatedRenyiNats a (QAlgorithms.traceLeft rho) - regulatedRenyiNats a rho

/-- PDF p.8, (2.12): the centered, normalized spectral factor. Subtracting the
full identity is harmless off occupied support because the perturbation annihilates it. -/
noncomputable def centeredPower {I : Type*} [Fintype I] [DecidableEq I]
    (a : ℝ) (rho : Matrix I I ℂ) : Matrix I I ℂ :=
  (((occupiedPower a rho).trace.re)⁻¹ : ℂ) • occupiedPower (a - 1) rho - 1

example {I : Type*} [Fintype I] (rho0 rho1 : Matrix I I ℂ) :
    densityPerturbation rho0 rho1 0 = rho0 := by
  simp [densityPerturbation]

example {I : Type*} [Fintype I] (rho : Matrix I I ℂ)
    (hrho : QAlgorithms.IsDensityMatrix rho) :
    IsSupportPreservingPerturbation rho 0 := by
  refine ⟨hrho, by simp [Matrix.IsHermitian], by simp, ?_, ?_⟩
  · intro v hv
    simp
  · apply Filter.Eventually.of_forall
    intro t
    constructor
    · simpa [densityPerturbation] using hrho
    · intro v
      simp [densityPerturbation]

example {I : Type*} [Fintype I] [DecidableEq I] (a : ℝ) :
    occupiedPower a (1 : Matrix I I ℂ) = 1 := by
  simp [occupiedPower, cfc_one]

example {I : Type*} [Fintype I] [DecidableEq I] :
    entropy (1 : Matrix I I ℂ) = 0 := by
  simp [entropy, cfc_one]

/-- PDF p.5: a one-dimensional pure density has zero Renyi entropy at every order. -/
example (a : ℝ) : regulatedRenyiNats a (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0 := by
  simp [regulatedRenyiNats, QAlgorithms.Papers.Independent.Advance50.P21.renyiNats,
    QAlgorithms.Papers.Independent.Dependency50.P05.renyiEntropy, cfc_one]

/-- PDF p.36, (A.22): the sine sum at k = 2d. The endpoint n = 1 is an empty
sum. At n = 0 the definition also returns zero, but the theorem excludes that input. -/
noncomputable def cosecantPowerSum (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n - 1),
    ((2 : ℝ) * Real.sin (Real.pi * (j : ℝ) / (n : ℝ)))⁻¹ ^ (2 * k)

/-- PDF p.37, (A.24)-(A.25): polynomial coefficients of ((1+u)^n-1)/(n*u).
The coefficient of u^m is (n-1)...(n-m)/(m+1)!. The empty product is one.
The variable of each coefficient polynomial represents n, not u. -/
noncomputable def binomialDenominator : PowerSeries (Polynomial ℝ) :=
  PowerSeries.mk fun m =>
    Polynomial.C (((m + 1).factorial : ℝ)⁻¹) *
      ∏ j ∈ Finset.Icc 1 m, (Polynomial.X - Polynomial.C (j : ℝ))

/-- PDF p.37, (A.24)-(A.25): explicit polynomial obtained from minus the residue
at t=1. Removing the Laurent factor u^-1 changes coefficient 2k-1 to coefficient 2k.
The inverse uses constant coefficient one, so this is a construction over R[n], not an
existence choice or interpolation axiom. -/
noncomputable def sineSumPolynomial (k : ℕ) : Polynomial ℝ :=
  Polynomial.C ((-1 : ℝ) ^ (k + 1)) *
    PowerSeries.coeff (2 * k)
      (((1 + PowerSeries.X : PowerSeries (Polynomial ℝ)) ^ (k - 1)) *
        PowerSeries.invOfUnit binomialDenominator 1)

/-- PDF p.37, (A.24): scalar version of the residue coefficient for an integer n.
For n>=1 this denominator series has constant coefficient one. -/
noncomputable def residueCoefficient (k n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + 1) * PowerSeries.coeff (2 * k)
    (((1 + PowerSeries.X : PowerSeries ℝ) ^ (k - 1)) *
      (PowerSeries.mk fun m => (n.choose (m + 1) : ℝ) / (n : ℝ))⁻¹)

/-- PDF p.36, (A.22): the specified continuation of the scalar-pair coefficient.
For k=2d and t>0 this is t^(1-4d) P_k(t)/2. It is not claimed to be the unique
analytic interpolation among arbitrary analytic functions. -/
noncomputable def scalarPairContinuation (k : ℕ) (t : ℝ) : ℝ :=
  (sineSumPolynomial k).eval t / (2 * t ^ (2 * k - 1))

example (k : ℕ) : cosecantPowerSum k 1 = 0 := by
  simp [cosecantPowerSum]

example : PowerSeries.constantCoeff binomialDenominator = 1 := by
  simp [binomialDenominator, PowerSeries.constantCoeff_mk]

example (k : ℕ) : scalarPairContinuation k 1 =
    (sineSumPolynomial k).eval 1 / 2 := by
  simp [scalarPairContinuation]

end QAlgorithms.Papers.Independent.Intakethird100.P41


