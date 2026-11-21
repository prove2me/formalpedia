-- Prove2me | Definitions.Def_MasulloRH_RationalClassThetaSpace
-- name    : MasulloRH_RationalClassThetaSpace
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T02:46:23.218206+00:00
-- url     : https://prove2.me/theorems/2bdb898d-12d8-41f3-8d46-3f847b10948f
-- title:
--   The intrinsic spherical theta annihilator and convolution on rational idèle classes
-- statement:
--   Inside quotient L² take the closed sector of functions invariant along the finite units. Its intersection with the orthogonal complement of the weighted global admissible theta rows defines the actual spherical theta annihilator. The convolution is characterized by its matrix coefficients against all quotient L² tests, using multiplication by the positive real section in the quotient.
-- source:
--   A. M. Masullo, The Music of the Primes, rational spherical specialization of §§9–10, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Uses the actual rational idèle class quotient and orbital spherical theta functions in definition 89c61f98.

import Definitions.Def_MasulloRH_RationalIdeleClass
import Definitions.Def_NumberField_AdelicFourier

open MeasureTheory NumberField IsDedekindDomain
open MasulloRH.RationalFinite MasulloRH.RationalClass
open scoped InnerProductSpace Topology

namespace MasulloRH
noncomputable section

variable [MeasurableSpace RationalClass.Ad] [MeasurableSpace RationalFinite.K] [MeasurableSpace RationalClass.C]

/-- The spherical sector in the actual quotient Hilbert space, expressed by invariance along the finite unit orbits. -/
def rationalClassSpherical (κ : Measure K) (ν : Measure C) : Submodule ℂ (Lp ℂ 2 ν) :=
  (Submodule.span ℂ {v : Lp ℂ 2 ν | ∀ᵐ z ∂ν, ∀ᵐ u ∂κ, v (z*finiteUnit u) = v z}).topologicalClosure

/-- Weighted conjugates of spherical theta profiles from admissible global Schwartz–Bruhat tests. -/
def rationalClassThetaRows (μ : Measure Ad) (κ : Measure K) (ν : Measure C) (p : ℝ) : Set (Lp ℂ 2 ν) :=
  {v | ∃ F ∈ AdelicFourier.schwartzBruhat ℚ, F 0 = 0 ∧ (∫ a, F a ∂μ) = 0 ∧
    (v : C → ℂ) =ᵐ[ν] fun z => (starRingEnd ℂ)
      ((((1+(logNorm z)^2)^(p/2) : ℝ):ℂ) * ((Real.exp (logNorm z/2):ℂ)*sphericalTheta κ F z))}

/-- The annihilator is taken inside the spherical sector of the full quotient L². -/
def rationalClassThetaAnnihilator (μ : Measure Ad) (κ : Measure K) (ν : Measure C) (p : ℝ) :
    Submodule ℂ (Lp ℂ 2 ν) :=
  rationalClassSpherical κ ν ⊓ (Submodule.span ℂ (rationalClassThetaRows μ κ ν p))ᗮ

instance rationalClassThetaAnnihilator_completeSpace (μ : Measure Ad) (κ : Measure K) (ν : Measure C) (p : ℝ) :
    CompleteSpace (rationalClassThetaAnnihilator μ κ ν p) := by
  have hc : IsClosed (rationalClassThetaAnnihilator μ κ ν p : Set (Lp ℂ 2 ν)) :=
    (Submodule.isClosed_topologicalClosure _).inter (Submodule.isClosed_orthogonal _)
  exact hc.completeSpace_coe

/-- Weak spherical convolution on idèle classes using the positive-real section of the class group. -/
def IsRationalClassThetaConvolution (μ : Measure Ad) (κ : Measure K) (ν : Measure C) (p : ℝ)
    (ray : ℝ → C) (φ : ℝ → ℂ) (T : rationalClassThetaAnnihilator μ κ ν p →L[ℂ]
      rationalClassThetaAnnihilator μ κ ν p) : Prop :=
  ∀ (u : rationalClassThetaAnnihilator μ κ ν p) (g : Lp ℂ 2 ν),
    ⟪g, (T u : Lp ℂ 2 ν)⟫_ℂ =
      ∫ y : ℝ, φ (Real.exp y) * ∫ z : C, (starRingEnd ℂ) (g z) *
        ((((1+(logNorm z)^2)^(-p/2) / (1+(logNorm (z*ray y))^2)^(-p/2) : ℝ):ℂ) *
        (u : Lp ℂ 2 ν) (z*ray y)) ∂ν

end
end MasulloRH


