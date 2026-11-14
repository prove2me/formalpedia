-- Prove2me | Definitions.Def_PGDRevision20261113_MeasureExtension
-- name    : PGDRevision20261113_MeasureExtension
-- status  : Definition
-- author  : @Somehow
-- created : 2026-11-13T07:58:47.877193+00:00
-- url     : https://prove2.me/theorems/141520ac-0c2c-43ed-9435-d13fb9b546ca
-- title:
--   Finite positive entropy measures and their exact performance interfaces
-- statement:
--   For a finite positive measure supported in $[0,\bar a]$, with $\bar a<1$ and positive first moment, define
--   $$\psi(t)=\int H(\sqrt a\,t)\,d\nu(a),\qquad A(t)=\int\frac{a}{1-at^2}\,d\nu(a).$$
--   This module supplies the integrated loss, power geometries, actual implicit-profile performance, and the target proposition extending the finite-mixture theorem. Finiteness, support, positive moment, and positive penalty scale are explicit hypotheses.
-- source:
--   Author manuscript, Exact Residual Bounds and Optimal Geometry Selection for Proximal Gradient Methods, revised reading edition, 13 November 2026; Sections 4--8 and Appendix B, with exact source references on each associated theorem.

import Definitions.Def_PGDRevision20261113_Geometry
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section
open scoped ENNReal
open MeasureTheory

namespace PGDRevision20261113

def normalizedEntropy (t : ℝ) : ℝ :=
  ((1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t)) / 2

def measureEntropyLoss (nu : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ a : ℝ, normalizedEntropy (Real.sqrt a * t) ∂nu

def measureEntropyCurvature (nu : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ a : ℝ, a / (1 - a * t ^ 2) ∂nu

def measureEntropyGeometry (nu : Measure ℝ) (lam : ℝ) : GeometryData :=
  ⟨.interval 1, measureEntropyCurvature nu, powerCurvature 1, lam⟩

def measureEntropyProfile (nu : Measure ℝ) (lam c : ℝ) : ScalarProfile :=
  ⟨Set.Ioo (-1 : ℝ) 1, measureEntropyLoss nu,
    (fun t => lam * normalizedEntropy t), doublePrimitive (powerCurvature c)⟩

def AdmissibleEntropyMeasure (nu : Measure ℝ) (abar lam : ℝ) : Prop :=
  IsFiniteMeasure nu ∧ 0 < abar ∧ abar < 1 ∧ 0 < lam ∧
  nu (Set.Icc (0 : ℝ) abar)ᶜ = 0 ∧ 0 < ∫ a : ℝ, a ∂nu

def entropyMeasureA0 (nu : Measure ℝ) : ℝ := ∫ a : ℝ, a ∂nu
def entropyMeasureA1 (nu : Measure ℝ) : ℝ := ∫ a : ℝ, a / (1 - a) ∂nu
def entropyThreshold (a : ℝ) : ℝ := (Real.sqrt (1 + 8 * a) - 1) / 2

def MeasureEntropyLocation (nu : Measure ℝ) (abar lam : ℝ) (z : ℝ × ℝ) : Prop :=
  0 < z.1 ∧ z.1 < entropyThreshold abar ∧ entropyThreshold abar < 1 ∧
  entropyMeasureA0 nu / 2 < z.2 ∧ z.2 < entropyMeasureA1 nu ∧
  0 < geometryRho (measureEntropyGeometry nu lam) z.1 z.2 ∧
  geometryRho (measureEntropyGeometry nu lam) z.1 z.2 <
    ENNReal.ofReal (entropyMeasureA0 nu / (entropyMeasureA0 nu + 2 * lam)) ∧
  entropyMeasureA0 nu / (entropyMeasureA0 nu + 2 * lam) < 1

def NonnegativeAlternatingContacts (G : GeometryData) (z : ℝ × ℝ) (r : ℝ) : Prop :=
  ∃ (t : Fin 3 → ℝ) (sigma : ℝ),
    0 ≤ t 0 ∧ t 0 < t 1 ∧ t 1 < t 2 ∧ t 2 < 1 ∧
    (sigma = 1 ∨ sigma = -1) ∧
    ∀ i, geometryError G z.1 z.2 (t i) = alternatingSign sigma i * r

def fixedExponentRates (G : GeometryData) (c : ℝ) : Set ℝ≥0∞ :=
  {r | ∃ p > (0 : ℝ), r = geometryRho G c p}

def PositiveMeasureEntropyExtensionClaim : Prop :=
  ∀ (nu : Measure ℝ) (abar lam : ℝ), AdmissibleEntropyMeasure nu abar lam →
    let G := measureEntropyGeometry nu lam
    AdmissibleGeometry G ∧
    (∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      deriv (deriv (measureEntropyLoss nu)) t = measureEntropyCurvature nu t) ∧
    (∀ c p : ℝ, 0 ≤ c → 0 < p →
      AdmissibleProfile (measureEntropyProfile nu lam c) p ∧
      ∀ N : ℕ, 1 ≤ N → profileOmega (measureEntropyProfile nu lam c) p N =
        geometryRho G c p ^ (2 * N)) ∧
    (∃! z : ℝ × ℝ, GeometryOptimum G z) ∧
    (∀ z, GeometryOptimum G z →
      MeasureEntropyLocation nu abar lam z ∧
      NonnegativeAlternatingContacts G z (geometryRho G z.1 z.2).toReal ∧
      geometryRho G z.1 z.2 < sInf (fixedExponentRates G 0) ∧
      geometryRho G z.1 z.2 < sInf (fixedExponentRates G 1) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ w : ℝ × ℝ, FeasiblePair w →
        profileOmega (measureEntropyProfile nu lam z.1) z.2 N ≤
          profileOmega (measureEntropyProfile nu lam w.1) w.2 N ∧
        (profileOmega (measureEntropyProfile nu lam w.1) w.2 N =
          profileOmega (measureEntropyProfile nu lam z.1) z.2 N → w = z)) ∧
    (∀ (z : ℝ × ℝ) (r : ℝ), FeasiblePair z → 0 < r →
      UniformGeometryEnvelope G z r → NonnegativeAlternatingContacts G z r →
      GeometryOptimum G z ∧ geometryRho G z.1 z.2 = ENNReal.ofReal r ∧
      ∀ w, GeometryOptimum G w → w = z) ∧
    (∀ a : ℝ, 0 < a → a < 1 →
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        measureEntropyLoss nu t = normalizedEntropy (Real.sqrt a * t)) →
      ∀ z, GeometryOptimum G z → a < z.2 ∧ z.2 < a / (1 - a) ∧
        ∃ t2 t3 : ℝ, 0 < t2 ∧ t2 < t3 ∧ t3 < 1 ∧
          geometryError G z.1 z.2 0 = (geometryRho G z.1 z.2).toReal ∧
          geometryError G z.1 z.2 t2 = -(geometryRho G z.1 z.2).toReal ∧
          geometryError G z.1 z.2 t3 = (geometryRho G z.1 z.2).toReal)

end PGDRevision20261113


