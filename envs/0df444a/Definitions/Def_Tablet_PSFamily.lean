-- Prove2me | Definitions.Def_Tablet_PSFamily
-- name    : Tablet_PSFamily
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:49:43.623772+00:00
-- url     : https://prove2.me/theorems/d043c7d8-5732-50e3-a785-dc36a33ae3c1
-- title:
--   PSFamily
-- statement:
--   Definitions and structural lemmas for PSFamily, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PSFamily.lean

import Definitions.Def_Tablet_ThetaL
import Definitions.Def_Tablet_curveRestrictTot
import Definitions.Def_Tablet_CurveMeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
open MeasureTheory ENNReal
structure PSFamily {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) where
-- BODY
  /-- `η_l`, a Borel measure on `Θ(E)` for each `l ∈ ℕ`. -/
  eta : ℕ → Measure (Curve E)
  /-- Each `η_l` is a finite measure. -/
  finite : ∀ l : ℕ, IsFiniteMeasure (eta l)
  /-- `η_l` is supported on `Θ_l(E)` for `l ≥ 1`. -/
  supported : ∀ l : ℕ, 1 ≤ l → eta l ((ThetaL l : Set (Curve E))ᶜ) = 0
  /-- Eq.~(4.8): `𝕄([[γ]]) = length(γ) = l` for `η_l`-a.e.\ `γ`, `l ≥ 1`. -/
  lengthExactly : ∀ l : ℕ, 1 ≤ l → ∀ᵐ γ ∂(eta l), γ.len = (l : ℝ)
  /-- Eq.~(4.6): `T(ω) = (1/l) ∫ [[γ]](ω) dη_l(γ)` for every `1`-form `ω`, `l ≥ 1`. -/
  weakLength : ∀ l : ℕ, 1 ≤ l → ∀ ω : Form1 E,
    T ω = (l : ℝ)⁻¹ * ∫ γ, curveCurrent γ ω ∂(eta l)
  /-- The mass measure `μ_T` of `T` (paper.tex line 1100), carried as data alongside its
  characterization via `η_l`'s beginning/ending marginals. -/
  massMeasure : Measure E
  massMeasure_finite : IsFiniteMeasure massMeasure
  /-- Eq.~(4.7): for every nonnegative measurable `φ : E → ℝ≥0∞` and `l ≥ 1`, `∫ φ dμ_T` equals
  both the `η_l`-average of `φ` at the curve's start and at its end. -/
  massMarginal : ∀ l : ℕ, 1 ≤ l → ∀ φ : E → ℝ≥0∞, Measurable φ →
    (∫⁻ x, φ x ∂massMeasure = ∫⁻ γ, φ (γ.toFun 0) ∂(eta l))
      ∧ (∫⁻ x, φ x ∂massMeasure = ∫⁻ γ, φ (γ.toFun γ.len) ∂(eta l))
  /-- Lemma A.5 (paper.tex line 1860): the marginal of `η_l` under restriction to the `j`-th unit
  subcurve, `j ∈ {1,…,l}`, coincides with `η_1`, stated for nonnegative measurable `h`. -/
  marginal : ∀ l j : ℕ, 1 ≤ j → j ≤ l → ∀ h : Curve E → ℝ≥0∞, Measurable h →
    ∫⁻ γ, h (curveRestrictTot γ ((j : ℝ) - 1) (j : ℝ)) ∂(eta l) = ∫⁻ γ, h γ ∂(eta 1)


