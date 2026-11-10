-- Prove2me | Definitions.Def_GEPPGrowth_Main_Gaussian
-- name    : GEPPGrowth_Main_Gaussian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:34:33.650192+00:00
-- url     : https://prove2.me/theorems/0163056d-0ad4-4055-8fbe-d5afcdbc1e29
-- title:
--   Centered Gaussian vectors and independent Gaussian columns
-- statement:
--   For a real symmetric positive semidefinite $d\times d$ matrix $S$, let $\gamma_S=N(0,S)$ be the centered Gaussian law on $\mathbb R^d$. For $m$ columns, write $\gamma_S^{\otimes m}$ for independent draws from this same law, arranged as a $d\times m$ matrix.
--
--   $$\gamma_S=N(0,S),\qquad \mathcal C_{S,m}=\operatorname{Law}([y_1\ \cdots\ y_m]),\quad y_j\overset{\mathrm{iid}}\sim\gamma_S.$$
--
--   These laws model the residual columns, including singular positive semidefinite covariances when relevant. The scalar probability helper evaluates the outer measure of an arbitrary set and converts its finite value to a real number; it does not require the set to be Borel. Matrix entries carry the product Borel sigma-algebra. Vectors use coordinates indexed from zero. Mathlib extends a non-positive-semidefinite covariance by a point mass at zero; source results requiring a covariance carry the appropriate positive semidefiniteness or definiteness condition. The published Gaussian matrix law and Euclidean spectral norm are imported rather than redefined.
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), §3, printed pp.6–7, PDF pp.7–8; §4.1, printed pp.7–9, PDF pp.8–10

import Mathlib
import Definitions.Def_GaussianMatrix_basic
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Finite real vectors, with Euclidean squared length given explicitly by dot products. -/
abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The product Borel sigma-algebra on the entries of a finite real matrix. -/
instance matrixMeasurable (n m : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

/-- Centered Gaussian law with covariance S. Only PSD matrices are used mathematically;
Mathlib extends a non-PSD covariance by a Dirac measure at zero. -/
noncomputable def normal {d : ℕ} (S : Mat d) : Measure (Vec d) :=
  (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S).map
    (fun x i => x i)

/-- Independent Gaussian columns, stored as a row-by-column matrix. -/
noncomputable def columnsLaw {d : ℕ} (S : Mat d) (m : ℕ) :
    Measure (Matrix (Fin d) (Fin m) ℝ) :=
  (Measure.pi (fun _ : Fin m => normal S)).map (fun z i j => z j i)

/-- Outer probability, also meaningful for the arbitrary conic sets in Lemma 4.5. -/
noncomputable def prob {α : Type*} [MeasurableSpace α] (μ : Measure α) (E : Set α) : ℝ :=
  (μ E).toReal

instance normal_isProbabilityMeasure {d : ℕ} (S : Mat d) : IsProbabilityMeasure (normal S) := by
  unfold normal
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  fun_prop

instance columnsLaw_isProbabilityMeasure {d : ℕ} (S : Mat d) (m : ℕ) :
    IsProbabilityMeasure (columnsLaw S m) := by
  unfold columnsLaw
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  change Measurable (fun z : Fin m → Vec d => fun i j => z j i)
  fun_prop

end GEPPGrowth.Main


