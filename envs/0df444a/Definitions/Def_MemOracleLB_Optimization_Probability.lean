-- Prove2me | Definitions.Def_MemOracleLB_Optimization_Probability
-- name    : MemOracleLB_Optimization_Probability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:46.10609+00:00
-- url     : https://prove2.me/theorems/12f7b3c4-274b-46b7-95cd-1ac1aeeb6465
-- title:
--   Gaussian laws, determinant refreshes and normal localization
-- statement:
--   Let $E_n=\mathbb R^n$ with its Euclidean inner product. This interface defines $\bar\gamma_n=N(0,I_n/n)$ by scaling the standard Gaussian, and $K(\mu)=D_{\rm KL}(\mu\|\gamma_n)$ with values in $[0,\infty]$. A full-dimensional law is absolutely continuous with respect to Lebesgue measure. A log-concave law has an integrable log-concave density; its density need not be Borel. Covariance bounds include finite second moments.
--
--   For independent square-matrix rows of laws $\mu_i$, let $X^{(i)}$ refresh row $i$ independently. The individual and average flips are
--
--   $$\nu_i=\Pr(\operatorname{sign}\det X\ne\operatorname{sign}\det X^{(i)}),\qquad \nu=\frac1d\sum_i\nu_i.$$
--
--   The interface also defines the normalized cofactor normal $v(A)$ of an $(n-1)\times n$ row matrix, sign-insensitive projective distance, row-to-span residual distances, and projected flip probabilities. Appending the fixed normal as the last row computes projected determinant signs up to one common sign, which leaves flip events unchanged. The Householder coordinates in Lemma 3.4 are explicit measurable formulas, held fixed during a refresh.
--
--   Second and angular moments are continuous linear operators. Projected entropy compares both pushed-forward measures on the ambient Euclidean space. The predicate naming Lemma 3.1's complete per-dimension property binds its constants in Lemma 3.2; it supplies no global assumption to the goal.
--
--   **Formalization Note** Normalization at zero returns zero, cofactor normals vanish off full row rank, and chi-square rank zero is a point mass. The relevant rank-deficient inputs have probability zero under the stated row laws.
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), definitions in §§1.3,2,3, PDF pp.5,8–10,14,16 (printed pp.4,7–9,13,15), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_LogConcaveOn

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace MemOracleLB.Optimization

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- PDF pp.5,8: Gaussian with coordinate variance 1/n. -/
def scaledGaussian (n : ℕ) : Measure (E n) :=
  (stdGaussian (E n)).map (fun x => (Real.sqrt n)⁻¹ • x)

/-- PDF p.8: Gaussian relative entropy, allowing infinity. -/
def gaussianEntropy {n : ℕ} (μ : Measure (E n)) : ℝ≥0∞ :=
  klDiv μ (stdGaussian (E n))

/-- PDF p.9: full-dimensional means absolutely continuous with respect to Lebesgue measure. -/
def HasDensity {n : ℕ} (μ : Measure (E n)) : Prop := μ ≪ volume

/-- PDF p.9: a law has a Lebesgue integrable log-concave density; no Borel condition. -/
def LogConcaveLaw {n : ℕ} (μ : Measure (E n)) : Prop :=
  ∃ f : E n → ℝ, Integrable f volume ∧
    ConvexOptimization.LogConcaveOn Set.univ f ∧
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- Finite second moment, kept separate from covariance to exclude its junk value. -/
def SecondMomentFinite {n : ℕ} (μ : Measure (E n)) : Prop :=
  Integrable (fun x => ‖x‖ ^ 2) μ

/-- Covariance comparison from PDF pp.9–10. -/
def CovarianceBound {n : ℕ} (μ : Measure (E n)) (b : ℝ) : Prop :=
  SecondMomentFinite μ ∧ ∀ w : E n,
    variance (fun x => ⟪w, x⟫) μ ≤ b * ‖w‖ ^ 2

/-- Total variation distance on a general measurable space, PDF p.8. -/
def totalVariation {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ (s : Set α) (_ : MeasurableSet s), ENNReal.ofReal |μ.real s - ν.real s|

/-- Chi-square law; at rank zero this is the point mass, not gammaMeasure 0. -/
def chiSquare (r : ℕ) : Measure ℝ :=
  if r = 0 then Measure.dirac 0 else gammaMeasure ((r : ℝ) / 2) (1 / 2)

/-- PDF p.10: sign of the determinant of the square row matrix. -/
def determinantSign {d : ℕ} (X : Fin d → E d) : ℝ :=
  Real.sign (Matrix.det (fun i j => X i j))

/-- Refresh row i by an independent copy; all other rows are shared. -/
def flip {d : ℕ} (μ : Fin d → Measure (E d)) (i : Fin d) : ℝ :=
  ((Measure.pi μ).prod (μ i)).real
    {p | determinantSign p.1 ≠ determinantSign (Function.update p.1 i p.2)}

/-- PDF p.10: uniform average over the refreshed row. -/
def averageFlip {d : ℕ} (μ : Fin d → Measure (E d)) : ℝ :=
  (∑ i, flip μ i) / d

/-- Unit vector normalization, with value zero at zero. -/
def unit {n : ℕ} (x : E n) : E n := ‖x‖⁻¹ • x

/-- PDF p.5: sign-insensitive projective distance. -/
def projectiveDistance {n : ℕ} (v w : E n) : ℝ :=
  min ‖unit v - unit w‖ ‖unit v + unit w‖

/-- Cofactors explicitly choose a normal; full-rank matrices have a nonzero cofactor vector. -/
def cofactorNormal {m : ℕ} (A : Fin m → E (m + 1)) : E (m + 1) :=
  WithLp.toLp 2 (fun j => (-1 : ℝ) ^ j.val *
    Matrix.det (fun i k => A i (j.succAbove k)))

def normal {m : ℕ} (A : Fin m → E (m + 1)) : E (m + 1) := unit (cofactorNormal A)

/-- Fixed orientation of the determinant on u-perp: append u as the last row.
Its sign differs from any orthonormal-coordinate determinant by one fixed sign. -/
def projectedSign {m : ℕ} (u : E (m + 1)) (A : Fin m → E (m + 1)) : ℝ :=
  Real.sign (Matrix.det (fun (i : Fin (m + 1)) (j : Fin (m + 1)) => (if h : i.val < m then A ⟨i.val, h⟩ j else u j)))

def projectedFlip {m : ℕ} (μ : Fin m → Measure (E (m + 1))) (u : E (m + 1)) : ℝ :=
  (∑ i, ((Measure.pi μ).prod (μ i)).real
    {p | projectedSign u p.1 ≠ projectedSign u (Function.update p.1 i p.2)}) / m

/-- PDF p.14: the explicit Householder choice, including the harmless zero branch. -/
def householder {m : ℕ} (x y : E (m + 1)) : E (m + 1) :=
  let e : E (m + 1) := WithLp.toLp 2 (Pi.single (Fin.last m) 1)
  let w := unit (e - unit x)
  y - (2 * ⟪w, y⟫) • w

/-- First m coordinates after reflection: fixed orthonormal coordinates on x-perp for x nonzero. -/
def perpendicularCoordinates {m : ℕ} (x y : E (m + 1)) : E m :=
  WithLp.toLp 2 (fun j => householder x y j.castSucc)

/-- Conditional projected-row laws with row r deleted. -/
def exposedLaws {m : ℕ} (μ : Fin (m + 1) → Measure (E (m + 1)))
    (r : Fin (m + 1)) (x : E (m + 1)) : Fin m → Measure (E m) :=
  fun j => (μ (r.succAbove j)).map (perpendicularCoordinates x)

/-- PDF p.10: distance of a row to the span of all the other rows. -/
def rowResidual {m n : ℕ} (A : Fin m → E n) (i : Fin m) : ℝ :=
  Metric.infDist (A i) (Submodule.span ℝ {x | ∃ j, j ≠ i ∧ A j = x} : Set (E n))

/-- PDF p.10, Lemma 3.1's per-dimension property, used to bind its constants in Lemma 3.2. -/
def ShortResidualProperty (m : ℕ) (c C : ℝ) : Prop :=
  ∀ (t : ℝ), 0 < t → t < 1 →
  ∀ (μ : Fin m → Measure (E (m + 1))),
    (∀ i, IsProbabilityMeasure (μ i)) →
    (∀ i, LogConcaveLaw (μ i)) →
    (∀ i, CovarianceBound (μ i) (1 / (m + 1 : ℝ))) →
  ∀ (u : E (m + 1)), ‖u‖ = 1 →
    1 - 1 / 1024 ≤ (Measure.pi μ).real
      {A | projectiveDistance (normal A) u ≤ t / C} →
    1 / 8 ≤ projectedFlip μ u →
    c * t ≤ (∑ i, (Measure.pi μ).real
      {A | rowResidual A i ≤ t / Real.sqrt (m + 1)}) / m

/-- Second-moment matrix as a continuous linear operator, PDF p.14 (5). -/
def momentOperator {d : ℕ} (μ : Measure (E d)) : E d →L[ℝ] E d :=
  ∫ x, (InnerProductSpace.toDual ℝ (E d) x).smulRight x ∂μ

def angularMomentOperator {d : ℕ} (μ : Measure (E d)) : E d →L[ℝ] E d :=
  ∫ x, (‖x‖ ^ 2)⁻¹ • (InnerProductSpace.toDual ℝ (E d) x).smulRight x ∂μ

/-- Orthogonal projection, viewed in the ambient space (PDF p.16). -/
def perpendicularProjection {d : ℕ} (v x : E d) : E d := x - ⟪unit v, x⟫ • unit v

/-- Both projected measures live on the same ambient space. -/
def projectedEntropy {d : ℕ} (μ : Measure (E d)) (v : E d) : ℝ≥0∞ :=
  klDiv (μ.map (perpendicularProjection v))
    ((stdGaussian (E d)).map (perpendicularProjection v))

end MemOracleLB.Optimization


