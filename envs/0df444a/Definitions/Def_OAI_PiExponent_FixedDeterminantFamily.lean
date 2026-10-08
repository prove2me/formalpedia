-- Prove2me | Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
-- name    : OAI_PiExponent_FixedDeterminantFamily
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-07T19:29:19.623232+00:00
-- url     : https://prove2.me/theorems/cbf7eeb1-95ec-4611-938f-2f3704818cb1
-- title:
--   The fixed interpolation matrix and determinant family for pi
-- statement:
--   For one fixed admissible parameter family $d$ and a real height $H$, this module defines the source's finite row and column sets, truncated logarithmic interpolation matrix $M_d(H)$, and square minors $M_d(H)[s]$ selected by maps from rows to columns. The rational centers are $2i\,p_j/q_j$; the logarithms are truncated at $\lceil F_0\lceil\log q_j\rceil/v_0\rceil$.
--
--   The mean row weight $b_d(H)$ is the sum of the weighted row indices divided by the number of rows times $H$. With $c_0=\log2/4$, the collision rate is
--
--   $$c_d(H)=\frac{c_0\eta^2\,\#\operatorname{Rows}_d(H)}{H\,\#\operatorname{LowIndices}_d(H)},\qquad
--   c_{d,\infty}=\frac{c_0\eta^2K\theta^m}{(m+1)v_0A^m}.$$
--
--   Two propositions name the source's open inputs. The interpolation proposition requires $M_d(H)$ to be surjective at cofinally many real heights. The analytic proposition requires an error $\varepsilon(H)\to0$ and, eventually in $H$, the upper estimate for every nonzero selected minor:
--
--   $$\frac{\log\|\det M_d(H)[s]\|}{\#\operatorname{Rows}_d(H)\,H}
--   \le e_{\rm an}(d)+\varepsilon(H)+\max\{-c_d(H),-\nu(A(1-\eta)-b_d(H))\}.$$
--
--   **Formalization Note.** The definitions, including both propositions, are transcribed from the pinned source. Naming a proposition does not prove it. The matrix is defined explicitly rather than supplied as an arbitrary witness.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean#L15-L108 ; InterpolationMatrix.lean definitions; MatrixArithmetic.lean#L132-L219; Polynomials/SimplexCounting.lean#L154-L164

-- Definitions transcribed from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a.
import Definitions.Def_OAI_PiExponent_AdmissibleDeterminantParameters
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology
open scoped BigOperators
noncomputable section
namespace OAI.PiExponent
noncomputable def realWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1))).filter
    (fun a => ∑ i, w i * (a i : ℝ) ≤ H)

noncomputable def strictWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by
  classical
  exact (realWeightedSimplex w H).filter (fun a => ∑ i, w i * (a i : ℝ) < H)

namespace InterpolationMatrix
noncomputable def exponentVector {m : ℕ} (a : Fin m → ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

noncomputable def truncatedLog (T : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc T (PowerSeries.log ℂ)

noncomputable def monomialImage {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.C ((1 + Polynomial.X) ^ h) *
    ∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
      MvPolynomial.X i) ^ a i

noncomputable def entry {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℂ :=
  ((monomialImage r G j h a).coeff (exponentVector b)).coeff s

def columnWeights {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases w0 w

noncomputable def rowWeights {m : ℕ} (v0 θ : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases v0 (fun i => w i / θ)

abbrev Column {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  ↥(PiExponent.realWeightedSimplex (columnWeights w0 w) H)

abbrev Row {m : ℕ} (K : ℕ) (v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  Fin K × ↥(PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H)

noncomputable def matrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  fun ρ c => entry r G ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ)
    (c.1 0) (fun i => c.1 i.succ)

noncomputable def truncatedLogMatrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  matrix K w0 v0 θ w H r (fun i => truncatedLog (T i))

end InterpolationMatrix
namespace MatrixArithmetic
noncomputable def logWeights {m : ℕ} (q : Fin m → ℕ) (i : Fin m) : ℝ :=
  (⌈Real.log (q i)⌉₊ : ℝ)

noncomputable def rationalCenters {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin m → ℂ :=
  fun i => 2 * Complex.I * (p i : ℂ) / (q i : ℂ)

noncomputable def truncationOrders {m : ℕ} (q : Fin m → ℕ) (F v0 : ℝ) : Fin m → ℕ :=
  fun i => ⌈F * logWeights q i / v0⌉₊

noncomputable def rowWeightedSum {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ∑ i, (ρ.2.1 i.succ : ℝ) * logWeights q i

noncomputable def meanRowWeight {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  rowWeightedSum K v0 θ q H /
    ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H)

noncomputable def selectedMinor {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) :
    Matrix (InterpolationMatrix.Row K v0 θ (logWeights q) H)
      (InterpolationMatrix.Row K v0 θ (logWeights q) H) ℂ :=
  (InterpolationMatrix.truncatedLogMatrix K w0 v0 θ (logWeights q) H
    (rationalCenters p q) (truncationOrders q F v0)).submatrix id selection

end MatrixArithmetic
namespace DeterminantContradiction
noncomputable def collisionConstant : ℝ := Real.log 2 / 4

abbrev FixedData (nu : ℝ) := AdmissibleParameters nu Arithmetic.lcmConstant collisionConstant

noncomputable def finiteNumerators {nu : ℝ} (d : FixedData nu) : Fin d.m → ℤ :=
  fun i => d.p i.val

noncomputable def finiteDenominators {nu : ℝ} (d : FixedData nu) : Fin d.m → ℕ :=
  fun i => d.q i.val

abbrev Row {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  InterpolationMatrix.Row d.K d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H

abbrev Column {nu : ℝ} (d : FixedData nu) (H : ℝ) :=
  InterpolationMatrix.Column d.w0 (MatrixArithmetic.logWeights (finiteDenominators d)) H

noncomputable def actualMatrix {nu : ℝ} (d : FixedData nu) (H : ℝ) :
    Matrix (Row d H) (Column d H) ℂ :=
  InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
    (MatrixArithmetic.logWeights (finiteDenominators d)) H
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)

noncomputable def actualMinor {nu : ℝ} (d : FixedData nu) (H : ℝ)
    (selection : Row d H → Column d H) : Matrix (Row d H) (Row d H) ℂ :=
  MatrixArithmetic.selectedMinor d.K d.w0 d.v0 d.base.theta d.F0 H
    (finiteNumerators d) (finiteDenominators d) selection

noncomputable def actualMean {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  MatrixArithmetic.meanRowWeight d.K d.v0 d.base.theta (finiteDenominators d) H

noncomputable def actualRowCount {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℕ :=
  Fintype.card (Row d H)

noncomputable def lowIndexCount {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℕ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights (finiteDenominators d))
    ((d.base.A : ℝ) * H)).card

noncomputable def collisionRate {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  collisionConstant * d.base.eta ^ 2 * (actualRowCount d H : ℝ) /
    (H * (lowIndexCount d H : ℝ))

noncomputable def collisionLimit {nu : ℝ} (d : FixedData nu) : ℝ :=
  collisionConstant *
    (d.base.eta ^ 2 * (d.K : ℝ) * (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m))

def GlobalInterpolationStatement : Prop :=
  ∀ nu : ℝ, 2 < nu → ∀ d : FixedData nu,
    ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧ Function.Surjective (actualMatrix d H).mulVecLin

def AnalyticAggregateStatement : Prop :=
  ∀ nu : ℝ, 2 < nu → ∀ d : FixedData nu,
    ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : ℝ in atTop, ∀ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 →
        Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
          d.analyticError + error H +
            max (-collisionRate d H)
              (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))

end DeterminantContradiction
end OAI.PiExponent


