-- Prove2me | Definitions.Def_QAlgorithms_Defs_TomographyOutcomes
-- name    : QAlgorithms_Defs_TomographyOutcomes
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:38:06.943436+00:00
-- url     : https://prove2.me/theorems/532517e2-fc45-4e7b-99fd-cef3f26b2061
-- title:
--   TomographyOutcomes
-- statement:
--   TomographyOutcomes
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\TomographyOutcomes.lean

import Definitions.Def_QAlgorithms_Defs_GeneralPOVMs
import Definitions.Def_QAlgorithms_Defs_GradientMethods
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open MeasureTheory
open scoped Matrix ComplexOrder

namespace QAlgorithms.Tomography

/-- Classical trace-one PSD reports on the same d-dimensional system
(1508.01797 p.6; 1508.01907 p.2; 2305.18519 pp.2,4). -/
abbrev DensityOutcome (d : ℕ) := {rho : Matrix (Fin d) (Fin d) ℂ // IsDensityMatrix rho}

/-- Borel reports for collective tomography (2305.18519 pp.3-4). -/
instance densityOutcomeMeasurable (d : ℕ) : MeasurableSpace (DensityOutcome d) := borel _

/-- The Borel convention for density-matrix reports (2305.18519 pp.3-4). -/
instance densityOutcomeBorel (d : ℕ) : BorelSpace (DensityOutcome d) := ⟨rfl⟩

/-- A measurement of exactly n copies, fixed before the unknown state
(1508.01797 p.6; 1508.01907 p.7; 2305.18519 pp.3-4,9).
Zero copies have a scalar input register. -/
structure CollectiveMeasurement (d n : ℕ) where
  dimension_positive : 0 < d
  measurement : Measurements.OperatorPOVM (Fin n → Fin d) (DensityOutcome d)

/-- Tensor-power density legality for the actual n-copy input
(2305.18519 pp.2-3). -/
theorem tensorDensity {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ)
    (hrho : IsDensityMatrix rho) (n : ℕ) : IsDensityMatrix (piKron n rho) := by
  constructor
  · induction n with
    | zero =>
        have he : piKron 0 rho = 1 := by
          ext x y; simp [piKron, Matrix.one_apply, Subsingleton.elim x y]
        rw [he]
        exact Matrix.PosSemidef.one
    | succ n ih =>
        have he : piKron (n+1) rho =
            (Matrix.kronecker rho (piKron n rho)).submatrix
              (fun x => (x 0,Fin.tail x)) (fun x => (x 0,Fin.tail x)) := by
          ext x y
          simp [piKron, Fin.prod_univ_succ, Matrix.kronecker_apply, Fin.tail]
        rw [he]
        exact (hrho.1.kronecker ih).submatrix _
  · simp only [Matrix.trace, Matrix.diag, piKron, Matrix.of_apply]
    rw [← Fintype.prod_sum (fun (_ : Fin n) (i : Fin d) => rho i i)]
    have ht : ∑ i : Fin d, rho i i = 1 := hrho.2
    simp [ht]

/-- Actual Born outcome measure on rho tensor-power n; no loss or accuracy is built in
(2305.18519 pp.2-4,9). -/
def collectiveOutcomeLaw {d n : ℕ} (M : CollectiveMeasurement d n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) : Measure (DensityOutcome d) :=
  Measurements.bornLaw M.measurement (piKron n rho) (tensorDensity rho hrho n)

example (d : ℕ) (rho sigma : Matrix (Fin d) (Fin d) ℂ) :
    piKron 0 rho = piKron 0 sigma := by
  ext x y
  simp [piKron]

example {d : ℕ} (M : CollectiveMeasurement d 0)
    (rho sigma : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (hsigma : IsDensityMatrix sigma) :
    collectiveOutcomeLaw M rho hrho = collectiveOutcomeLaw M sigma hsigma := by
  unfold collectiveOutcomeLaw
  congr 1

end QAlgorithms.Tomography


