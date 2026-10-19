-- Prove2me | Definitions.Def_QAlgorithms_Defs_SchurTomography
-- name    : QAlgorithms_Defs_SchurTomography
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:43:53.253061+00:00
-- url     : https://prove2.me/theorems/f5e9ccec-d09c-43fd-a939-4cbf741d36e1
-- title:
--   SchurTomography
-- statement:
--   SchurTomography
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SchurTomography.lean

import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
noncomputable section

open MeasureTheory
open scoped Matrix

namespace QAlgorithms.Tomography

/-- Matrix reports use their finite-dimensional Borel sigma algebra
(1508.01797 p.6, classical estimate). -/
instance matrixReportMeasurable (d : ℕ) : MeasurableSpace (Matrix (Fin d) (Fin d) ℂ) :=
  borel _

/-- Borel convention for matrix reports (1508.01797 p.6). -/
instance matrixReportBorel (d : ℕ) : BorelSpace (Matrix (Fin d) (Fin d) ℂ) := ⟨rfl⟩

/-- Equation (10)'s collective measurement density, with respect to counting on
partitions times probability Haar on U(d). This is the raw source operator;
its lawful continuous-POVM wrapper must be established from this construction,
not assumed in its input (1508.01797 p.6, Eq.(10)). -/
def haahDensity {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (lambda : Schur.Partition d n) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ((Schur.schurDimension lambda /
    MvPolynomial.eval (Schur.normalizedRows hd hn lambda) (Schur.schurPolynomial lambda) : ℝ) : ℂ) •
    (Schur.isotypicProjector lambda * piKron n (Schur.estimate hd hn lambda U) *
      Schur.isotypicProjector lambda)

/-- Identity unitary leaves the diagram diagonal in the source density
(1508.01797 p.6, Eq.(10)). -/
example {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (lambda : Schur.Partition d n) :
    haahDensity hd hn lambda 1 =
      ((Schur.schurDimension lambda /
        MvPolynomial.eval (Schur.normalizedRows hd hn lambda) (Schur.schurPolynomial lambda) : ℝ) : ℂ) •
        (Schur.isotypicProjector lambda * piKron n (Schur.normalizedDiagram hd hn lambda) *
          Schur.isotypicProjector lambda) := by
  simp [haahDensity,Schur.estimate]


/-- Joint Born law of Eq.(10), on counting shapes times probability Haar.
The hidden input enters only through rho tensor-power n
(1508.01797 p.6, Eqs.(10)-(11)). -/
def haahJointLaw {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (_density : IsDensityMatrix rho) :
    Measure (Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ) :=
  (Measure.count.prod (Schur.unitaryHaar d)).withDensity (fun outcome =>
    ENNReal.ofReal (effectProb (haahDensity hd hn outcome.1 outcome.2) (piKron n rho)))

/-- Borel estimator decoder: continuous matrix conjugation on each discrete
shape (1508.01797 p.6, output after Eq.(14)). -/
theorem haahDecoder_measurable {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    Measurable (fun outcome : Schur.Partition d n × Matrix.unitaryGroup (Fin d) ℂ =>
      Schur.estimate hd hn outcome.1 outcome.2) := by
  apply measurable_from_prod_countable_right
  intro lambda
  change Measurable (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
    (U : Matrix _ _ ℂ) * Schur.normalizedDiagram hd hn lambda * star (U : Matrix _ _ ℂ))
  have hc : Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
    (U : Matrix _ _ ℂ) * Schur.normalizedDiagram hd hn lambda * star (U : Matrix _ _ ℂ)) := by
    fun_prop
  exact hc.measurable

/-- Observed Haah report law: measurable pushforward of the Born-weighted
joint law by U diag(lambda/n) U dagger. Haar alone is not the observed law
(1508.01797 p.6, Eqs.(10),(14)). -/
def haahOutcomeLaw {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (density : IsDensityMatrix rho) :
    Measure (Matrix (Fin d) (Fin d) ℂ) :=
  (haahJointLaw hd hn rho density).map
    (fun outcome => Schur.estimate hd hn outcome.1 outcome.2)

/-- An empty report event has zero probability (1508.01797 p.6). -/
example {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (rho : Matrix (Fin d) (Fin d) ℂ) (density : IsDensityMatrix rho) :
    haahOutcomeLaw hd hn rho density ∅ = 0 := by simp

end QAlgorithms.Tomography


