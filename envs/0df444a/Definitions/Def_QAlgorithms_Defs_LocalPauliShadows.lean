-- Prove2me | Definitions.Def_QAlgorithms_Defs_LocalPauliShadows
-- name    : QAlgorithms_Defs_LocalPauliShadows
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:02:56.958694+00:00
-- url     : https://prove2.me/theorems/78135f81-6c25-41b6-828b-de243dba252b
-- title:
--   LocalPauliShadows
-- statement:
--   LocalPauliShadows
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\LocalPauliShadows.lean

import Definitions.Def_QAlgorithms_Defs_LocalGroundStateFamilies
import Definitions.Def_QAlgorithms_Defs_Measurement
noncomputable section

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace QAlgorithms.GroundStateLearning

/-- The three Pauli axes for each local measurement (2106.12627 p.12, Eq.(A5)). -/
inductive Axis where
  | X | Y | Z
  deriving DecidableEq

/-- Explicitly the three axes in Eq.(A5), 2106.12627 p.12. -/
instance Axis.fintype : Fintype Axis :=
  ⟨{.X,.Y,.Z},by intro a; cases a <;> simp⟩

/-- Finite measurement labels carry the discrete sigma algebra (2106.12627 p.12). -/
instance Axis.measurableSpace : MeasurableSpace Axis := ⊤

/-- Borel measurable matrix entries of the state family (2106.12627 pp.29-30). -/
instance shadowMatrixMeasurableSpace (n : ℕ) :
    MeasurableSpace (Matrix (Qubits n) (Qubits n) ℂ) := borel _

/-- The state matrix sigma algebra is its Borel one (2106.12627 pp.29-30). -/
instance shadowMatrixBorelSpace (n : ℕ) :
    BorelSpace (Matrix (Qubits n) (Qubits n) ℂ) := ⟨rfl⟩

/-- Axis operator in the shared Pauli convention (2106.12627 p.12, Eq.(A5)). -/
def Axis.mat : Axis → Matrix Bool Bool ℂ
  | .X => pauliX | .Y => pauliY | .Z => pauliZ

/-- Six possible local labels; true denotes the +1 eigenvalue
(2106.12627 pp.3,12, Eqs.(A1)-(A5)). -/
abbrev ShadowLabel (n : ℕ) := Fin n → Axis × Bool

/-- Joint Pauli POVM effects, including the 3^{-n} basis-choice probability
(2106.12627 p.12, Eq.(A5)). -/
def pauliPOVM {n : ℕ} (label : ShadowLabel n) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((3 : ℂ)^n)⁻¹ • kronAll fun j =>
    (2⁻¹ : ℂ) • (1+(if (label j).2 then (1 : ℂ) else -1) • (label j).1.mat)

/-- Single-shot reconstruction, potentially indefinite (2106.12627 p.12, Eq.(A5)). -/
def snapshot {n : ℕ} (label : ShadowLabel n) : Matrix (Qubits n) (Qubits n) ℂ :=
  kronAll fun j => (2⁻¹ : ℂ) •
    (1+(if (label j).2 then (3 : ℂ) else -3) • (label j).1.mat)

/-- Product uniform measure on the length-two parameter cube
(2106.12627 p.29, Eq.(F2)). Its empty-dimensional case is a point mass. -/
def parameterCubeLaw (m : ℕ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  (Measure.pi fun _ : Fin m => (2⁻¹ : ℝ≥0∞) • volume.restrict (Set.Icc (-1 : ℝ) 1)).map
    (WithLp.toLp 2)

/-- Actual one-shot joint distribution: cube parameter, then the local-Pauli Born label.
Measurability is a legality requirement; no normalization of arbitrary weights is performed
(2106.12627 pp.27,33, Eqs.(E3),(F27),(F32)). -/
def trainingShotLaw {n m : ℕ}
    (rho : EuclideanSpace ℝ (Fin m) → Matrix (Qubits n) (Qubits n) ℂ)
    (_measurable : Measurable rho)
    (_states : ∀ x ∈ parameterCube m, IsDensityMatrix (rho x)) :
    Measure (EuclideanSpace ℝ (Fin m) × ShadowLabel n) :=
  ∑ label : ShadowLabel n,
    ((parameterCubeLaw m).withDensity
      (fun x => ENNReal.ofReal (effectProb (pauliPOVM label) (rho x)))).map (fun x => (x,label))

/-- N independent copies of the actual joint law; each point supplies one fresh shadow
(2106.12627 pp.27,33, Eqs.(E3),(F27),(F32)). -/
def trainingLaw {n m : ℕ}
    (rho : EuclideanSpace ℝ (Fin m) → Matrix (Qubits n) (Qubits n) ℂ)
    (measurable : Measurable rho)
    (states : ∀ x ∈ parameterCube m, IsDensityMatrix (rho x)) (N : ℕ) :
    Measure (Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n) :=
  Measure.pi fun _ => trainingShotLaw rho measurable states

example (label : ShadowLabel 0) : snapshot label = 1 := by
  ext x y
  simp [snapshot, kronAll, Matrix.one_apply, Subsingleton.elim x y]

example (label : ShadowLabel 0) : pauliPOVM label = 1 := by
  ext x y
  simp [pauliPOVM, kronAll, Matrix.one_apply, Subsingleton.elim x y]

example (x : Qubits 1) :
    snapshot (fun _ : Fin 1 => (Axis.Z,true)) x x = if x 0 then -1 else 2 := by
  cases h : x 0 <;> simp [snapshot, kronAll, Axis.mat, pauliZ, h] <;> norm_num

end QAlgorithms.GroundStateLearning


