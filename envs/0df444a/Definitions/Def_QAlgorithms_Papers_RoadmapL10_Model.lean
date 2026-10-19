-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapL10_Model
-- name    : QAlgorithms_Papers_RoadmapL10_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:41.377758+00:00
-- url     : https://prove2.me/theorems/c2ac6628-fec3-4b9a-97b6-9960d820670b
-- title:
--   Provably efficient machine learning for quantum many-body problems: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Provably efficient machine learning for quantum many-body problems, arXiv:2106.12627v4, https://arxiv.org/abs/2106.12627v4. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_DirichletShadowLearning
import Definitions.Def_QAlgorithms_Defs_ShadowLearnerPrograms
noncomputable section

open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapL10

open GroundStateLearning

/-- The six single-qubit labels of Appendix A, PDF pp.12–13; true means spin up. -/
def shadowLabelCode (s : Axis × Bool) : Fin 6 :=
  match s with
  | (.X, false) => 0
  | (.X, true) => 1
  | (.Y, false) => 2
  | (.Y, true) => 3
  | (.Z, false) => 4
  | (.Z, true) => 5

/-- Parameter input to the compact-data loader (F32, F42, PDF pp.33,35). -/
def parameterInput {n m N : ℕ}
    (data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n) : ℕ → ℝ :=
  fun address => ((List.ofFn fun l => List.ofFn (data l).1).flatten).getD address 0

/-- Label input to the loader: one of six outcomes per site, not a dense matrix (F32). -/
def labelInput {n m N : ℕ}
    (data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n) : ℕ → Fin 6 :=
  fun address => ((List.ofFn fun l => List.ofFn fun j =>
    shadowLabelCode ((data l).2 j)).flatten).getD address 0

/-- Compact representation: m*N parameter words followed by n*N labels (F42). -/
def loadedTraining {n m N : ℕ} (load : LearnerProgram)
    (data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n) : LearnerState :=
  learnerExecution (parameterInput data) (labelInput data) (fun _ => 0)
    load ⟨0, ∅, 0, false⟩

/-- Real and imaginary entries of supplied few-body operators in wire order (F45). -/
def fewBodyEntryInput {L : ℕ} (arity : Fin L → ℕ)
    (localOp : (i : Fin L) → Matrix (Qubits (arity i)) (Qubits (arity i)) ℂ) : ℕ → ℝ :=
  fun address => ((List.ofFn fun i => (List.ofFn fun a : Fin (2 ^ arity i) =>
    (List.ofFn fun b : Fin (2 ^ arity i) =>
      let entry := localOp i ((bitsEquivFin (arity i)).symm a)
        ((bitsEquivFin (arity i)).symm b)
      [entry.re, entry.im]).flatten).flatten).flatten).getD address 0

/-- Execute an actual arithmetic/RAM evaluator on loaded data (F43–F46).
Only the new parameter and the local observable entries are external inputs. -/
def evaluatedPrediction {n m N L : ℕ} (load : LearnerProgram) (evaluate : LearnerProgram)
    (data : Fin N → EuclideanSpace ℝ (Fin m) × ShadowLabel n)
    (x : EuclideanSpace ℝ (Fin m)) (arity : Fin L → ℕ)
    (localOp : (i : Fin L) → Matrix (Qubits (arity i)) (Qubits (arity i)) ℂ) : LearnerState :=
  learnerExecution (fun address => (List.ofFn x).getD address 0) (fun _ => 0)
    (fewBodyEntryInput arity localOp) evaluate
    { loadedTraining load data with work := 0, failed := false }

/-- F1 and F.5(c), PDF pp.29,36: normalized projector onto the whole ground eigenspace.
Zero outside the cube is only a measurable extension, never a prediction target there. -/
def targetGroundFamily {n m terms spatial : ℕ}
    (H : HamiltonianFamily n m terms spatial) (x : EuclideanSpace ℝ (Fin m)) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  if x ∈ parameterCube m then
    if h : (H.hamiltonian x).IsHermitian then groundDensity (H.hamiltonian x) h else 0
  else 0


end QAlgorithms.Papers.RoadmapL10


