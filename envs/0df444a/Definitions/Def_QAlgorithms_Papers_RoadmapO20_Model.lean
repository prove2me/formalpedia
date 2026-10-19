-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapO20_Model
-- name    : QAlgorithms_Papers_RoadmapO20_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:24:02.970224+00:00
-- url     : https://prove2.me/theorems/0334db6c-cb17-4346-82d4-4740c8d34461
-- title:
--   Randomized and quantum approximate matrix multiplication: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Randomized and quantum approximate matrix multiplication, arXiv:2510.08509v1, https://arxiv.org/abs/2510.08509v1. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_ClassicalMatrixSketchEstimator
import Definitions.Def_QAlgorithms_Defs_ApproximateMatrixMultiplicationContracts
noncomputable section

open MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapO20

open QAlgorithms MatrixApprox

/-- Row-major full input, in factor order; §2.3, PDF p.8. There are k+1 factors. -/
def o20Input {n k : ℕ} (A : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ) :
    Fin ((k+1)*(n*n)) → ℝ :=
  fun z => let ij := finProdFinEquiv.symm z
           let rc := finProdFinEquiv.symm ij.2
           A ij.1 rc.1 rc.2

/-- Product of the Frobenius norms, Definition 2.1, PDF p.7. -/
def o20F {n k : ℕ} (A : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ j, frobeniusNorm (A j)

/-- Squared norm statistic computed by preprocessing, with no square roots or divisions. -/
def o20SquaredF {n k : ℕ} (A : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∏ j, ∑ a, ∑ b, A j a b ^ 2

/-- Confidence amplification and integer rounding of the sample counts in pp.22-23.
Budget zero selects the direct zero answer. Clipping the classical width at n selects
exact multiplication, as in §4.1 when a sketch would be wider than the input. -/
def o20Budgets (n k : ℕ) (squaredF eps delta : ℝ) : ℕ × ℕ × ℕ :=
  if squaredF ≤ eps^2 then (0,0,0) else
    (min n (max 1 ⌈108 * (3 : ℝ)^(k+1)*squaredF/eps^2⌉₊),
      max 1 ⌈(3 : ℝ)^(((k+1 : ℕ) : ℝ)/2)*Real.sqrt squaredF/eps *
        max 1 (Real.log ((n : ℝ)^2/delta))⌉₊,
      2*⌈100*Real.log delta⁻¹⌉₊+1)

/-- A classical exact-real circuit with random coins and comparisons. Comparisons are
needed for the median-of-means selection in Theorem 4.11, PDF p.23. All data reads
have fixed addresses and are charged frozen arithmetic instructions. Comparisons write a
0/1 result and continue through the same word; every instruction is executed and charged. -/
inductive O20ClassicalWord (input registers n : ℕ) where
  | halt (out : Fin (n*n) → Fin registers)
  | arithmetic (op : ExactArithmetic.ClassicalInstruction input registers)
      (next : O20ClassicalWord input registers n)
  | compare (dst a b : Fin registers) (next : O20ClassicalWord input registers n)

/-- Computed classical output and actual arithmetic work on each random branch. -/
def o20ClassicalExecution {input registers n : ℕ} (data : Fin input → ℝ) :
    O20ClassicalWord input registers n → ExactArithmetic.ClassicalState registers →
      PMF (Matrix (Fin n) (Fin n) ℝ × Bool × ℕ)
  | .halt out, state => PMF.pure
      (Matrix.of fun i j => state.memory (out (finProdFinEquiv (i,j))),
        state.failed, state.work+n*n)
  | .arithmetic op next, state =>
      (ExactArithmetic.classicalStep data state op).bind (o20ClassicalExecution data next)
  | .compare dst a b next, state =>
      o20ClassicalExecution data next
        {state with
          memory := Function.update state.memory dst
            (if state.memory a ≤ state.memory b then 1 else 0)
          work := state.work+1}

/-- The exact-real classical circuit; it contains no indexed memory operation. -/
structure O20ClassicalCircuit (n input : ℕ) where
  registers : ℕ
  word : O20ClassicalWord input registers n

/-- Classical law computed from the circuit, with allocated registers and input reads charged. -/
def o20ClassicalLaw {n input : ℕ} (C : O20ClassicalCircuit n input) (data : Fin input → ℝ) :
    PMF (Matrix (Fin n) (Fin n) ℝ × Bool × ℕ) :=
  o20ClassicalExecution data C.word ⟨0,false,input+C.registers⟩

/-- Maximum possible sequential work of the actual quantum word. The frozen constructor
also charges input, real registers, qubits and circuit construction (node count). -/
def o20QuantumDepth {input r q : ℕ} : MeanEstimatorProgram input r q → ℕ
  | .halt => 0
  | .step _ next => 1+o20QuantumDepth next
  | .observe _ zero one => 1+max (o20QuantumDepth zero) (o20QuantumDepth one)

/-- Quantum cost is tied to the actual circuit, including uncomputation and classical output. -/
def o20QuantumWork {n input : ℕ} (C : MeanEstimatorCircuit n input) : ℕ :=
  C.constructionWork+o20QuantumDepth C.program+n*n

/-- Classical preprocessing cost in the exact-arithmetic circuit model, PDF p.8. -/
def o20PreprocessingWork {input r : ℕ}
    (C : ExactArithmetic.ClassicalCircuit input r 1) : ℕ :=
  input+r+C.instructions.length+1

/-- Polylogarithmic confidence and size overhead; §2.1, PDF p.7. Totalized at scale zero. -/
def o20Logs (n k : ℕ) (eps delta scale : ℝ) (power : ℕ) : ℝ :=
  max 1 (Real.log (2+(n : ℝ)+k+eps⁻¹+delta⁻¹+max 1 scale))^power


end QAlgorithms.Papers.RoadmapO20


