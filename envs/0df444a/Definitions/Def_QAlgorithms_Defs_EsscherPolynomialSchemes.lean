-- Prove2me | Definitions.Def_QAlgorithms_Defs_EsscherPolynomialSchemes
-- name    : QAlgorithms_Defs_EsscherPolynomialSchemes
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:28:20.678106+00:00
-- url     : https://prove2.me/theorems/8c3d542e-e4b4-4ac9-87b8-03ec25d17cc0
-- title:
--   EsscherPolynomialSchemes
-- statement:
--   EsscherPolynomialSchemes
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\EsscherPolynomialSchemes.lean

import Definitions.Def_QAlgorithms_Defs_QuantumEsscherData
import Definitions.Def_QAlgorithms_Defs_MatrixQSVTCircuits
import Definitions.Def_QAlgorithms_Defs_CircuitResources
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.QuantumEsscher

/-- QAlgorithms.QuantumEsscher.IsBoundedApproximation: arxiv-2401.07561v2 PDF p.5, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.17, arxiv-2401.07561v2 PDF p.18. Source domains are explicit below. -/
def IsBoundedApproximation (f : ℝ → ℝ) (alpha lower upper scale eps : ℝ)
    (P : Polynomial ℝ) : Prop :=
  0 < alpha ∧ lower ≤ upper ∧ 0 < scale ∧ 0 < eps ∧
    (∀ x ∈ Set.Icc lower upper, |f (alpha*x)-P.eval x| ≤ eps) ∧
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x/scale| ≤ 1/2

/-- QAlgorithms.QuantumEsscher.EigenvalueStep: arxiv-2401.07561v2 PDF p.5, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.17, arxiv-2401.07561v2 PDF p.18, arxiv-2401.07561v2 PDF p.14. Source domains are explicit below. -/
inductive EigenvalueStep (a n : ℕ) where
  | phase (angle : ℝ) (flag : Bool)
  | signal (adjoint : Bool) (control : Option Bool)
  | flags (U : Matrix.unitaryGroup (Bool × Bool) ℂ)

/-- QAlgorithms.QuantumEsscher.EigenvalueStep.mat: arxiv-2401.07561v2 PDF p.5, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.17, arxiv-2401.07561v2 PDF p.18, arxiv-2401.07561v2 PDF p.14. Source domains are explicit below. -/
def EigenvalueStep.mat {a n : ℕ} (U : Matrix (Qubits (a+n)) (Qubits (a+n)) ℂ) :
    EigenvalueStep a n → Matrix ((Bool × Bool) × Qubits (a+n)) ((Bool × Bool) × Qubits (a+n)) ℂ
  | .phase theta flag => Matrix.diagonal fun z =>
      Complex.exp (Complex.I*(if (if flag then z.1.2 else z.1.1) = true then -theta
        else if (qubitsAppendEquiv a n z.2).1 = 0 then theta else -theta : ℝ))
  | .signal adj ctl => Matrix.of fun p q => if p.1 = q.1 then
      (if ctl.all (fun flag => if flag then q.1.2 else q.1.1)
        then (if adj then star U else U) p.2 q.2 else (1 : Matrix _ _ ℂ) p.2 q.2) else 0
  | .flags R => Matrix.kronecker (R : Matrix _ _ ℂ) 1

/-- QAlgorithms.QuantumEsscher.eigenvalueWord: arxiv-2401.07561v2 PDF p.5, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.17, arxiv-2401.07561v2 PDF p.18, arxiv-2401.07561v2 PDF p.14. Source domains are explicit below. -/
def eigenvalueWord {a n : ℕ} (word : List (EigenvalueStep a n))
    (U : Matrix (Qubits (a+n)) (Qubits (a+n)) ℂ) :
    Matrix ((Bool × Bool) × Qubits (a+n)) ((Bool × Bool) × Qubits (a+n)) ℂ :=
  (word.map (EigenvalueStep.mat U)).reverse.prod


/-- The same QET word restricted to a two-dimensional singular plane, arxiv-2401.07561v2 PDF p.17,
Theorem 15. This virtual plane does not add a physical signal-ancilla hypothesis. -/
def eigenvalueScalarStep {a n : ℕ} (x : ℝ) : EigenvalueStep a n →
    Matrix ((Bool × Bool) × Bool) ((Bool × Bool) × Bool) ℂ
  | .phase theta flag => Matrix.diagonal fun z => Complex.exp (Complex.I*
      (if (if flag then z.1.2 else z.1.1) then -theta else if z.2 then -theta else theta : ℝ))
  | .signal adj ctl => Matrix.of fun p q => if p.1 = q.1 then
      (if ctl.all (fun flag => if flag then q.1.2 else q.1.1)
        then (if adj then star (qspW x) else qspW x) (if p.2 then 1 else 0) (if q.2 then 1 else 0)
        else (1 : Matrix Bool Bool ℂ) p.2 q.2) else 0
  | .flags R => Matrix.kronecker (R : Matrix _ _ ℂ) 1

/-- The signal-only syntax of a QET word. The first component selects U or its adjoint;
the optional flag denotes the single controlled signal. Source: arxiv-2401.07561v2 PDF p.17,
Theorem 15, using alternating singular-plane transport before the terminal parity selection. -/
def signalPattern {a n : ℕ} (word : List (EigenvalueStep a n)) : List (Bool × Option Bool) :=
  word.filterMap fun step => match step with
    | .signal adj ctl => some (adj,ctl)
    | _ => none

/-- QAlgorithms.QuantumEsscher.EigenvalueScheme: arxiv-2401.07561v2 PDF p.14, arxiv-2401.07561v2 PDF p.17, arxiv-2401.07561v2 PDF p.18. Source domains are explicit below. -/
structure EigenvalueScheme (a n : ℕ) where
  polynomial : Polynomial ℝ
  degree : ℕ
  degree_bound : polynomial.natDegree ≤ degree
  bounded : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |polynomial.eval x| ≤ 1/2
  word : List (EigenvalueStep a n)
  alternating : signalPattern word =
    (List.ofFn fun j : Fin degree => (decide (j.val%2 = 1),none)) ++
      [(decide (degree%2 = 1),some false)]
  compilation : OracleCircuit oneTwoQubitGateSet (fun _ : Fin 1 => a+n) (2+(a+n))
  calls : compilation.queryCount 0 = degree+1
  plainCalls : compilation.plainQueryCount 0 = degree
  controlledCalls : compilation.controlledQueryCount 0 = 1
  realizesWord : ∀ U : Matrix (Qubits (a+n)) (Qubits (a+n)) ℂ,
    U ∈ Matrix.unitaryGroup _ ℂ →
    compilation.unitary (fun _ => U) =
      (eigenvalueWord word U).submatrix
        (fun z => ( (z 0,z 1),fun i => z (Fin.natAdd 2 i)))
        (fun z => ( (z 0,z 1),fun i => z (Fin.natAdd 2 i)))
  scalarCalibration : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    ((word.map (eigenvalueScalarStep x)).reverse.prod)
      ((false,false),false) ((false,false),false) = ((polynomial.eval x : ℝ) : ℂ)

example {a n : ℕ} (U : Matrix (Qubits (a+n)) (Qubits (a+n)) ℂ) :
    eigenvalueWord ([] : List (EigenvalueStep a n)) U = 1 := rfl

end QAlgorithms.QuantumEsscher


