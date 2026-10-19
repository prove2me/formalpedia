-- Prove2me | Definitions.Def_QAlgorithms_Defs_EsscherOracleCircuits
-- name    : QAlgorithms_Defs_EsscherOracleCircuits
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:29:22.538193+00:00
-- url     : https://prove2.me/theorems/97e888c2-691f-4cf2-b927-f1a7d3dadf01
-- title:
--   EsscherOracleCircuits
-- statement:
--   EsscherOracleCircuits
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\EsscherOracleCircuits.lean

import Definitions.Def_QAlgorithms_Defs_PurifiedDensityAccess
import Definitions.Def_QAlgorithms_Defs_EsscherPolynomialSchemes
import Definitions.Def_QAlgorithms_Defs_PositiveLCU
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.QuantumEsscher

/-- QAlgorithms.QuantumEsscher.paddedLinearCombination: arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.7, arxiv-2401.07561v2 PDF p.15, arxiv-2401.07561v2 PDF p.16. Source domains are explicit below. -/
def paddedLinearCombination {b a n : ℕ} (d : ℕ) (fits : d+1 ≤ 2^b)
    (PL PR : Matrix.unitaryGroup (Qubits b) ℂ)
    (U : Fin (d+1) → Matrix (Qubits (a+n)) (Qubits (a+n)) ℂ) :
    Matrix (Qubits b × Qubits (a+n)) (Qubits b × Qubits (a+n)) ℂ :=
  let select : Matrix (Qubits b × Qubits (a+n)) (Qubits b × Qubits (a+n)) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then
      if h : bitsToNat q.1 < d+1 then U ⟨bitsToNat q.1,h⟩ p.2 q.2
      else (1 : Matrix _ _ ℂ) p.2 q.2 else 0
  Matrix.kronecker (star (PL : Matrix _ _ ℂ)) 1*select*Matrix.kronecker (PR : Matrix _ _ ℂ) 1


/-- Known identity padding on unused auxiliary wires, arxiv-2401.07561v2 PDF pp.15-16.
The last n wires remain the system and all other wires are auxiliary. -/
def padAuxiliary (a target n : ℕ) (fits : a ≤ target)
    (U : Matrix (Qubits (a+n)) (Qubits (a+n)) ℂ) :
    Matrix (Qubits (target+n)) (Qubits (target+n)) ℂ :=
  let restrict := fun z : Qubits (target+n) =>
    Fin.append (fun i : Fin a => z ⟨i.val,by have := i.isLt; omega⟩)
      (fun j : Fin n => z (Fin.natAdd target j))
  Matrix.of fun y z => if ∀ j : Fin target, a ≤ j.val → y (Fin.castAdd n j) = z (Fin.castAdd n j)
    then U (restrict y) (restrict z) else 0

/-- Known wire-count cast; arxiv-2401.07561v2 PDF pp.6-7. -/
def castOperator {a b : ℕ} (h : a = b) (U : Matrix (Qubits a) (Qubits a) ℂ) :
    Matrix (Qubits b) (Qubits b) ℂ := h ▸ U

/-- External oracle widths: density followed by d observable encodings; arxiv-2401.07561v2 PDF p.6. -/
def externalWidths (P : PublicParameters) (k : Fin (P.d+1)) : ℕ :=
  if k.val = 0 then P.n+P.purificationAncillas+P.n else P.observableAncillas+P.n

/-- Literal log-QET, two-preparation SELECT, exp-QET composition. It does not mention the Esscher
error bound or its target block. Source: Algorithm 1, arxiv-2401.07561v2 PDF pp.6-7. -/
def composedOperator (P : PublicParameters)
    (logarithm : EigenvalueScheme (P.n+P.purificationAncillas) P.n)
    (exponential : EigenvalueScheme (max P.observableAncillas (P.n+P.purificationAncillas)+2+P.selectorBits) P.n)
    (PL PR : Matrix.unitaryGroup (Qubits P.selectorBits) ℂ)
    (O : (k : Fin (P.d+1)) → Matrix (Qubits (externalWidths P k)) (Qubits (externalWidths P k)) ℂ) :
    Matrix (Qubits (P.outputAncillas+P.n)) (Qubits (P.outputAncillas+P.n)) ℂ := by
  let common := max P.observableAncillas (P.n+P.purificationAncillas)+2
  let logSignal : Matrix (Qubits (P.n+P.purificationAncillas+P.n))
      (Qubits (P.n+P.purificationAncillas+P.n)) ℂ := by
    simpa [externalWidths] using O 0
  let Ulog := logarithm.compilation.unitary (fun _ => logSignal)
  let logPadded := padAuxiliary (2+P.n+P.purificationAncillas) common P.n
    (by dsimp [common]; have := Nat.le_max_right P.observableAncillas (P.n+P.purificationAncillas); omega)
    (castOperator (by omega) Ulog)
  let obs := fun j : Fin P.d => padAuxiliary P.observableAncillas common P.n
    (by dsimp [common]; have := Nat.le_max_left P.observableAncillas (P.n+P.purificationAncillas); omega)
    (show Matrix (Qubits (P.observableAncillas+P.n)) (Qubits (P.observableAncillas+P.n)) ℂ from
      by simpa [externalWidths] using O j.succ)
  let combined := paddedLinearCombination P.d (Nat.le_pow_clog (by decide) (P.d+1)) PL PR
    (Fin.lastCases logPadded obs)
  let combinedFlat := combined.submatrix (qubitsAppendEquiv P.selectorBits (common+P.n))
    (qubitsAppendEquiv P.selectorBits (common+P.n))
  let U : Matrix (Qubits (max P.observableAncillas (P.n+P.purificationAncillas)+2+P.selectorBits+P.n))
      (Qubits (max P.observableAncillas (P.n+P.purificationAncillas)+2+P.selectorBits+P.n)) ℂ :=
    castOperator (by dsimp [common]; omega) combinedFlat
  exact castOperator (by unfold PublicParameters.outputAncillas; omega)
    (exponential.compilation.unitary (fun _ => U))

/-- Public Algorithm-1 synthesis choices and an actual flattened circuit with primitive compilation
checked against the literal composition. No final block error, target correctness or query bound is
an assumed field. Source: arxiv-2401.07561v2 PDF pp.6-7,15-18. -/
structure Construction (P : PublicParameters) where
  logarithm : EigenvalueScheme (P.n+P.purificationAncillas) P.n
  exponential : EigenvalueScheme (max P.observableAncillas (P.n+P.purificationAncillas)+2+P.selectorBits) P.n
  PL : Matrix.unitaryGroup (Qubits P.selectorBits) ℂ
  PR : Matrix.unitaryGroup (Qubits P.selectorBits) ℂ
  pair : IsStatePrepPair P.beta P.preparationError
    (Fin.snoc (fun j : Fin P.d => (P.theta j : ℂ)) (2*(1+Real.logb 2 (2*P.kappa)) : ℝ)) (PL : Matrix (Qubits P.selectorBits) (Qubits P.selectorBits) ℂ) (PR : Matrix (Qubits P.selectorBits) (Qubits P.selectorBits) ℂ)
  circuit : OracleCircuit oneTwoQubitGateSet (externalWidths P) (P.outputAncillas+P.n)
  primitiveCompilation : ∀ O : (k : Fin (P.d+1)) →
    Matrix (Qubits (externalWidths P k)) (Qubits (externalWidths P k)) ℂ,
    (∀ k, O k ∈ Matrix.unitaryGroup _ ℂ) →
      circuit.unitary O = composedOperator P logarithm exponential PL PR O
  logApproximation : IsBoundedApproximation (Real.logb 2) 1 P.kappa⁻¹ 1
    (2*(1+Real.logb 2 (2*P.kappa))) P.encodingError
    (Polynomial.C (2*(1+Real.logb 2 (2*P.kappa))) * logarithm.polynomial)
  expApproximation : IsBoundedApproximation (fun x => Real.exp x/Real.exp P.beta)
    P.beta (-1) 1 4 P.eps (Polynomial.C 4*exponential.polynomial)

-- The composed oracle circuit is recorded separately from the target/error contract.
-- Source primitive compilation relations will be audited below; no target block equality is a field.
/-- QAlgorithms.QuantumEsscher.UniformQueryBounds: arxiv-2401.07561v2 PDF p.2, arxiv-2401.07561v2 PDF p.6, arxiv-2401.07561v2 PDF p.7. Source domains are explicit below. -/
def UniformQueryBounds
    (construct : (P : PublicParameters) → Construction P) : Prop :=
  ∃ Cr Co : ℝ, 0 < Cr ∧ 0 < Co ∧ ∃ p : ℕ, ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
    ∀ P, P.eps ≤ eps0 →
      let L := Real.logb 2 P.eps⁻¹
      ((construct P).circuit.queryCount ⟨0,by have := P.d_pos; omega⟩ : ℝ) ≤
        Cr*P.kappa*L^2*max 1 (Real.logb 2 (2+P.kappa*L^2))^p ∧
      ∀ j : Fin P.d, ((construct P).circuit.queryCount j.succ : ℝ) ≤ Co*L

example {b a n : ℕ} (d : ℕ) (fits : d+1 ≤ 2^b)
    (PL PR : Matrix.unitaryGroup (Qubits b) ℂ)
    (U : Fin (d+1) → Matrix (Qubits (a+n)) (Qubits (a+n)) ℂ) :
    conjSuperop (paddedLinearCombination d fits PL PR U) 0 = 0 := by simp [conjSuperop]

end QAlgorithms.QuantumEsscher


