-- Prove2me | Definitions.Def_QAlgorithms_Defs_TaylorSimulationPrograms
-- name    : QAlgorithms_Defs_TaylorSimulationPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:29:48.995052+00:00
-- url     : https://prove2.me/theorems/91682641-9ad6-4870-b7db-07486cc27b4c
-- title:
--   TaylorSimulationPrograms
-- statement:
--   TaylorSimulationPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\TaylorSimulationPrograms.lean

import Definitions.Def_QAlgorithms_Defs_TaylorSegmentChannels
import Definitions.Def_QAlgorithms_Defs_QECC
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.TaylorSimulation

/-- QAlgorithms.TaylorSimulation.SegmentedProgram: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4. Source domains are explicit below. -/
structure SegmentedProgram (n L K : ℕ) where
  alpha : Fin L → ℝ
  positive : ∀ i, 0 < alpha i
  mass_pos : 0 < ∑ i, alpha i
  time : ℝ
  time_nonnegative : 0 ≤ time
  labelBits : ℕ
  labels : TaylorWord L K ↪ Qubits labelBits
  prep : ℝ → Matrix.unitaryGroup (Qubits labelBits) ℂ
  prepares : ∀ dt, 0 ≤ dt →
    let coefficient := fun w : TaylorWord L K => dt^w.1.val/(w.1.val.factorial : ℝ)*∏ i, alpha (w.2 i)
    let mass := ∑ w, coefficient w
    ∀ z, act (prep dt : Matrix _ _ ℂ) (zeroKet labelBits) z =
      ∑ w, if labels w = z then (Real.sqrt (coefficient w/mass) : ℂ) else 0
  compilation : ℝ → OracleCircuit oneTwoQubitGateSet
    (fun _ : Fin 1 => 1+Nat.clog 2 L+n) (1+(labelBits+n))

/-- QAlgorithms.TaylorSimulation.SegmentedProgram.durations: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def SegmentedProgram.durations {n L K : ℕ} (P : SegmentedProgram n L K) : List ℝ :=
  let mass := ∑ i, P.alpha i
  let r := ⌈mass*P.time/Real.log 2⌉₊
  if r = 0 then [] else List.replicate (r-1) (Real.log 2/mass) ++ [P.time-(r-1)*Real.log 2/mass]

/-- QAlgorithms.TaylorSimulation.SegmentedProgram.wordMass: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def SegmentedProgram.wordMass {n L K : ℕ} (P : SegmentedProgram n L K) (dt : ℝ) : ℝ :=
  ∑ w : TaylorWord L K, dt^w.1.val/(w.1.val.factorial : ℝ)*∏ i, P.alpha (w.2 i)

/-- QAlgorithms.TaylorSimulation.SegmentedProgram.wordSelect: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def SegmentedProgram.wordSelect {n L K : ℕ} (P : SegmentedProgram n L K)
    (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) :
    Matrix (Qubits P.labelBits × Qubits n) (Qubits P.labelBits × Qubits n) ℂ :=
  let Pi : Matrix (Qubits P.labelBits) (Qubits P.labelBits) ℂ :=
    ∑ w : TaylorWord L K, Matrix.single (P.labels w) (P.labels w) 1
  (∑ w : TaylorWord L K, Matrix.kronecker (Matrix.single (P.labels w) (P.labels w) 1)
    ((-Complex.I)^w.1.val • (List.ofFn fun i => (H (w.2 i) : Matrix _ _ ℂ)).prod)) +
    Matrix.kronecker (1-Pi) (1 : Matrix (Qubits n) (Qubits n) ℂ)

/-- QAlgorithms.TaylorSimulation.SegmentedProgram.block: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def SegmentedProgram.block {n L K : ℕ} (P : SegmentedProgram n L K)
    (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) (dt : ℝ) :
    Matrix (Bool × (Qubits P.labelBits × Qubits n)) (Bool × (Qubits P.labelBits × Qubits n)) ℂ :=
  let B := P.prep dt
  let W := Matrix.kronecker (star (B : Matrix _ _ ℂ)) 1*P.wordSelect H*Matrix.kronecker (B : Matrix _ _ ℂ) 1
  Matrix.kronecker (1 : Matrix Bool Bool ℂ) W *
    Matrix.kronecker (rotY (2*Real.arccos (P.wordMass dt/2))) (1 : Matrix (Qubits P.labelBits × Qubits n) _ ℂ)

/-- QAlgorithms.TaylorSimulation.SegmentedProgram.amplified: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def SegmentedProgram.amplified {n L K : ℕ} (P : SegmentedProgram n L K)
    (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) (dt : ℝ) :=
  let W := P.block H dt
  let J : Matrix (Bool × Qubits P.labelBits) (Bool × Qubits P.labelBits) ℂ :=
    pureDensity (ket (false,0))
  let R := 1-2 • (Matrix.kronecker J (1 : Matrix (Qubits n) (Qubits n) ℂ)).submatrix
    (fun z : Bool × (Qubits P.labelBits × Qubits n) => ((z.1,z.2.1),z.2.2))
    (fun z : Bool × (Qubits P.labelBits × Qubits n) => ((z.1,z.2.1),z.2.2))
  show Matrix (Bool × (Qubits P.labelBits × Qubits n))
    (Bool × (Qubits P.labelBits × Qubits n)) ℂ from -(W*R*star W*R*W)

/-- QAlgorithms.TaylorSimulation.signedOracle: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def signedOracle {n L : ℕ} (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) :
    Matrix (Qubits (1+Nat.clog 2 L+n)) (Qubits (1+Nat.clog 2 L+n)) ℂ :=
  let J : Matrix (Qubits (1+Nat.clog 2 L+n)) (Bool × (Fin L × Qubits n)) ℂ :=
    Matrix.of fun z input => if z = Fin.append (Fin.append (fun _ : Fin 1 => input.1) (natToBits (Nat.clog 2 L) input.2.1)) input.2.2
      then 1 else 0
  let selected : Matrix (Fin L × Qubits n) (Fin L × Qubits n) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then -Complex.I*(H q.1 : Matrix _ _ ℂ) p.2 q.2 else 0
  extendEncodedUnitary J (controlled selected)

/-- QAlgorithms.TaylorSimulation.IsSourceCompilation: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def IsSourceCompilation {n L K : ℕ} (P : SegmentedProgram n L K) : Prop :=
  ∀ H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ,
    ∀ dt ∈ P.durations,
      (P.compilation dt).unitary (fun _ => signedOracle H) =
        (P.amplified H dt).submatrix
          (fun z => ((qubitsAppendEquiv 1 (P.labelBits+n) z).1 0,
            qubitsAppendEquiv P.labelBits n (qubitsAppendEquiv 1 (P.labelBits+n) z).2))
          (fun z => ((qubitsAppendEquiv 1 (P.labelBits+n) z).1 0,
            qubitsAppendEquiv P.labelBits n (qubitsAppendEquiv 1 (P.labelBits+n) z).2))

/-- Execute the actual compiled list, reindexed to the compensation/label/system registers.
Source: arxiv-1412.4687v1 PDF pp.3-4. Output and counted calls now use the same circuit even
before the source-compilation identity is established. -/
def SegmentedProgram.executed {n L K : ℕ} (P : SegmentedProgram n L K)
    (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) (dt : ℝ) :
    Matrix (Bool × (Qubits P.labelBits × Qubits n))
      (Bool × (Qubits P.labelBits × Qubits n)) ℂ :=
  ((P.compilation dt).unitary (fun _ => signedOracle H)).submatrix
    (fun z => Fin.append (fun _ : Fin 1 => z.1) (Fin.append z.2.1 z.2.2))
    (fun z => Fin.append (fun _ : Fin 1 => z.1) (Fin.append z.2.1 z.2.2))

/-- QAlgorithms.TaylorSimulation.SegmentedProgram.output: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def SegmentedProgram.output {n L K : ℕ} (P : SegmentedProgram n L K)
    (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) : Superop (Qubits n) (Qubits n) :=
  fun rho => P.durations.foldl (fun state dt =>
    let initial := (Matrix.kronecker (pureDensity (ket (false,0))) state).submatrix
      (fun z : Bool × (Qubits P.labelBits × Qubits n) => ((z.1,z.2.1),z.2.2))
      (fun z : Bool × (Qubits P.labelBits × Qubits n) => ((z.1,z.2.1),z.2.2))
    traceLeft ((conjSuperop (P.executed H dt) initial).submatrix
      (fun z : (Bool × Qubits P.labelBits) × Qubits n => (z.1.1,(z.1.2,z.2)))
      (fun z : (Bool × Qubits P.labelBits) × Qubits n => (z.1.1,(z.1.2,z.2))))) rho

/-- QAlgorithms.TaylorSimulation.SegmentedProgram.queryCount: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def SegmentedProgram.queryCount {n L K : ℕ} (P : SegmentedProgram n L K) : ℕ :=
  (P.durations.map fun dt => (P.compilation dt).queryCount 0).sum

/-- QAlgorithms.TaylorSimulation.SegmentedProgram.gateCount: arxiv-1412.4687v1 PDF p.3, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
def SegmentedProgram.gateCount {n L K : ℕ} (P : SegmentedProgram n L K) : ℕ :=
  (P.durations.map fun dt => (P.compilation dt).gateCount).sum

/-- QAlgorithms.TaylorSimulation.IsAccurate: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def IsAccurate {n L K : ℕ} (P : SegmentedProgram n L K)
    (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) (eps : ℝ) : Prop :=
  (∑ i, (P.alpha i : ℂ) • (H i : Matrix (Qubits n) (Qubits n) ℂ)).IsHermitian ∧ 0 < eps ∧
    ∀ psi : EuclideanSpace ℂ (Qubits n), IsState psi →
      traceNorm (P.output H (pureDensity psi)-conjSuperop
        (NormedSpace.exp (-(Complex.I*(P.time : ℂ)) • ∑ i, (P.alpha i : ℂ) • (H i : Matrix (Qubits n) (Qubits n) ℂ)))
        (pureDensity psi)) ≤ eps

example {n L K : ℕ} (P : SegmentedProgram n L K) (h : P.time = 0)
    (H : Fin L → Matrix.unitaryGroup (Qubits n) ℂ) (rho : Matrix (Qubits n) (Qubits n) ℂ) :
    P.output H rho = rho := by simp [SegmentedProgram.output,SegmentedProgram.durations,h]

end QAlgorithms.TaylorSimulation


