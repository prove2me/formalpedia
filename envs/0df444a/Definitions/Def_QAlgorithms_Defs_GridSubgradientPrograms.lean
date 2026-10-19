-- Prove2me | Definitions.Def_QAlgorithms_Defs_GridSubgradientPrograms
-- name    : QAlgorithms_Defs_GridSubgradientPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:34.661455+00:00
-- url     : https://prove2.me/theorems/5b0b6da5-6d7d-4eb0-b41a-958650276a84
-- title:
--   GridSubgradientPrograms
-- statement:
--   GridSubgradientPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\GridSubgradientPrograms.lean

import Definitions.Def_QAlgorithms_Defs_FiniteValueAccess
import Definitions.Def_QAlgorithms_Defs_SamplingUtilities
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
noncomputable section

namespace QAlgorithms.ValueAccess

variable {n m d k b w M K N c out : ℕ}

/-- Finite-seed physical query procedure, 1809.00643 pp.10–13 and
2503.17356 pp.22–23. Initial states and oracle-independent unitaries are
fixed before f/U, and control access is disabled. -/
structure RandomizedQueryProcedure (d : ℕ) (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] where
  seeds : ℕ
  seeds_pos : 0 < seeds
  initial : Fin seeds → EuclideanSpace ℂ I
  normalized : ∀ s, IsState (initial s)
  circuit : Fin seeds → FiniteOracleCircuit (fun _ : Fin 1 => J) (fun _ => false) I
  decode : Fin seeds → I → Fin d → ℝ

/-- Event law from the actual seed-average circuit Born probabilities,
1809.00643 pp.11–13; 2503.17356 pp.22–23. -/
def queryProcedureLaw {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (P : RandomizedQueryProcedure d J I)
    (U : Matrix J J ℂ) (event : (Fin d → ℝ) → Prop) : ℝ :=
  (open Classical in
    (P.seeds : ℝ)⁻¹ * ∑ s, probEvent
      (act ((P.circuit s).unitary (fun _ => U)) (P.initial s))
      (fun z => event (P.decode s z)))

/-- Actual worst-seed oracle/adjoint call count (1809.00643 p.12). -/
def procedureQueries {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (P : RandomizedQueryProcedure d J I) : ℕ :=
  Finset.univ.sup fun s => (P.circuit s).queryCount 0

/-- Signed frequency decoder for the original binary QFT index,
1809.00643 pp.10–11. It wraps the upper half to negative values. -/
def jordanFrequency (k : ℕ) (z : Qubits k) : ℝ :=
  if 1 ≤ k ∧ 2 ^ (k - 1) ≤ bitsToNat z then
    (bitsToNat z : ℝ) / (2 : ℝ) ^ k - 1
  else (bitsToNat z : ℝ) / (2 : ℝ) ^ k

/-- Exact one-shot standard-oracle Jordan operator, 1809.00643 pp.10–11.
Value computation, known answer phase, inverse query, and inverse QFT
are separate ordered operations; no phase-oracle access is granted. -/
def jordanOperator {d k b : ℕ} (decode : Qubits b → ℝ) (B : ℝ) (hB : 0 < B)
    (U : Matrix ((Fin d → Qubits k) × Qubits b)
      ((Fin d → Qubits k) × Qubits b) ℂ) :
    Matrix ((Fin d → Qubits k) × Qubits b) ((Fin d → Qubits k) × Qubits b) ℂ :=
  Matrix.kronecker (piKron d (star (qftQubits k))) 1 *
    star U * Matrix.diagonal (fun z => Complex.exp
      (2 * Real.pi * Complex.I * ((2 : ℂ) ^ k) * (decode z.2 : ℂ) / (3 * (B : ℂ)))) * U * Matrix.kronecker (piKron d (hadamardN k)) 1

/-- A physical compilation of the printed Jordan/median procedure
(1809.00643 pp.10–13; 2503.17356 pp.22–23).
The repetitions satisfy the source median-amplification schedule; 100 is a
conservative absolute choice for its O(log(d/rho)) repetition count.
The certificate fixes its exact distribution by the source circuit, not
by an estimation-success or complexity assumption. Circuit/query data remain
operational and input independent. -/
structure JordanCompilation (d b repeats : ℕ)
    (X I : Type) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I] where
  grid : CompatibleHypergrid d X
  repeats_pos : 0 < repeats
  L : ℝ
  delta : ℝ
  rho : ℝ
  L_pos : 0 < L
  delta_pos : 0 < delta
  rho_pos : 0 < rho
  rho_le : rho ≤ 1 / 3
  repeats_bound : 100 * Real.log (2 * (d : ℝ) / rho) ≤ (repeats : ℝ)
  meshBudget_bound : grid.meshBudget ≤
    min (delta/(1000000000*d*L)) (grid.r2^2/(1000000000*d*grid.r1))
  r2_eq : grid.r2 = Real.sqrt (delta * grid.r1 * rho / (d * L))
  radius : ℝ
  radius_eq : radius = 2 * grid.r2 / d
  radius_pos : 0 < radius
  B : ℝ
  B_pos : 0 < B
  B_bound : L * radius ≤ B
  phaseCalibration : 3 * B / (84 * Real.pi * delta) = (2 : ℝ) ^ grid.jordanBits
  procedure : RandomizedQueryProcedure d (X × Qubits b) I
  encoding : FixedPointEncoding b
  realizes : ∀ U : Matrix (X × Qubits b) (X × Qubits b) ℂ,
    U ∈ Matrix.unitaryGroup _ ℂ →
    (∀ y z, y.1 ≠ z.1 → U y z = 0) →
    ∀ event : (Fin d → ℝ) → Prop,
    queryProcedureLaw procedure U event =
      (open Classical in
        ((2 : ℝ) ^ (d * grid.centerBits))⁻¹ *
        ∑ center : Fin d → Qubits grid.centerBits,
          ∑ outcomes : Fin repeats → (Fin d → Qubits grid.jordanBits) × Qubits b,
            (if event (coordinateMedian (List.ofFn fun t => fun j =>
              3 * B / radius * jordanFrequency grid.jordanBits ((outcomes t).1 j)))
            then ∏ t, prob
              (act (jordanOperator encoding.value B B_pos
                (U.submatrix
                  (fun z => (grid.localIndex center z.1,z.2))
                  (fun z => (grid.localIndex center z.1,z.2))))
                (ket ((fun _ _ => false),0))) (outcomes t)
            else 0))

/-- Compiled standard-oracle noisy-subgradient routine, 2503.17356 pp.22–23.
All local query coordinates, phase scale and original QFT indices are pinned.
The physical compilation has no estimation-success or resource bound field. -/
def noisySubgradientProgram {d b t : ℕ} {X I : Type} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] (C : JordanCompilation d b t X I) :
    RandomizedQueryProcedure d (X × Qubits b) I :=
  C.procedure

/-- Complete register for the relational Jordan circuit, 1809.00643 pp.27–28:
a protected original grid input and fresh full oracle registers. -/
abbrev RelationalJordanRegister (d k b w shots : ℕ) (X : Type) :=
  (Fin d → Qubits k) × (Fin shots → X × (Qubits b × Qubits w))

/-- One original U application on a fresh private oracle register,
1809.00643 p.28. All other registers, including the protected input, persist. -/
def relationalQueryLift {d k b w shots : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (i : Fin shots) (U : Matrix (X × (Qubits b × Qubits w)) (X × (Qubits b × Qubits w)) ℂ) :
    Matrix (RelationalJordanRegister d k b w shots X)
      (RelationalJordanRegister d k b w shots X) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ (∀ j, j ≠ i → p.2 j = q.2 j)
    then U (p.2 i) (q.2 i) else 0

/-- Copy/uncompute known input labels while protecting the original x,
1809.00643 p.28. The finite permutation swaps a public reset label with
the desired query label; it is an involution. No oracle call is hidden. -/
def relationalInputCopy {d k b w shots : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (zeroIndex : X) (index : (Fin d → Qubits k) → X) :
    Matrix (RelationalJordanRegister d k b w shots X)
      (RelationalJordanRegister d k b w shots X) ℂ :=
  Matrix.of fun p q => if p =
    (q.1,fun i => (Equiv.swap zeroIndex (index q.1) (q.2 i).1,(q.2 i).2)) then 1 else 0

/-- Actual relational phase-compute/uncompute and protected inverse QFT,
1809.00643 pp.27–28. Median amplification is coherent and all garbage
remains in the output. U-dagger is not assumed to clean phase-modified
garbage exactly. The repetition parameter is the actual number of calls. -/
def relationalJordanOperator {d k b w shots : ℕ} {X : Type} [Fintype X] [DecidableEq X]
    (zeroIndex : X) (index : (Fin d → Qubits k) → X) (decode : Qubits b → ℝ) (B : ℝ) (hB : 0 < B)
    (U : Matrix (X × (Qubits b × Qubits w)) (X × (Qubits b × Qubits w)) ℂ) :
    Matrix (RelationalJordanRegister d k b w shots X)
      (RelationalJordanRegister d k b w shots X) ℂ :=
  letI : DecidableEq (RelationalJordanRegister d k b w shots X) := Classical.decEq _
  let copy := relationalInputCopy (d:=d) (k:=k) (b:=b) (w:=w) (shots:=shots) zeroIndex index
  let calls := orderedProd (fun i : Fin shots => relationalQueryLift (d:=d) (k:=k) i U)
  let phase := Matrix.diagonal fun z : RelationalJordanRegister d k b w shots X =>
    Complex.exp (2 * Real.pi * Complex.I * (2 : ℂ)^k *
      (realMedian (List.ofFn fun i => decode (z.2 i).2.1) : ℂ) / (3 * (B : ℂ)))
  Matrix.kronecker (piKron d (star (qftQubits k))) 1 *
    copy * star calls * phase * calls * copy *
      Matrix.kronecker (piKron d (hadamardN k)) 1

/-- Physical compilation of Corollary 29's relational branch,
1809.00643 pp.27–28, used by Lemma 18's footnote.
257 fresh answers amplify a 2/3-valid oracle beyond 1-1/1200:
Hoeffding gives exp(-257/18)<1/1200. The odd median and protected
input and logarithmic median-amplification schedule are explicit. The
constant 100 also covers the relational phase-approximation loss.
The certificate pins an executed circuit law,
never an estimation success probability or a complexity conclusion. -/
structure RelationalJordanCompilation (d b w repeats : ℕ)
    (X I : Type) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I] where
  grid : CompatibleHypergrid d X
  zeroIndex : X
  repeats_pos : 0 < repeats
  L : ℝ
  delta : ℝ
  rho : ℝ
  L_pos : 0 < L
  delta_pos : 0 < delta
  rho_pos : 0 < rho
  rho_le : rho ≤ 1/3
  repeats_bound : 100 * Real.log (2 * (d : ℝ) / rho) ≤ (repeats : ℝ)
  meshBudget_bound : grid.meshBudget ≤
    min (delta/(1000000000*d*L)) (grid.r2^2/(1000000000*d*grid.r1))
  r2_eq : grid.r2 = Real.sqrt (delta * grid.r1 * rho / (d*L))
  B : ℝ
  B_pos : 0 < B
  B_bound : L * (2*grid.r2/d) ≤ B
  phaseCalibration : 3*B/(84*Real.pi*delta) = (2:ℝ)^grid.jordanBits
  encoding : FixedPointEncoding b
  procedure : RandomizedQueryProcedure d (X × (Qubits b × Qubits w)) I
  realizes : ∀ U : Matrix (X × (Qubits b × Qubits w)) (X × (Qubits b × Qubits w)) ℂ,
    U ∈ Matrix.unitaryGroup _ ℂ → ∀ event : (Fin d → ℝ) → Prop,
      queryProcedureLaw procedure U event =
        (open Classical in
          ((2:ℝ)^(d*grid.centerBits))⁻¹ *
          ∑ center : Fin d → Qubits grid.centerBits,
            ∑ outcomes : Fin repeats →
                RelationalJordanRegister d grid.jordanBits b w 257 X,
              if event (coordinateMedian (List.ofFn fun t => fun j =>
                  3*B/(2*grid.r2/d) * jordanFrequency grid.jordanBits ((outcomes t).1 j)))
              then ∏ t, prob
                (act (relationalJordanOperator zeroIndex (grid.localIndex center) encoding.value B B_pos U)
                  (ket ((fun _ _ => false),fun _ => (zeroIndex,(0,0))))) (outcomes t)
              else 0)

/-- Separate relational access-mode branch, 1809.00643 p.12 footnote 7 and
pp.27–28. It does not grant relational-oracle access to the 2025 theorem. -/
def relationalNoisySubgradientProgram {d b w repeats : ℕ} {X I : Type}
    [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (C : RelationalJordanCompilation d b w repeats X I) :
    RandomizedQueryProcedure d (X × (Qubits b × Qubits w)) I := C.procedure

/-- Sanity check for the modeled source objects (arxiv-1809.00643v4, PDF pp.5,10,11,12,13; arxiv-2503.17356v2, PDF pp.22,23,30). -/
example : jordanFrequency 1 ![false] = 0 ∧ jordanFrequency 1 ![true] = -(1 / 2) := by
  constructor <;> norm_num [jordanFrequency, bitsToNat]

/-- Sanity check for the modeled source objects (arxiv-1809.00643v4, PDF pp.5,10,11,12,13; arxiv-2503.17356v2, PDF pp.22,23,30). -/
example {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (P : RandomizedQueryProcedure d J I) (U : Matrix J J ℂ) :
    queryProcedureLaw P U (fun _ => False) = 0 := by
  simp [queryProcedureLaw, probEvent]

end QAlgorithms.ValueAccess


