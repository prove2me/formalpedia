-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P85
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P85
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:07:04.951085+00:00
-- url     : https://prove2.me/theorems/d2ff9116-baca-4671-9cfd-f7f5042b1d29
-- title:
--   Definitions for Exact synthesis of multiqubit Clifford+T circuits
-- statement:
--   The objects the formalized statements of *Exact synthesis of multiqubit Clifford+T circuits* (arXiv:1212.0506) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `omegaGate`: The scalar generator of equation (1), PDF p.1, acts on zero wires.
--   - `gateSet`: Exactly H,S,CNOT,T and the eighth-root scalar, equation (1), PDF p.1.
--   - `ScalarExponent`: Natural denominator exponents, Definition 3, PDF p.2; also defined at zero.
--   - `VectorExponent`: Componentwise denominator validity, Definition 3, PDF p.2.
--   - `MatrixExponent`: Arbitrary-dimension matrix denominator validity, Definition 3, PDF p.2.
--   - `LeastScalarExponent`: Least natural exponent as a graph, Definition 3, PDF p.2; no off-domain fallback.
--   - `LeastMatrixExponent`: Least natural matrix exponent as a graph, Definition 3, PDF p.2.
--   - `kResidue`: The k-residue; statements always carry denominator validity, PDF p.3.
--   - `residueConjugate`: Conjugation pqrs -> rqps, equation (2) and §3.3, PDF p.2.
--   - `residueNorm`: Multiplication uses the quotient algebra, not pointwise multiplication, PDF p.3.
--   - `TwiceReducible`: Twice reducible means an image of multiplication by the residue of 2, PDF p.3.
--   - `Dyadic`: Real dyadic coefficients, Definition 1, PDF p.2.
--   - `DyadicCoordinates`: Unique omega-power coordinates of a D[omega] scalar, Definition 1, PDF p.2. Using coordinates as data avoids choosing a value outside the coefficient ring.
--   - `dyadicValue`: Dyadic scalar extension of the imported integer-coordinate evaluator, PDF p.2. The frozen evaluator uses ascending powers; Fin.rev supplies the paper's descending order.
--   - `coordinateWeight`: Squared weight, Definition 2, equation (4), PDF p.2.
--   - `vectorNormSq`: Squared vector norm, Definition 2, PDF p.2.
--   - `twoLevel`: Ordered two-coordinate block, §4, PDF p.3; callers provide distinct coordinates.
--   - `LevelOp`: The paper's actual one- and two-level operations, §4, PDF pp.3–4.
--   - `levelMatrix`: Exact operation matrices; omega is one-level, PDF pp.3–4.
--   - `levelWordMatrix`: The head acts first, with identity for the empty word, PDF p.4.
--   - `inverseOp`: An inverse operation expanded in the same alphabet, PDF pp.4–5.
--   - `inverseWord`: Chronological inverse of a reduction word, PDF p.5.
--   - `liftHT`: Lift a chronological H/T word onto distinct ordered rows, Lemma 4, PDF p.4.
--   - `rowCandidates`: Finite candidate words from the three cases of the row proof, PDF p.4. Printed HT^m becomes the chronological word T^m,H. Two such rounds suffice.
--   - `rowWord`: First successful row word in the proof's bounded candidate list, PDF p.4. This exact predicate search counts only output letters; no arithmetic cost is asserted.
--   - `PassTrace`: A single positive-exponent column pass from the inner induction, PDF p.4. Only matched irreducible pairs are processed; stopping means every entry is reducible.
--   - `baseColumnWord`: Swap to the target and correct its eighth-root phase, Lemma 5 base case, PDF p.4.
--   - `ColumnTrace`: The column proof's actual pass sequence and its base case, Lemma 5, PDF p.4.
--   - `shiftOp`: Lift a tail operation, fixing the first coordinate, Lemma 6, PDF p.4.
--   - `MatrixTrace`: Column elimination in the order of Lemma 6, PDF p.4, with §7's 3k tail allowance. The trace records reductions; inverseWord returns the factorization.
--   - `indexedMatrix`: Frozen most-significant-bit indexing, applied to an input operator, PDF p.7.
--   - `qubitLevelMatrix`: A level operation expressed on the qubit register, PDF pp.5,7.
--   - `CompilationTrace`: A gate-by-gate compilation trace with the same trailing clean helper, PDF pp.5,7. Each output segment is an actual elementary circuit, bounded by B*n gates.
--   - `multiplyControlled`: All controls are positive and precede the target wire, §5.2, PDF p.5.
--   - `boundedOperators`: Distinct phase-sensitive unitary operators cleared by k, §8, PDF p.7.
-- source:
--   Exact synthesis of multiqubit Clifford+T circuits, arXiv:1212.0506v3, https://arxiv.org/abs/1212.0506v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_CircuitResources
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P13

/-!
Giles and Selinger, arXiv:1212.0506v3, PDF pp.1–7.
Absolute phase is retained. Words are chronological (head first).
Only the pinned accepted definitions are imported from earlier papers.
The local traces record output operations, not arithmetic running time.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P85

open scoped Classical BigOperators
open QAlgorithms
open QAlgorithms.Papers.Independent.Gap48.P10
  (InZomega InDomega Residue bits residue residueMultiply Reducible)
open QAlgorithms.Papers.Independent.Support21.P13
  (synthesisRing integralRing coordinateValue HTLetter htWordMatrix EntriesInRing cliffordTLibrary)

local notation "omega" => QAlgorithms.gateT true true
local notation "sqrtTwo" => ((Real.sqrt 2 : ℝ) : ℂ)

/-- The scalar generator of equation (1), PDF p.1, acts on zero wires. -/
def omegaGate : Gate := ⟨0, fun _ _ => omega⟩

/-- Exactly H,S,CNOT,T and the eighth-root scalar, equation (1), PDF p.1. -/
def gateSet : Set Gate := cliffordTLibrary ∪ {omegaGate}

/-- Natural denominator exponents, Definition 3, PDF p.2; also defined at zero. -/
def ScalarExponent (t : ℂ) (k : ℕ) : Prop := InZomega (sqrtTwo ^ k * t)

/-- Componentwise denominator validity, Definition 3, PDF p.2. -/
def VectorExponent {ι : Type*} (u : ι → ℂ) (k : ℕ) : Prop :=
  ∀ i, ScalarExponent (u i) k

/-- Arbitrary-dimension matrix denominator validity, Definition 3, PDF p.2. -/
def MatrixExponent {ι : Type*} (U : Matrix ι ι ℂ) (k : ℕ) : Prop :=
  ∀ i j, ScalarExponent (U i j) k

/-- Least natural exponent as a graph, Definition 3, PDF p.2; no off-domain fallback. -/
def LeastScalarExponent (t : ℂ) (k : ℕ) : Prop :=
  ScalarExponent t k ∧ ∀ l, ScalarExponent t l → k ≤ l

/-- Least natural matrix exponent as a graph, Definition 3, PDF p.2. -/
def LeastMatrixExponent {ι : Type*} (U : Matrix ι ι ℂ) (k : ℕ) : Prop :=
  MatrixExponent U k ∧ ∀ l, MatrixExponent U l → k ≤ l

/-- The k-residue; statements always carry denominator validity, PDF p.3. -/
def kResidue (t : ℂ) (k : ℕ) : Residue := residue (sqrtTwo ^ k * t)

/-- Conjugation pqrs -> rqps, equation (2) and §3.3, PDF p.2. -/
def residueConjugate (x : Residue) : Residue := ![x 2, x 1, x 0, x 3]

/-- Multiplication uses the quotient algebra, not pointwise multiplication, PDF p.3. -/
def residueNorm (x : Residue) : Residue := residueMultiply (residueConjugate x) x

/-- Twice reducible means an image of multiplication by the residue of 2, PDF p.3. -/
def TwiceReducible (x : Residue) : Prop :=
  ∃ y : Residue, residueMultiply (bits 0) y = x

/-- Real dyadic coefficients, Definition 1, PDF p.2. -/
def Dyadic (a : ℝ) : Prop := ∃ z : ℤ, ∃ k : ℕ, a = (z : ℝ) / 2 ^ k

/-- Unique omega-power coordinates of a D[omega] scalar, Definition 1, PDF p.2.
Using coordinates as data avoids choosing a value outside the coefficient ring. -/
abbrev DyadicCoordinates := {a : Fin 4 → ℝ // ∀ i, Dyadic (a i)}

/-- Dyadic scalar extension of the imported integer-coordinate evaluator, PDF p.2.
The frozen evaluator uses ascending powers; Fin.rev supplies the paper's descending order. -/
def dyadicValue (a : Fin 4 → ℝ) : ℂ :=
  ∑ j : Fin 4, (a j : ℂ) *
    coordinateValue (fun i => if i = Fin.rev j then (1 : ℤ) else 0)

/-- Squared weight, Definition 2, equation (4), PDF p.2. -/
def coordinateWeight (a : Fin 4 → ℝ) : ℝ := ∑ j, a j ^ 2

/-- Squared vector norm, Definition 2, PDF p.2. -/
def vectorNormSq {ι : Type*} [Fintype ι] (u : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (u i)

/-- Ordered two-coordinate block, §4, PDF p.3; callers provide distinct coordinates. -/
def twoLevel {d : ℕ} (M : Matrix Bool Bool ℂ) (j l : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b =>
    if a = j then (if b = j then M false false else if b = l then M false true else 0)
    else if a = l then (if b = j then M true false else if b = l then M true true else 0)
    else if a = b then 1 else 0

/-- The paper's actual one- and two-level operations, §4, PDF pp.3–4. -/
inductive LevelOp (d : ℕ) where
  | x (j l : Fin d) (distinct : j ≠ l)
  | h (j l : Fin d) (distinct : j ≠ l)
  | t (j l : Fin d) (distinct : j ≠ l)
  | phase (j : Fin d)

/-- Exact operation matrices; omega is one-level, PDF pp.3–4. -/
def levelMatrix {d : ℕ} : LevelOp d → Matrix (Fin d) (Fin d) ℂ
  | .x j l _ => twoLevel pauliX j l
  | .h j l _ => twoLevel hadamard j l
  | .t j l _ => twoLevel gateT j l
  | .phase j => Matrix.diagonal (fun i => if i = j then omega else 1)

/-- The head acts first, with identity for the empty word, PDF p.4. -/
def levelWordMatrix {d : ℕ} (w : List (LevelOp d)) : Matrix (Fin d) (Fin d) ℂ :=
  (w.map levelMatrix).reverse.prod

/-- An inverse operation expanded in the same alphabet, PDF pp.4–5. -/
def inverseOp {d : ℕ} : LevelOp d → List (LevelOp d)
  | .x j l h => [.x j l h]
  | .h j l h => [.h j l h]
  | .t j l h => List.replicate 7 (.t j l h)
  | .phase j => List.replicate 7 (.phase j)

/-- Chronological inverse of a reduction word, PDF p.5. -/
def inverseWord {d : ℕ} (w : List (LevelOp d)) : List (LevelOp d) :=
  w.reverse.flatMap inverseOp

/-- Lift a chronological H/T word onto distinct ordered rows, Lemma 4, PDF p.4. -/
def liftHT {d : ℕ} (j l : Fin d) (h : j ≠ l) (w : List HTLetter) : List (LevelOp d) :=
  w.map (fun a => match a with | .h => .h j l h | .t => .t j l h)

/-- Finite candidate words from the three cases of the row proof, PDF p.4.
Printed HT^m becomes the chronological word T^m,H. Two such rounds suffice. -/
def rowCandidates : List (List HTLetter) :=
  let rounds := (List.range 8).map (fun m => List.replicate m HTLetter.t ++ [.h])
  [[]] ++ rounds ++ rounds.flatMap (fun a => rounds.map (fun b => a ++ b))

/-- First successful row word in the proof's bounded candidate list, PDF p.4.
This exact predicate search counts only output letters; no arithmetic cost is asserted. -/
def rowWord (u : Bool → ℂ) (k : ℕ) : List HTLetter :=
  ((rowCandidates.find? (fun w => decide
    (VectorExponent ((htWordMatrix w).mulVec u) (k - 1)))).getD [])

/-- A single positive-exponent column pass from the inner induction, PDF p.4.
Only matched irreducible pairs are processed; stopping means every entry is reducible. -/
inductive PassTrace {d : ℕ} (k : ℕ) :
    (Fin d → ℂ) → List (LevelOp d) → Prop where
  | done (u : Fin d → ℂ) (stop : ∀ i, Reducible (kResidue (u i) k)) :
      PassTrace k u []
  | pair (u : Fin d → ℂ) (j l : Fin d) (h : j ≠ l)
      (active : ¬ Reducible (kResidue (u j) k))
      (matched : residueNorm (kResidue (u j) k) = residueNorm (kResidue (u l) k))
      (rest : List (LevelOp d))
      (next : PassTrace k
        ((levelWordMatrix (liftHT j l h (rowWord (fun b => if b then u l else u j) k))).mulVec u)
        rest) :
      PassTrace k u (liftHT j l h (rowWord (fun b => if b then u l else u j) k) ++ rest)

/-- Swap to the target and correct its eighth-root phase, Lemma 5 base case, PDF p.4. -/
def baseColumnWord {d : ℕ} (first j : Fin d) (m : Fin 8) : List (LevelOp d) :=
  (if h : first = j then [] else [.x first j h]) ++ List.replicate m.val (.phase first)

/-- The column proof's actual pass sequence and its base case, Lemma 5, PDF p.4. -/
inductive ColumnTrace {d : ℕ} (first : Fin d) :
    (Fin d → ℂ) → ℕ → List (LevelOp d) → Prop where
  | base (j : Fin d) (m : Fin 8) :
      ColumnTrace first (fun i => if i = j then omega ^ (8 - m.val) else 0) 0
        (baseColumnWord first j m)
  | step (u : Fin d → ℂ) (k : ℕ) (pass rest : List (LevelOp d))
      (onePass : PassTrace (k + 1) u pass)
      (next : ColumnTrace first ((levelWordMatrix pass).mulVec u) k rest) :
      ColumnTrace first u (k + 1) (pass ++ rest)

/-- Lift a tail operation, fixing the first coordinate, Lemma 6, PDF p.4. -/
def shiftOp {d : ℕ} : LevelOp d → LevelOp (d + 1)
  | .x j l h => .x j.succ l.succ (fun e => h (Fin.succ_injective d e))
  | .h j l h => .h j.succ l.succ (fun e => h (Fin.succ_injective d e))
  | .t j l h => .t j.succ l.succ (fun e => h (Fin.succ_injective d e))
  | .phase j => .phase j.succ

/-- Column elimination in the order of Lemma 6, PDF p.4, with §7's 3k tail allowance.
The trace records reductions; inverseWord returns the factorization. -/
inductive MatrixTrace : {d : ℕ} → Matrix (Fin d) (Fin d) ℂ → ℕ →
    List (LevelOp d) → Prop where
  | empty (U : Matrix (Fin 0) (Fin 0) ℂ) (k : ℕ) : MatrixTrace U k []
  | step {d : ℕ} (U : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (k : ℕ)
      (pass : List (LevelOp (d + 1))) (rest : List (LevelOp d))
      (column : ColumnTrace 0 (fun i => U i 0) k pass)
      (tail : MatrixTrace ((levelWordMatrix pass * U).submatrix Fin.succ Fin.succ) (3 * k) rest) :
      MatrixTrace U k (pass ++ rest.map shiftOp)

/-- Frozen most-significant-bit indexing, applied to an input operator, PDF p.7. -/
def indexedMatrix {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  U.submatrix (bitsEquivFin n).symm (bitsEquivFin n).symm

/-- A level operation expressed on the qubit register, PDF pp.5,7. -/
def qubitLevelMatrix {n : ℕ} (g : LevelOp (2 ^ n)) : Matrix (Qubits n) (Qubits n) ℂ :=
  (levelMatrix g).submatrix (bitsEquivFin n) (bitsEquivFin n)

/-- A gate-by-gate compilation trace with the same trailing clean helper, PDF pp.5,7.
Each output segment is an actual elementary circuit, bounded by B*n gates. -/
inductive CompilationTrace (B n : ℕ) : List (LevelOp (2 ^ n)) →
    Circuit gateSet (n + 1) → Prop where
  | nil : CompilationTrace B n [] []
  | cons (g : LevelOp (2 ^ n)) (w : List (LevelOp (2 ^ n)))
      (segment rest : Circuit gateSet (n + 1))
      (exactSegment : ImplementsWithCleanAncillas segment.unitary (qubitLevelMatrix g))
      (sizeSegment : segment.size ≤ B * n)
      (next : CompilationTrace B n w rest) :
      CompilationTrace B n (g :: w) (segment ++ rest)

/-- All controls are positive and precede the target wire, §5.2, PDF p.5. -/
def multiplyControlled (r : ℕ) (M : Matrix Bool Bool ℂ) :
    Matrix (Qubits (r + 1)) (Qubits (r + 1)) ℂ :=
  fun y z =>
    if (∀ i : Fin r, y i.castSucc = z i.castSucc) then
      if (∀ i : Fin r, z i.castSucc = true) then M (y (Fin.last r)) (z (Fin.last r))
      else if y (Fin.last r) = z (Fin.last r) then 1 else 0
    else 0

/-- Distinct phase-sensitive unitary operators cleared by k, §8, PDF p.7. -/
def boundedOperators (n k : ℕ) :=
  {U : Matrix (Qubits n) (Qubits n) ℂ //
    U ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧ MatrixExponent U k}

example (t : ℂ) : ScalarExponent t 0 ↔ InZomega t := by simp [ScalarExponent]

example : Dyadic 0 := ⟨0, 0, by norm_num⟩

example {d : ℕ} (M : Matrix Bool Bool ℂ) (j l : Fin d) (h : j ≠ l) :
    twoLevel M j l j l = M false true := by simp [twoLevel, h, Ne.symm h]

example {d : ℕ} (j : Fin d) : levelMatrix (LevelOp.phase j) j j = omega := by
  simp [levelMatrix]

example {d : ℕ} (first : Fin d) (m : Fin 8) :
    baseColumnWord first first m = List.replicate m.val (.phase first) := by
  simp [baseColumnWord]

example : omegaGate.arity = 0 := rfl

example : levelWordMatrix ([] : List (LevelOp 0)) = 1 := rfl

example : inverseWord ([] : List (LevelOp 0)) = [] := rfl

example : residueConjugate (bits 1) = bits 1 := by
  ext i
  fin_cases i <;> norm_num [residueConjugate, bits]

example : dyadicValue (fun _ => 0) = 0 := by simp [dyadicValue]

example : coordinateWeight (fun _ => 0) = 0 := by simp [coordinateWeight]

example : vectorNormSq (fun _ : Fin 0 => (0 : ℂ)) = 0 := by simp [vectorNormSq]

example : ([] : List HTLetter) ∈ rowCandidates := by simp [rowCandidates]

example (u : Fin 0 → ℂ) (k : ℕ) : PassTrace k u [] :=
  .done u (fun i => Fin.elim0 i)

example (U : Matrix (Fin 0) (Fin 0) ℂ) (k : ℕ) : MatrixTrace U k [] := .empty U k

example (B n : ℕ) : CompilationTrace B n [] [] := .nil

example (M : Matrix Bool Bool ℂ) (y z : Qubits 1) :
    multiplyControlled 0 M y z = M (y 0) (z 0) := by simp [multiplyControlled]

end QAlgorithms.Papers.Independent.Intakethird100.P85


