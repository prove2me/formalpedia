-- Prove2me | Definitions.Def_QAlgorithms_Defs_ReedSolomonDecoders
-- name    : QAlgorithms_Defs_ReedSolomonDecoders
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:32:30.936681+00:00
-- url     : https://prove2.me/theorems/cda79200-435d-48fe-9cf3-654b6978601f
-- title:
--   ReedSolomonDecoders
-- statement:
--   ReedSolomonDecoders
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ReedSolomonDecoders.lean

import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_Defs_ReedSolomonData
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.ReedSolomon

/-- Public Gaussian-elimination state; 2607.16541 pp.10–11,
2610.02145 pp.18,34. Pivots are selected in increasing column/row order. -/
structure EliminationState (n m : ℕ) (F : Type*) [Field F] where
  matrix : Matrix (Fin n) (Fin m) F
  transform : Matrix (Fin n) (Fin n) F
  pivots : List (Fin m)

/-- One public column pivot, with row scaling and all-row elimination;
2607.16541 pp.10–11, 2610.02145 p.34. -/
def eliminateColumn {F : Type*} [Field F] {n m : ℕ}
    (s : EliminationState n m F) (col : Fin m) : EliminationState n m F :=
  let p := s.pivots.length
  match ((List.finRange n).find? fun row => p ≤ row.val ∧ s.matrix row col ≠ 0) with
  | none => s
  | some row =>
      if hp : p < n then
        let pivot : Fin n := ⟨p,hp⟩
        let permutation := Equiv.swap pivot row
        let A := s.matrix.submatrix permutation id
        let T := s.transform.submatrix permutation id
        let divisor := A pivot col
        let normalizedA := fun j => A pivot j/divisor
        let normalizedT := fun j => T pivot j/divisor
        ⟨Matrix.of (fun i j => if i = pivot then normalizedA j else A i j-A i col*normalizedA j),
          Matrix.of (fun i j => if i = pivot then normalizedT j else T i j-A i col*normalizedT j),
          s.pivots ++ [col]⟩
      else s

/-- Constructed right inverse from fixed-order Gaussian elimination;
2607.16541 pp.10–11. Full-row-rank identity and bit-cost are consequences.
On rank-deficient data unmatched rows are set to zero. -/
def syndromeRepresentatives {F : Type*} [Field F] {n m : ℕ}
    (H : Matrix (Fin n) (Fin m) F) : Matrix (Fin m) (Fin n) F :=
  let reduced := (List.finRange m).foldl eliminateColumn
    (⟨H,1,[]⟩ : EliminationState n m F)
  Matrix.of fun i j =>
    let r := reduced.pivots.idxOf i
    if hr : r < reduced.pivots.length ∧ r < n then reduced.transform ⟨r,hr.2⟩ j else 0

/-- Complete canonical shell list, with no omitted fiber members;
2607.16541 pp.11–12. This is mathematical list semantics; efficient realization
is specified separately and is not granted to finite enumeration. -/
def canonicalShellList {F : Type} [Field F] [Fintype F] {n m : ℕ}
    (E : OPI.publicFieldEncoding F) (H : Matrix (Fin n) (Fin m) F)
    (weights : Finset ℕ) (s : Fin n → F) : List (Fin m → F) :=
  ((Finset.univ.filter fun y : Fin m → F =>
    H.mulVec y = s ∧ hammingNorm y ∈ weights).toList).mergeSort fun y z =>
      decide (List.Lex (· < ·)
        ((List.ofFn fun i => OPI.fieldBits E (y i)).flatten)
        ((List.ofFn fun i => OPI.fieldBits E (z i)).flatten) ∨ y = z)

/-- Public bounded-distance GRS decoder specification;
2610.02145 pp.18,34. Unique output is constrained by the actual scaled code,
and failure is explicit off the decoding promise. -/
def grsUniqueDecode {F : Type*} [Field F] [Fintype F] {m : ℕ}
    (alpha v : Fin m → F) (k radius : ℕ) (received : Fin m → F) : Option (Fin m → F) :=
  let candidates := (Finset.univ : Finset (Fin k → F)).image
    (fun x => fun i => v i*(OPI.coefficientPolynomial x).eval (alpha i))
  let within := candidates.filter fun word => hammingDist received word ≤ radius
  if within.card = 1 then within.toList.head? else none

/-- Total unique syndrome-decoder map, dividing/restoring actual GRS multipliers;
2610.02145 pp.18,34, Lemma 5. Off promise or failed decoding returns zero.
This semantic map is distinct from its priced conventional implementation. -/
def uniqueSyndromeDecoder {F : Type*} [Field F] [Fintype F] {m n : ℕ}
    (alpha : Fin m → F) (distinct : Function.Injective alpha) (_dimensions : n ≤ m) (radius : ℕ)
    (s : Fin n → F) : Fin m → F :=
  let H := (OPI.vandermondeEncoder alpha n).transpose
  let r := (syndromeRepresentatives H).mulVec s
  let nu := dualMultipliers alpha distinct
  let rescaled := fun i => r i/nu i
  match grsUniqueDecode alpha (fun _ => 1) (m-n) radius rescaled with
  | none => 0
  | some word => r-(fun i => nu i*word i)

/-- Concrete deterministic list-decoder bit implementation and fixed padding;
2607.16541 pp.11–12. Completeness and polynomial cost are separate conclusions. -/
structure ListDecoderRealization where
  program : OPI.BitOracleProgram
  publicOnly : OPI.IsPublicPreprocessor program
  pad : ℕ → ℕ

/-- Canonical bit input to the list decoder: public field modulus, dimensions,
active weights, parity matrix and syndrome; 2607.16541 pp.7,11–13. Integers are
binary encoded and field values use fieldBits. No precomputed list or decoder
answer is supplied as free input. -/
def shellListInput {F : Type} [Field F] [Fintype F] {n m : ℕ}
    (E : OPI.publicFieldEncoding F) (H : Matrix (Fin n) (Fin m) F)
    (weights : Finset ℕ) (s : Fin n → F) : Complexity.Str :=
  LocalHamiltonian.encBin E.p ++ LocalHamiltonian.encBin E.e ++
    (List.ofFn fun j : Fin (E.e+1) =>
      LocalHamiltonian.encBin (E.modulus.coeff j.val).val).flatten ++
    LocalHamiltonian.encBin n ++ LocalHamiltonian.encBin m ++
    LocalHamiltonian.encBin weights.card ++
    ((weights.sort (· ≤ ·)).map LocalHamiltonian.encBin).flatten ++
    (List.ofFn fun i => (List.ofFn fun j => OPI.fieldBits E (H i j)).flatten).flatten ++
    (List.ofFn fun i => OPI.fieldBits E (s i)).flatten

/-- Agreement with full canonical list semantics, including duplicate removal and sorting;
2607.16541 pp.11–12. No list-size inequality substitutes for execution. -/
def RealizesShellList {F : Type} [Field F] [Fintype F] {n m : ℕ}
    (P : ListDecoderRealization) (E : OPI.publicFieldEncoding F)
    (H : Matrix (Fin n) (Fin m) F) (weights : Finset ℕ) : Prop :=
  ∀ s,
    let result := OPI.bitProgramExecution P.program (shellListInput E H weights s)
      (fun _ => false) (fun _ => false) (P.pad (m+E.e*Nat.clog 2 E.p))
    result.status = some true ∧ result.output =
      (canonicalShellList E H weights s).flatMap fun y =>
        (List.ofFn fun i => OPI.fieldBits E (y i)).flatten

example {F : Type*} [Field F] {m : ℕ}
    (s : EliminationState 0 m F) (col : Fin m) : eliminateColumn s col = s := by
  simp [eliminateColumn]

end QAlgorithms.ReedSolomon


