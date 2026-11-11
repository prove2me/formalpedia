-- Prove2me | Definitions.Def_EFI1PRS_Uniform_Generator
-- name    : EFI1PRS_Uniform_Generator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T05:00:59.713787+00:00
-- url     : https://prove2.me/theorems/4ac38671-75e0-4177-b6b8-8ebca70d9917
-- title:
--   Coherent pure outputs with all boundary qubits and secret Pauli masks
-- statement:
--   The initial pure vector is the product of all $Lt$ independently keyed coherent source copies. Given fixed public seeds and shifts, each column's exact Clifford circuit acts on its actual row positions. The output wire order lists all retained column wires, then the full complementary list, including every boundary qubit. Public seeds and shifts are included as basis registers.
--
--   For each fixed key $(S,J^t,b,u,v)$ the generated vector is
--
--   $$|\mathrm{Gen}_\lambda\rangle=(I_A\otimes P_{u,v})|\Psi_{S,J^t,b}\rangle.$$
--
--   The formula retains the full preparation workspace and every wire traced in the analysis. Normalization, the mask-average identity, efficient uniform circuit implementation and positive stretch remain proof obligations; none is assumed in a structure field. The product register $A\times D$ is a representation of the same $q+MLt$ output qubits.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, §§5.2–5.3, pp.14–15

import Definitions.Def_EFI1PRS_Uniform_Interfaces

/-! Batra, §§5.2–5.3, pp.14–15. Coherent whole-output construction:
all discarded analysis wires, all boundaries and all public bits are retained. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

def sourceQubits (g : PairPreparation) (sec : ℕ) : ℕ :=
  sourceWidth g sec * copies (sourceWidth g sec) * rows (sourceWidth g sec) sec

def rowShift (g : PairPreparation) (sec : ℕ)
    (J : Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec))) (r : ℕ) : ℕ :=
  bitsInteger (fun j : Fin (shiftBits (sourceWidth g sec)) =>
    bitAt J (r*shiftBits (sourceWidth g sec)+j.val))

def initialSourceVector (g : PairPreparation) (sec : ℕ)
    (b : Qubits (copies (sourceWidth g sec)*rows (sourceWidth g sec) sec)) :
    EuclideanSpace ℂ (Qubits (sourceQubits g sec)) :=
  let M := sourceWidth g sec
  WithLp.toLp 2 fun x => ∏ r : Fin (rows M sec), ∏ c : Fin (copies M),
    sourceVector g sec (bitAt b (r.val*copies M+c.val))
      (fun j => bitAt x (r.val*(M*copies M)+c.val*M+j.val))

def placeOperator {n k : ℕ} (pos : Fin k → ℕ)
    (U : Matrix (Qubits k) (Qubits k) ℂ) : Matrix (Qubits n) (Qubits n) ℂ :=
  fun x y => if ∀ j : Fin n, j.val ∉ Set.range pos → x j = y j then
    U (fun i => bitAt x (pos i)) (fun i => bitAt y (pos i)) else 0

def allColumnUnitary (g : PairPreparation) (sec : ℕ)
    (S : Qubits (windowLength (sourceWidth g sec)*seedLength (rows (sourceWidth g sec) sec) sec))
    (J : Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec))) :
    Matrix (Qubits (sourceQubits g sec)) (Qubits (sourceQubits g sec)) ℂ :=
  let M := sourceWidth g sec
  let t := rows M sec
  let a := seedLength t sec
  ((List.range (windowLength M)).map fun c =>
    placeOperator (fun r : Fin t => r.val*(M*copies M)+rowShift g sec J r.val+c)
      (sampledCircuit t sec (fun j => bitAt S (c*a+j.val))).unitary).reverse.prod

/-- Retained wires in R1,...,RN order, each with ell row wires. -/
def retainedPositions (g : PairPreparation) (sec : ℕ)
    (J : Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec))) : List ℕ :=
  let M := sourceWidth g sec
  (List.range (windowLength M)).flatMap fun c =>
    (List.range (retained M sec)).map fun r => r*(M*copies M)+rowShift g sec J r+c

/-- D1,...,DN in column order, followed by every boundary qubit in original
wire order. This is the source's D=D1...DN B, including all omitted boundaries. -/
def discardedPositions (g : PairPreparation) (sec : ℕ)
    (J : Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec))) : List ℕ :=
  let M := sourceWidth g sec
  let t := rows M sec
  let ell := retained M sec
  let columnDiscards := (List.range (windowLength M)).flatMap fun c =>
    (List.range (t-ell)).map fun r => (r+ell)*(M*copies M)+rowShift g sec J (r+ell)+c
  let windowPositions := (List.range (windowLength M)).flatMap fun c =>
    (List.range t).map fun r => r*(M*copies M)+rowShift g sec J r+c
  columnDiscards ++ ((List.range (sourceQubits g sec)).filter fun j => j ∉ windowPositions)

def unmaskedVector (g : PairPreparation) (sec : ℕ)
    (S : Qubits (windowLength (sourceWidth g sec)*seedLength (rows (sourceWidth g sec) sec) sec))
    (J : Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec)))
    (b : Qubits (copies (sourceWidth g sec)*rows (sourceWidth g sec) sec)) :
    EuclideanSpace ℂ (Qubits (retainedWidth g sec) × Qubits (maskedWidth g sec)) :=
  let M := sourceWidth g sec
  let N := windowLength M
  let a := seedLength (rows M sec) sec
  let v := act (allColumnUnitary g sec S J) (initialSourceVector g sec b)
  WithLp.toLp 2 fun x =>
    if (∀ j : Fin (N*a), bitAt x.1 j.val = S j) ∧
      (∀ j : Fin (rows M sec*shiftBits M), bitAt x.1 (N*a+j.val) = J j)
    then v (fun old =>
      if old.val ∈ retainedPositions g sec J then
        bitAt x.1 (publicLength g sec + (retainedPositions g sec J).idxOf old.val)
      else bitAt x.2 ((discardedPositions g sec J).idxOf old.val))
    else 0

def generatedVector (g : PairPreparation) (sec : ℕ)
    (S : Qubits (windowLength (sourceWidth g sec)*seedLength (rows (sourceWidth g sec) sec) sec))
    (J : Qubits (rows (sourceWidth g sec) sec * shiftBits (sourceWidth g sec)))
    (b : Qubits (copies (sourceWidth g sec)*rows (sourceWidth g sec) sec))
    (u v : Qubits (maskedWidth g sec)) :
    EuclideanSpace ℂ (Qubits (retainedWidth g sec) × Qubits (maskedWidth g sec)) :=
  act (Matrix.kronecker (1 : Matrix (Qubits (retainedWidth g sec)) (Qubits (retainedWidth g sec)) ℂ)
    (pauliMask u v)) (unmaskedVector g sec S J b)

end EFI1PRS.Uniform


