-- Prove2me | Definitions.Def_QuarticGap_IsCoherentAccess
-- name    : QuarticGap_IsCoherentAccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:34.371839+00:00
-- url     : https://prove2.me/theorems/29d50642-125e-4ba5-917d-810d2f148995
-- title:
--   Coherent access to a matrix, oracle-circuit output law, $O_f$ and its simulation
-- statement:
--   For a nonzero real matrix $A$ with entries in a fixed binary encoding, a choice of the **quantum input operations** is five unitaries:
--
--   1. the reversible entry query $|i,j,z\rangle \mapsto |i,j,z \oplus A_{ij}\rangle$;
--   2. row preparation $|i\rangle|0\rangle \mapsto |i\rangle \sum_j (A_{ij}/\|A_{i,*}\|)|j\rangle$ and column preparation $|j\rangle|0\rangle \mapsto |j\rangle \sum_i (A_{ij}/\|A_{*,j}\|)|i\rangle$, which fix $|i\rangle|0\rangle$ or $|j\rangle|0\rangle$ for a zero row or column;
--   3. norm preparation $|0\rangle \mapsto \sum_i (\|A_{i,*}\|/\|A\|_F)|i\rangle$, and its column analogue.
--
--   Row, column and norm preparation are specified only on these states, and their action elsewhere is arbitrary. Each unitary, its inverse and its controlled version count as one query. The item also defines the output law of an oracle circuit started in $|0\rangle$ and measured at the end, the total query count, the bit oracle $O_f|\sigma,c\rangle = |\sigma, c \oplus (1 - f(\sigma))/2\rangle$, the controlled phase query $|b\rangle|\sigma\rangle \mapsto f(\sigma)^b|b\rangle|\sigma\rangle$, and fixed circuits that implement a tuple of operations with one black box, with ancillas that start and end in $|0\rangle$.
--
--   This is the quantum model of the mission. An algorithm must succeed for every choice of the unspecified action, so this predicate appears as a premise of its lower bound and as a universally quantified condition in its upper bound.
--
--   **Formalization Note** The encoding is a table of bit strings, fixed by each statement. Matrices are indexed by qubit registers; a matrix of another size is held on $\lceil\log N\rceil$ wires with zero rows and columns added. Inverses and controlled versions are supplied by the published `OracleStep.query`, and `queryCount` counts each as one call.
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Definition 2.2, pp.15–16; Definition 2.3, p.16; §2.5, p.18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuarticGap_sqRespond

open QAlgorithms

namespace QuarticGap

/-- The string `0^n`. -/
def zeros (n : ℕ) : Qubits n := fun _ => false

/-- The register sizes of the five quantum input operations of a matrix on `d₁` row wires and `d₂`
column wires with entries in `w` bits: reversible entry query on row, column and output registers;
row preparation; column preparation; row-norm preparation; column-norm preparation
(arXiv:2610.42069, Definition 2.2, pp.15–16). -/
def coherentArity (d₁ d₂ w : ℕ) : Fin 5 → ℕ :=
  ![d₁ + d₂ + w, d₁ + d₂, d₂ + d₁, d₁, d₂]

/-- The image `|i⟩ ∑_j (A_ij/∥A_{i,∗}∥)|j⟩` of `|i⟩|0⟩` under row preparation, and `|i⟩|0⟩` itself for
a zero row (arXiv:2610.42069, Definition 2.2, clause 2, p.16). -/
noncomputable def rowPrepState {d₁ d₂ : ℕ} (A : Matrix (Qubits d₁) (Qubits d₂) ℝ) (i : Qubits d₁) :
    EuclideanSpace ℂ (Qubits (d₁ + d₂)) :=
  if rowNorm A i = 0 then ket (Fin.append i (zeros d₂))
  else ∑ j, ((A i j / rowNorm A i : ℝ) : ℂ) • ket (Fin.append i j)

/-- The image `|j⟩ ∑_i (A_ij/∥A_{∗,j}∥)|i⟩` of `|j⟩|0⟩` under column preparation, and `|j⟩|0⟩` itself
for a zero column (arXiv:2610.42069, Definition 2.2, clause 2, p.16). -/
noncomputable def colPrepState {d₁ d₂ : ℕ} (A : Matrix (Qubits d₁) (Qubits d₂) ℝ) (j : Qubits d₂) :
    EuclideanSpace ℂ (Qubits (d₂ + d₁)) :=
  if colNorm A j = 0 then ket (Fin.append j (zeros d₁))
  else ∑ i, ((A i j / colNorm A j : ℝ) : ℂ) • ket (Fin.append j i)

/-- `orc` is a choice of the quantum input operations of `A` (arXiv:2610.42069, Definition 2.2,
pp.15–16): all five are unitary; `orc 0` is the reversible entry query `|i, j, z⟩ ↦ |i, j, z ⊕ e i j⟩`
on every basis state; `orc 1`, `orc 2` are row and column preparation on `|i⟩|0⟩`, `|j⟩|0⟩`; `orc 3`,
`orc 4` map `|0⟩` to `∑_i (∥A_{i,∗}∥/∥A∥_F)|i⟩`, `∑_j (∥A_{∗,j}∥/∥A∥_F)|j⟩`. Nothing else is
constrained, matching "their action on other states is arbitrary".

**Formalization Note** `e i j` is the binary encoding of the entry `A i j`, given as a table so that
each statement fixes its encoding. Definition 2.2 is for a nonzero matrix; for `A = 0` the norm
preparation has no unitary, so a statement about a family that can vanish must exclude it. A matrix
of size `N₁ × N₂` that is not a power of two is held on `⌈log N₁⌉`, `⌈log N₂⌉` wires with zero rows
and columns added. Inverses and controlled versions need no separate oracle: the published
`OracleStep.query` supplies them and `queryCount` counts each as one call, as the source does. -/
def IsCoherentAccess {d₁ d₂ w : ℕ} (A : Matrix (Qubits d₁) (Qubits d₂) ℝ)
    (e : Qubits d₁ → Qubits d₂ → Qubits w)
    (orc : (k : Fin 5) → Matrix (Qubits (coherentArity d₁ d₂ w k))
      (Qubits (coherentArity d₁ d₂ w k)) ℂ) : Prop :=
  (∀ k, orc k ∈ Matrix.unitaryGroup (Qubits (coherentArity d₁ d₂ w k)) ℂ) ∧
  (∀ i j z, act (orc 0 : Matrix (Qubits (d₁ + d₂ + w)) (Qubits (d₁ + d₂ + w)) ℂ)
      (ket (Fin.append (Fin.append i j) z)) = ket (Fin.append (Fin.append i j) (z + e i j))) ∧
  (∀ i, act (orc 1 : Matrix (Qubits (d₁ + d₂)) (Qubits (d₁ + d₂)) ℂ)
      (ket (Fin.append i (zeros d₂))) = rowPrepState A i) ∧
  (∀ j, act (orc 2 : Matrix (Qubits (d₂ + d₁)) (Qubits (d₂ + d₁)) ℂ)
      (ket (Fin.append j (zeros d₁))) = colPrepState A j) ∧
  act (orc 3 : Matrix (Qubits d₁) (Qubits d₁) ℂ) (ket (zeros d₁)) =
      ∑ i, ((rowNorm A i / frobR A : ℝ) : ℂ) • ket i ∧
  act (orc 4 : Matrix (Qubits d₂) (Qubits d₂) ℂ) (ket (zeros d₂)) =
      ∑ j, ((colNorm A j / frobR A : ℝ) : ℂ) • ket j

/-- Every unitary gate of every arity, the gate set of the quantum lower bounds. -/
def UnitaryGates : Set Gate := {g | g.IsUnitary}

/-- Total number of oracle calls of a circuit, over all oracles and all variants (plain, inverse,
controlled). -/
def totalQueries {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {N : ℕ} (c : OracleCircuit S a N) : ℕ :=
  ∑ k, c.queryCount k

/-- Output law of a quantum algorithm: run the circuit on `|0^N⟩`, measure all wires in the
computational basis, and output `out` of the outcome (arXiv:2610.42069, Definition 2.3, p.16). -/
noncomputable def qOut {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {N : ℕ} {Y : Type*} [DecidableEq Y]
    (c : OracleCircuit S a N) (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (out : Qubits N → Y) (j : Y) : ℝ :=
  probEvent (act (c.unitary orc) (zeroKet N)) (fun z => out z = j)

/-- The bit oracle `|σ, c⟩ ↦ |σ, c ⊕ g(σ)⟩` of a function `g : {0,1}^m → {0,1}`, on `m + 1` wires with
the target last. For a Boolean function `f` the source's `O_f` of §2.5, p.18 is `bitOracle (signBit f)`;
for a string `s` it is the bit oracle of `s` (arXiv:2610.42069, Lemma 2.10, p.20). -/
def bitOracle {m : ℕ} (g : Qubits m → Bool) : Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
  Matrix.of fun y x =>
    if y = Fin.snoc (α := fun _ => Bool) (Fin.init (α := fun _ => Bool) x)
        (xor (x (Fin.last m)) (g (Fin.init (α := fun _ => Bool) x))) then 1 else 0

/-- The bit `(1 − f(σ))/2` of a sign `f(σ)`: `true` exactly when `f(σ) = −1`
(arXiv:2610.42069, §2.5, p.18). -/
def signBit {m : ℕ} (f : Qubits m → ℤˣ) (σ : Qubits m) : Bool :=
  decide (f σ = -1)

/-- The controlled phase query `|b⟩|σ⟩ ↦ f(σ)^b |b⟩|σ⟩` (arXiv:2610.42069, §2.5, p.18), with `b` on
wire `0`. -/
noncomputable def phaseOracle {m : ℕ} (f : Qubits m → ℤˣ) :
    Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
  Matrix.diagonal fun x => if x 0 then ((sgn (f (Fin.tail (α := fun _ => Bool) x)) : ℝ) : ℂ) else 1

/-- `U` on `a + N` wires implements `V` on the first `a` wires with `N` ancillas that start and end
in `|0⟩`: `U |x⟩|0⟩ = (V |x⟩)|0⟩` for every basis state `x`. -/
def ImplementsWithAncilla {a N : ℕ} (U : Matrix (Qubits (a + N)) (Qubits (a + N)) ℂ)
    (V : Matrix (Qubits a) (Qubits a) ℂ) : Prop :=
  ∀ x, act U (ket (Fin.append x (zeros N))) = ∑ y, V y x • ket (Fin.append y (zeros N))

/-- Fixed circuits with one black box on `b` wires that implement a tuple of operations with arities
`a`: for each operation, a circuit for it, one for its inverse, and one for its controlled version
(control on the wire just after the operation's wires), each with `N` ancillas. All gates are fixed
before the black box is chosen. -/
structure AccessSim {r : ℕ} (a : Fin r → ℕ) (b N : ℕ) where
  /-- Circuit for the operation. -/
  fwd : (k : Fin r) → OracleCircuit UnitaryGates (fun _ : Fin 1 => b) (a k + N)
  /-- Circuit for its inverse. -/
  inv : (k : Fin r) → OracleCircuit UnitaryGates (fun _ : Fin 1 => b) (a k + N)
  /-- Circuit for its controlled version. -/
  ctl : (k : Fin r) → OracleCircuit UnitaryGates (fun _ : Fin 1 => b) (a k + 1 + N)

/-- Every circuit of the simulation makes at most `C` calls to the black box. -/
def AccessSim.CallsAtMost {r : ℕ} {a : Fin r → ℕ} {b N : ℕ} (sim : AccessSim a b N) (C : ℕ) : Prop :=
  ∀ k, (sim.fwd k).queryCount 0 ≤ C ∧ (sim.inv k).queryCount 0 ≤ C ∧ (sim.ctl k).queryCount 0 ≤ C

/-- With the black box `O`, the simulation implements the tuple `orc`, its inverses and its
controlled versions. -/
def AccessSim.Realizes {r : ℕ} {a : Fin r → ℕ} {b N : ℕ} (sim : AccessSim a b N)
    (O : Matrix (Qubits b) (Qubits b) ℂ)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) : Prop :=
  ∀ k, ImplementsWithAncilla ((sim.fwd k).unitary fun _ => O) (orc k) ∧
    ImplementsWithAncilla ((sim.inv k).unitary fun _ => O) (star (orc k)) ∧
    ImplementsWithAncilla ((sim.ctl k).unitary fun _ => O) (controlledQubits (orc k))

/-- The search string of an input of Lemma 2.10 (arXiv:2610.42069, p.20): `s = 0` for `A(∅)` (`none`),
and the indicator vector of `a` for `A(a)` (`some a`). Positions are the elements of a set `marks`
of strings. -/
def searchString {d : ℕ} {marks : Finset (Qubits d)} : Option marks → Qubits d → Bool
  | none => fun _ => false
  | some a => fun x => decide (x = a)

end QuarticGap


