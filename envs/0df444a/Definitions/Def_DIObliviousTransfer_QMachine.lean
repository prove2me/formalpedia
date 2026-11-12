-- Prove2me | Definitions.Def_DIObliviousTransfer_QMachine
-- name    : DIObliviousTransfer_QMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T09:04:07.8607+00:00
-- url     : https://prove2.me/theorems/53d4864f-9d7e-4c8b-bb90-116c23176022
-- title:
--   Nonuniform QPT machines and tests
-- statement:
--   A **quantum machine** has a port of $P$ qubits and $w$ work qubits. Each activation does three things:
--   1. it loads its classical input, self-delimitingly encoded, into its first input wires;
--   2. it applies a circuit of unitary gates on at most two qubits and single-wire resets to $|0\rangle$;
--   3. it measures its first output wires and decodes the classical output.
--
--   Gate entries are arbitrary, so families are nonuniform. After its declared number of activations a machine is inert. A family indexed by $\lambda$ is **QPT** when its qubits, input and output wires, activations and circuit sizes are bounded by one polynomial. Quantum advice needs no separate field: it is part of the arbitrary initial state of the machine's registers.
--
--   A **test** is a one-activation machine on the compared quantum state and ancillas; it receives the classical part as input and outputs one bit.
--
--   **Formalization Note** This is decision D3. Gates come from the published `QAlgorithms` circuit layer.
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), §1.1, p.2; Definition 4 (ii), p.17; Definition 5, p.18

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_DIObliviousTransfer_WinStrat

namespace DIObliviousTransfer

open Matrix QAlgorithms
open scoped Kronecker ComplexOrder

/-!
Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held version, sha256 8334c039…), §1.1 (p.2), §2.4
(Definition 4 (ii), p.17) and Definition 5 (ii), p.18: nonuniform QPT machines and tests.

"We assume qOWFs and a possibly nonuniform QPT adversary with polynomial-size quantum advice"
(p.2); "Active instruments are nonuniform QPT on polynomial-size registers" (Def. 4 (ii));
"All simulators are QPT, with a polynomial bound on every branch" (p.17).

**Formalization Note** (decisions D2, D3). A machine has a port of `P` qubits (for quantum
messages in device windows) and `w` work qubits. Each activation loads its classical input, in the
self-delimiting encoding `packOne`, into the first `nIn` work wires (the old content is
discarded), applies a circuit of unitary gates on at most two qubits (the gate set `smallGates`
over the published `QAlgorithms.Circuit` layer, arbitrary complex entries: nonuniform) and resets
of single wires to `|0⟩`, and measures the first `nOut` work wires in the computational basis; the
outcome is decoded with `unpack` into its classical output. Classical control is part of the
circuit (classically controlled gates are unitary), so a machine has no unbounded classical
controller. After `acts` activations a machine is inert (identity, empty output). A family indexed
by `λ` is QPT when its qubits, input and output wires, activations and circuit sizes are bounded
by one polynomial in `λ`. Quantum advice needs no separate field: it is part of the arbitrary
initial state of the machine's registers (decision D3).
-/

/-- Unitary gates on at most two qubits. -/
def smallGates : Set Gate := {g | g.arity ≤ 2 ∧ g.IsUnitary}

/-- An elementary operation: a gate of `smallGates`, or a reset of one wire to `|0⟩`. -/
inductive ElemOp (n : ℕ) where
  | gate (g : GateApp smallGates n)
  | reset (i : Fin n)

/-- The Kraus operators of an elementary operation. -/
def ElemOp.kraus {n : ℕ} : ElemOp n → List (Matrix (Qubits n) (Qubits n) ℂ)
  | .gate g => [embedOp g.gate.mat g.wires]
  | .reset i => [false, true].map fun b =>
      Matrix.of fun out inp => if inp i = b ∧ out = Function.update inp i false then 1 else 0

/-- The Kraus operators of a sequence of operations (first operation rightmost). -/
def krausSeq {n : ℕ} (ops : List (ElemOp n)) : List (Matrix (Qubits n) (Qubits n) ℂ) :=
  ops.foldl (fun acc op => (op.kraus).flatMap fun K => acc.map fun A => K * A) [1]

/-- `Qubits (a + b) ≃ Qubits a × Qubits b` (first `a` wires, then `b`). -/
def qsplit (a b : ℕ) : Qubits (a + b) ≃ Qubits a × Qubits b where
  toFun x := (fun i => x (Fin.castAdd b i), fun j => x (Fin.natAdd a j))
  invFun p := Fin.append p.1 p.2
  left_inv := by
    intro x; funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  right_inv := by
    intro p; ext i <;> simp

/-- A quantum machine with a port of `P` qubits and `w` work qubits. -/
structure QMachine (P w : ℕ) where
  nIn : ℕ
  nOut : ℕ
  acts : ℕ
  circ : ℕ → List (ElemOp (P + w))

namespace QMachine

variable {P w : ℕ} (M : QMachine P w)

/-- Work wire `j` as a wire of the whole register. -/
def workWire (j : Fin w) : Fin (P + w) := Fin.natAdd P j

/-- The loading Kraus operator for old input-wire content `z` and classical input `x`. -/
def loadKraus (x : Bits) (z : Fin (min M.nIn w) → Bool) :
    Matrix (Qubits (P + w)) (Qubits (P + w)) ℂ :=
  Matrix.of fun out inp =>
    if (∀ j : Fin (min M.nIn w), inp (workWire (Fin.castLE (min_le_right _ _) j)) = z j) ∧
        (∀ j : Fin (min M.nIn w), out (workWire (Fin.castLE (min_le_right _ _) j)) =
          (packOne x).getD j false) ∧
        (∀ i : Fin (P + w), (∀ j : Fin (min M.nIn w),
          i ≠ workWire (Fin.castLE (min_le_right _ _) j)) → out i = inp i)
    then 1 else 0

/-- The projector of output outcome `o` on the first `nOut` work wires. -/
def outProj (o : Fin (min M.nOut w) → Bool) : Matrix (Qubits (P + w)) (Qubits (P + w)) ℂ :=
  Matrix.of fun out inp =>
    if out = inp ∧ ∀ j : Fin (min M.nOut w), inp (workWire (Fin.castLE (min_le_right _ _) j)) = o j
    then 1 else 0

/-- The classical output of a measured outcome. -/
def decodeOut (o : Fin (min M.nOut w) → Bool) : Bits := (unpack (List.ofFn o)).headD []

/-- Activation `i` on classical input `x`, as an instrument on `Qubits P × Qubits w` with
outcomes the classical outputs. -/
noncomputable def act (i : ℕ) (x : Bits) : Instr (Qubits P × Qubits w) Bits := by
  classical
  exact if i < M.acts then
    { outs := Finset.univ.image M.decodeOut
      kraus := fun b =>
        ((Finset.univ.filter fun o => M.decodeOut o = b).toList.flatMap fun o =>
          (krausSeq (M.circ i)).flatMap fun K =>
            (Finset.univ.toList).map fun z =>
              Matrix.reindex (qsplit P w) (qsplit P w) (M.outProj o * K * M.loadKraus x z)) }
  else { outs := {[]}, kraus := fun b => if b = [] then [1] else [] }

end QMachine

/-- A QPT family of machines (decision D3): all sizes bounded by one polynomial in `λ`. -/
def IsQPTFam {P w : ℕ → ℕ} (M : (lam : ℕ) → QMachine (P lam) (w lam)) : Prop :=
  ∃ p : ℕ → ℕ, PolyBound p ∧ ∀ lam,
    P lam + w lam + (M lam).nIn + (M lam).nOut + (M lam).acts ≤ p lam ∧
    ∀ i, ((M lam).circ i).length ≤ p lam

/-- The probability that the test machine `D` (one activation, `a` ancillas in `|0⟩`) outputs
the bit `1` on classical input `x` and the quantum state `σ` on its first `n` work wires. -/
noncomputable def acceptProb {n a : ℕ} (D : QMachine 0 (n + a)) (x : Bits)
    (σ : Matrix (Qubits n) (Qubits n) ℂ) : ℝ := by
  classical
  let σa : Matrix (Qubits 0 × Qubits (n + a)) (Qubits 0 × Qubits (n + a)) ℂ :=
    Matrix.of fun i j =>
      σ ((qsplit n a i.2).1) ((qsplit n a j.2).1) *
        (if (qsplit n a i.2).2 = (fun _ => false) ∧ (qsplit n a j.2).2 = (fun _ => false)
          then 1 else 0)
  exact ∑ b ∈ (D.act 0 x).outs, if b.headD false = true then ((D.act 0 x).apply b σa).trace.re else 0

end DIObliviousTransfer


