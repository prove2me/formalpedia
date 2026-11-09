-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Main_Compiler
-- name    : QMAPerfectCompleteness_Main_Compiler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:49.24357+00:00
-- url     : https://prove2.me/theorems/20fe066e-b706-410e-bdc8-664acec1bf38
-- title:
--   Circuits for $U_{z,a,b}$: wire layout, clean workspace, and the codes of the compiler
-- statement:
--   This is the vocabulary for the circuit clause of Lemma 3.6. A circuit for $U_{z,a,b}$ acts on the wires of the index register, the clock register (with $\ell+1=2^c$, so $c$ wires), the verifier's proof and ancilla wires, the flag, and $w$ workspace wires, in this order. A register holding an integer stores bit $i$ on its $i$-th wire.
--
--   A circuit with unitary $C$ **implements** a matrix $U$ on index, clock, verifier wires and flag with clean workspace if, for every state $\psi$ of those wires,
--
--   $$
--   C\,(|\psi\rangle\otimes|0\rangle_{\mathrm{work}})=(U|\psi\rangle)\otimes|0\rangle_{\mathrm{work}}.
--   $$
--
--   The sublist $V$ is the gate list of the verifier moved to its wires in the block register. The sublist $V^\dagger$ is the reversed list; every gate of $\mathcal G_2$ is its own inverse. The input of the compiler is the code of $V$ followed by the bits of $z$ and the $k$-bit expansions of $a$ and $b$, and its output is the number of wires and the gate list.
--
--   **Formalization Note** The relation `Implements` is written on basis states: for a basis state $x$ with clean workspace, the entry $\langle y|C|x\rangle$ is the corresponding entry of $U$ when the workspace of $y$ is clean, and zero otherwise. This is the matrix form of the display above.
--   The surrounding gate lists and workspace count have a separate self-delimiting code. Their generator receives only register sizes, the output-wire address, the index size and the certificate; it receives no gates of $V$. This fixes the surrounding circuit for all verifiers with the same layout and index size.
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), Lemma 3.6 and its proof, p. 10

import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding

open Matrix

/-!
# Circuits on the block register: wire layout, clean workspace and codes

Sabee Grewal, Dorian Rudolph, *QMA has perfect completeness*, STOC 2027 submission #490
(October 2026), Lemma 3.6 (p. 10).

The vocabulary for the circuit clause of Lemma 3.6. A circuit acts on `k` index wires, `c` clock
wires, the wires of `V`, one flag wire and `w` workspace wires, in this order. Registers holding an
integer store bit `i` on their `i`-th wire.
-/

namespace QMAPerfectCompleteness.Main

open QAlgorithms.Complexity (Str encNat)

namespace BlockCircuit

variable (V : Verifier gatesG2)

/-- The number of clock wires. -/
abbrev clockWires : ℕ := clockQubits V.proofQubits

/-- The number of wires of the block register before the workspace. -/
abbrev bodyWires : ℕ :=
  indexQubits V + clockWires V + (V.proofQubits + V.ancillaQubits) + 1

variable {V}

/-- The `i`-th wire of the index register. -/
def indexWire {w : ℕ} (i : Fin (indexQubits V)) : Fin (bodyWires V + w) :=
  ⟨i, by have := i.2; simp only [bodyWires]; omega⟩

/-- The `i`-th wire of the clock register. -/
def clockWire {w : ℕ} (i : Fin (clockWires V)) : Fin (bodyWires V + w) :=
  ⟨indexQubits V + i, by have := i.2; simp only [bodyWires]; omega⟩

/-- The `i`-th wire of the verifier's own register. -/
def verifierWire {w : ℕ} (i : Fin (V.proofQubits + V.ancillaQubits)) : Fin (bodyWires V + w) :=
  ⟨indexQubits V + clockWires V + i, by have := i.2; simp only [bodyWires]; omega⟩

/-- The flag wire. -/
def flagWire {w : ℕ} : Fin (bodyWires V + w) :=
  ⟨indexQubits V + clockWires V + (V.proofQubits + V.ancillaQubits), by
    simp only [bodyWires]; omega⟩

/-- The `i`-th workspace wire. -/
def workspaceWire {w : ℕ} (i : Fin w) : Fin (bodyWires V + w) := Fin.natAdd _ i

/-- The value of the bits on a list of wires, bit `i` on the `i`-th wire. -/
def bitsValue {n r : ℕ} (x : Basis n) (wire : Fin r → Fin n) : ℕ :=
  ∑ i : Fin r, if x (wire i) then 2 ^ (i : ℕ) else 0

/-- Read a basis state of the wires as a basis state of `J`, clock, verifier register and flag.
Since `ℓ + 1 = 2^c` the reductions modulo `ℓ + 1` and `2^k` do not change the values. -/
def decode {w : ℕ} (x : Basis (bodyWires V + w)) : V.BlockReg (indexQubits V) :=
  (Fin.ofNat _ (bitsValue x indexWire),
    Fin.ofNat _ (bitsValue x clockWire), fun i => x (verifierWire i), x flagWire)

/-- All workspace wires are zero. -/
def WorkspaceClean {w : ℕ} (x : Basis (bodyWires V + w)) : Prop :=
  ∀ i : Fin w, x (workspaceWire i) = false

instance {w : ℕ} (x : Basis (bodyWires V + w)) : Decidable (WorkspaceClean x) :=
  inferInstanceAs (Decidable (∀ i : Fin w, x (workspaceWire i) = false))

/-- The circuit `C` implements `U` with workspace that starts and ends in `|0⟩`:
`C (|ψ⟩ ⊗ |0⟩_work) = (U|ψ⟩) ⊗ |0⟩_work` for every state `ψ`, written on basis states. -/
def Implements {w : ℕ} (C : Matrix (Basis (bodyWires V + w)) (Basis (bodyWires V + w)) ℂ)
    (U : Matrix (V.BlockReg (indexQubits V)) (V.BlockReg (indexQubits V)) ℂ) : Prop :=
  ∀ y x, WorkspaceClean x →
    C y x = if WorkspaceClean y then U (decode y) (decode x) else 0

/-- The wires of `V` inside the block register, as an injection. -/
def verifierEmbedding (w : ℕ) :
    Fin (V.proofQubits + V.ancillaQubits) ↪ Fin (bodyWires V + w) :=
  ⟨verifierWire, fun i j h => by
    simp only [verifierWire, Fin.mk.injEq] at h
    exact Fin.ext (by omega)⟩

/-- `V`'s gate list, on its wires of the block register. -/
noncomputable def forwardGates (V : Verifier gatesG2) (w : ℕ) : List (Instr gatesG2 (bodyWires V + w)) :=
  V.gates.map (Instr.mapWires (verifierEmbedding w))

/-- `V†` as the reversed gate list of `V`: every gate of `𝒢₂` is its own inverse (p. 10). -/
noncomputable def backwardGates (V : Verifier gatesG2) (w : ℕ) : List (Instr gatesG2 (bodyWires V + w)) :=
  (forwardGates V w).reverse

/-- The code of the input of the compiler: the code of `V`, the `m` bits of `z`, and `a`, `b` as
`k`-bit strings. -/
noncomputable def encodeInput (V : Verifier gatesG2) (z : V.Proof) (a b : ℕ) : Str :=
  V.encode ++ List.ofFn z ++
    List.ofFn (fun i : Fin (indexQubits V) => a.testBit i) ++
    List.ofFn (fun i : Fin (indexQubits V) => b.testBit i)

/-- The data determining the circuit surrounding the two uses of `V` and `V†`.
This contains register sizes, the output-wire address and the certificate, but no gate of `V`.
In particular, verifiers with the same layout and `H ⊗ H` count must use the same surrounding
circuit for a fixed certificate. -/
noncomputable def encodeLayout (V : Verifier gatesG2) (z : V.Proof) (a b : ℕ) : Str :=
  encNat V.proofQubits ++ encNat V.ancillaQubits ++ encNat V.output.val ++
    encNat (indexQubits V) ++ List.ofFn z ++
    List.ofFn (fun i : Fin (indexQubits V) => a.testBit i) ++
    List.ofFn (fun i : Fin (indexQubits V) => b.testBit i)

/-- A self-delimiting description of the extra workspace and the three surrounding gate lists.
Together with `encodeLayout`, equality of these codes fixes the surrounding circuit independently
of the verifier's gate list. -/
noncomputable def encodeScaffold (V : Verifier gatesG2) (w : ℕ)
    (pre mid post : List (Instr gatesG2 (bodyWires V + w))) : Str :=
  encNat w ++ encodeGates pre ++ encodeGates mid ++ encodeGates post

/-- The code of the output of the compiler: the number of wires and the gate list. -/
noncomputable def encodeCircuit {n : ℕ} (gs : List (Instr gatesG2 n)) : Str :=
  encNat n ++ encodeGates gs

end BlockCircuit

end QMAPerfectCompleteness.Main


