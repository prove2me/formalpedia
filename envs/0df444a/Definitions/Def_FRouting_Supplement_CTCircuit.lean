-- Prove2me | Definitions.Def_FRouting_Supplement_CTCircuit
-- name    : FRouting_Supplement_CTCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:18:24.388831+00:00
-- url     : https://prove2.me/theorems/000eaa93-d375-4034-81a1-caf14ab78314
-- title:
--   Clifford+T circuits, their magic count and their description
-- statement:
--   A **Clifford+T circuit** on qubits is a list of gates from $\{H, S, \mathrm{CNOT}, T\}$, with
--   $$H=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad S=\begin{pmatrix}1&0\\0&i\end{pmatrix},\qquad T=\begin{pmatrix}1&0\\0&e^{i\pi/4}\end{pmatrix},$$
--   acting on $\mathrm{in}$ input wires followed by some ancilla wires initialized to $|0\rangle$; a list of distinct wires is kept as the output and the others are traced out. The **size** of the circuit is its number of gates, its **width** its number of wires, and its **magic count** the number of $T$ gates; $H$, $S$ and $\mathrm{CNOT}$ are Clifford gates and cost nothing in the magic count.
--
--   The circuit's unitary, channel and output state (the kept wires after running on $|0\cdots0\rangle$) are those of the published qubit circuit obtained by writing $H$ as the Fourier gate $F_2$, $T$ as $T_2$, $\mathrm{CNOT}$ as $\mathrm{SUM}_2$ and $S$ as $T_2T_2$ (an identity of unitaries, $S=T^2$). The **description** of a circuit lists the widths in unary, the kept wires, the number of gates and the gates, each wire index in self-delimiting binary.
--
--   These are the circuits of the adversaries in Definition 6.1 and the inputs $W_\rho, W_\sigma$ of Theorem 6.3.
--
--   **Formalization Note** The published qubit gate type has no $S$, so counting its $T_2$ gates would charge every $S$ as two magic gates; the magic count is taken on the Clifford+T gate list itself.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 6.1 and the setup of §6.1, p.23

import Definitions.Def_FRouting_encCircuit

set_option autoImplicit false

open Matrix

namespace FRouting.Supplement

open QAlgorithms.Complexity

/-- **A Clifford+T gate on `W` qubit wires**: Hadamard `H`, phase `S = diag(1, i)` and `T = diag(1, e^{iπ/4})`
on one wire, and `CNOT` on two distinct wires. Renard, *Computational Bounds for f-Routing*,
arXiv:2609.40278 (held copy, sha256 4a327f29…), §6.1, p.23 (Definition 6.1) speaks of "Clifford+T
circuits" and their "magic gates" without listing the gates; this is the standard set `{H, S, CNOT, T}`,
in which only `T` is a magic gate.

**Formalization Note** The published qubit gates `FRouting.Gate 2` have no `S`; this type has it, so that
`S` is free in the magic count. Wire indices are `Fin W`. -/
inductive CTGate (W : ℕ) where
  | h (w : Fin W)
  | s (w : Fin W)
  | t (w : Fin W)
  | cnot (c u : Fin W) (hcu : c ≠ u)

/-- A Clifford+T gate as published qubit gates: `H ↦ F₂`, `T ↦ T₂`, `CNOT ↦ SUM₂`, and `S ↦ T₂, T₂`
(`S = T²`, an identity of unitaries; the count of magic gates is taken on the Clifford+T gate list,
never on this compilation). -/
def CTGate.compile {W : ℕ} : CTGate W → List (Gate 2 W)
  | .h w => [.fourier w]
  | .s w => [.tee w, .tee w]
  | .t w => [.tee w]
  | .cnot c u hcu => [.sum c u hcu]

/-- Is the gate a magic (`T`) gate. -/
def CTGate.isMagic {W : ℕ} : CTGate W → Bool
  | .t _ => true
  | _ => false

/-- **A Clifford+T circuit** from `inW` input qubits to `outW` kept qubits (Definition 6.1 and the setup
of §6.1, p.23): the input wires come first, then `ancillas` wires in `|0⟩`; the gates (first applied
first) act on all of them; the wires in `kept` form the output and the others are traced out. Its size
is the number of gates, its width the number of wires, and its magic count the number of `T` gates.

**Formalization Note** The same shape as the published `FRouting.Circuit` at `d = 2`; its channel and
output state are those of `toCircuit`, the published circuit obtained by compiling each gate. -/
structure CTCircuit (inW outW : ℕ) where
  /-- The number of ancilla wires, each starting in `|0⟩`. -/
  ancillas : ℕ
  /-- The gates, first applied first. -/
  gates : List (CTGate (inW + ancillas))
  /-- The output wires. -/
  kept : Fin outW → Fin (inW + ancillas)
  kept_inj : Function.Injective kept

namespace CTCircuit

variable {inW outW : ℕ} (C : CTCircuit inW outW)

/-- The number of wires. -/
def width : ℕ := inW + C.ancillas

/-- The number of gates (each Clifford+T gate counts once). -/
def size : ℕ := C.gates.length

/-- The number of magic (`T`) gates. -/
def magicCount : ℕ := C.gates.countP fun g => g.isMagic

/-- The published qubit circuit with the same wires and kept wires and the compiled gates; it has the
same unitary, channel and output state. -/
def toCircuit : Circuit 2 inW outW where
  d_pos := by norm_num
  ancillas := C.ancillas
  gates := C.gates.flatMap CTGate.compile
  kept := C.kept
  kept_inj := C.kept_inj

/-- The description of one Clifford+T gate: a tag, then its wires in binary. -/
def encCTGate {W : ℕ} : CTGate W → Str
  | .h w => encBin 0 ++ encBin w
  | .s w => encBin 1 ++ encBin w
  | .t w => encBin 2 ++ encBin w
  | .cnot c u _ => encBin 3 ++ encBin c ++ encBin u

end CTCircuit

/-- **The description of a Clifford+T circuit**: the widths in unary, the kept wires, the number of
gates, then the gates (the analogue of the published `FRouting.encCircuit`, with Clifford+T gate tags). -/
def encCTCircuit {inW outW : ℕ} (C : CTCircuit inW outW) : Str :=
  encNat inW ++ encNat outW ++ encNat C.ancillas ++
    (List.ofFn C.kept).flatMap (fun w => encBin w.val) ++
    encBin C.gates.length ++ C.gates.flatMap CTCircuit.encCTGate

end FRouting.Supplement


