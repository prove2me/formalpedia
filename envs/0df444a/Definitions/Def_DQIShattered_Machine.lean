-- Prove2me | Definitions.Def_DQIShattered_Machine
-- name    : DQIShattered_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:53.248627+00:00
-- url     : https://prove2.me/theorems/188e6973-6a3f-47c3-976c-7496a3595cec
-- title:
--   Machines writing circuits over $\{H, T, \mathrm{CNOT}\}$, and word codes
-- statement:
--   This definition file fixes what "efficiently" means in the mission.
--
--   1. $\mathrm{OutputsWithin}(T, w, w', t)$: the deterministic multi-stack Turing machine $T$, started on the binary word $w$, halts within $t$ steps with the word $w'$ on its output stack.
--   2. A **circuit** is a number of wires and a list of gates from the finite gate set $\{H, T, \mathrm{CNOT}\}$, applied first to last; its unitary is the ordered product of the gate unitaries, each acting on its own wires.
--   3. **Word codes.** A circuit is written as its wire count in self-delimiting unary followed by its gates. A matrix $B\in\mathbb F_2^{M\times N}$ is written as its sizes followed by its entries row by row. A sign vector $v\in\mathbb F_2^M$ is written as its bits. A real parameter $r\ge 0$ at size $N$ is written as the binary digits of $\lfloor 2^N r\rfloor$.
--
--   These objects give the Turing-machine reading of "DQI can efficiently solve" in Theorems 2.4 and 2.7.
--
--   **Formalization Note** The paper fixes no machine model and no gate set. A fixed finite gate set is the strong reading: gates with real parameters could carry the instance's real numbers for free. $\mathrm{OutputsWithin}$ is a local copy of the platform definition `HMBinPacking.OutputsWithin`, which was not public when this mission was drafted. The gates are the published `QAlgorithms` gates `hadamard`, `gateT` and `cnot`, and the gate set is the published `htcxGateSet`.
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorems 2.4 and 2.7, pp.5, 7 ("efficiently")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods

namespace DQIShattered

open QAlgorithms

/-- **A machine outputs a word within a number of steps** (the run notion behind "efficiently" in
L. Zhou, N. Shutty, M. Sellke, S. P. Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum
Interferometry*, arXiv:2609.40345, held version sha256 0c7f6fdf…, Theorems 2.4 and 2.7, pp.5, 7).

`OutputsWithin M input output t` says that the multi-stack Turing machine `M` (Mathlib's
`Turing.TM2ComputableAux Bool Bool`), started on `input`, halts with `output` on its output stack after at
most `t` steps.

**Formalization Note** The paper names no machine model. This is Mathlib's `Turing.TM2OutputsInTime`, the run
notion of `Turing.TM2ComputableInTime`; polynomial time is invariant under the usual changes of model. The
definition is a local copy of the platform definition `HMBinPacking.OutputsWithin`, which was not public at
drafting time. -/
def OutputsWithin (M : Turing.TM2ComputableAux Bool Bool) (input output : List Bool) (t : ℕ) :
    Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (input.map M.inputAlphabet.symm)
    (some (output.map M.outputAlphabet.symm)) t)

/-- The self-delimiting unary code `1ᵏ 0`. -/
def unaryD (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- A gate of the finite gate set `{H, T, CNOT}` on `n` wires. -/
inductive GateCode (n : ℕ) where
  /-- The Hadamard gate on wire `a`. -/
  | H (a : Fin n)
  /-- The `T` gate on wire `a`. -/
  | T (a : Fin n)
  /-- `CNOT` with control `a` and target `b ≠ a`. -/
  | CNOT (a b : Fin n) (h : a ≠ b)

/-- A single wire as an embedding. -/
def wire1 {n : ℕ} (a : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => a, fun _ _ _ => Subsingleton.elim _ _⟩

/-- An ordered pair of distinct wires as an embedding. -/
def wire2 {n : ℕ} (a b : Fin n) (h : a ≠ b) : Fin 2 ↪ Fin n :=
  ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij h | exact absurd hij.symm h⟩

/-- The gate application of the published gate set `htcxGateSet = {H, T, CNOT}` that a code denotes. -/
noncomputable def GateCode.toApp {n : ℕ} : GateCode n → GateApp htcxGateSet n
  | .H a => ⟨Gate.ofMatrix1 hadamard, by simp [htcxGateSet], wire1 a⟩
  | .T a => ⟨Gate.ofMatrix1 gateT, by simp [htcxGateSet], wire1 a⟩
  | .CNOT a b h => ⟨Gate.ofMatrix2 cnot, by simp [htcxGateSet], wire2 a b h⟩

/-- **A circuit over `{H, T, CNOT}`**: its number of wires and its gates, first gate first. -/
structure Circ where
  /-- The number of wires. -/
  wires : ℕ
  /-- The gates, in order of application. -/
  gates : List (GateCode wires)

/-- The unitary of a circuit, the published `QAlgorithms.Circuit.unitary` (first gate rightmost). -/
noncomputable def Circ.unitary (c : Circ) : Matrix (Qubits c.wires) (Qubits c.wires) ℂ :=
  Circuit.unitary (c.gates.map GateCode.toApp)

/-- The word code of a gate. -/
def GateCode.enc {n : ℕ} : GateCode n → List Bool
  | .H a => unaryD 0 ++ unaryD a
  | .T a => unaryD 1 ++ unaryD a
  | .CNOT a b _ => unaryD 2 ++ unaryD a ++ unaryD b

/-- **The word code of a circuit**: the wire count in self-delimiting unary, then the gates. -/
def encCirc (c : Circ) : List Bool :=
  unaryD c.wires ++ c.gates.flatMap GateCode.enc

/-- The self-delimited binary digits of `⌊2ⁿ r⌋`: the first `n` binary places of a real parameter
`r ≥ 0` (the error rate `γ` or the inverse temperature `β`) that a machine run at size `n` reads. -/
noncomputable def encReal (n : ℕ) (r : ℝ) : List Bool :=
  let a := ⌊(2 : ℝ) ^ n * r⌋₊
  unaryD (Nat.bits a).length ++ Nat.bits a

/-- The self-delimiting code of a matrix over `𝔽₂`: its sizes, then its entries row by row. -/
def encMatrix {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) : List Bool :=
  unaryD n ++ unaryD m ++
    (List.finRange m).flatMap fun i => (List.finRange n).map fun j => decide (B i j = 1)

/-- The code of a vector over `𝔽₂` (the sign vector `v` of the couplings `J = (−1)^v`). -/
def encVec {m : ℕ} (v : Fin m → ZMod 2) : List Bool :=
  (List.finRange m).map fun i => decide (v i = 1)

end DQIShattered


