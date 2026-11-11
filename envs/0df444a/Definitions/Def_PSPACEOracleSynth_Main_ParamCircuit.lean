-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_ParamCircuit
-- name    : PSPACEOracleSynth_Main_ParamCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:46.585194+00:00
-- url     : https://prove2.me/theorems/06f6a278-43d9-47dd-9709-b59d72dc46a1
-- title:
--   Uniformly controlled gates, parameterized circuits, near-isometries and sparsity patterns
-- statement:
--   1. A **uniformly controlled gate** has a control register, a one-qubit target and a unitary $W_y$ for each control string $y$, and acts as
--   $$\bigoplus_y W_y:=\sum_y |y\rangle\langle y|\otimes W_y.$$
--   2. A **parameterized circuit** is a unitary circuit over $G$ and uniformly controlled gates with one-qubit targets in which the unitaries $W_y$ are left unspecified; these are its *parameters*. Its gate list (registers, gate order, control lists) is a short description even when there are exponentially many parameters.
--   3. For Lemma 3.6, on an index register of $n$ qubits, a row register of $w$ qubits and two flag qubits,
--   $$\iota_{\mathrm{in}}|v\rangle=|v\rangle|0^w\rangle|0\rangle|0\rangle,\qquad \iota_{\mathrm{out}}|u\rangle=|0^n\rangle|u\rangle|1\rangle|1\rangle.$$
--   4. A matrix $\Lambda$ is an **$\varepsilon$-near-isometry** if $(1-\varepsilon)I\preceq\Lambda^\dagger\Lambda\preceq I$ (Loewner order).
--   5. A **sparsity pattern** of $\Lambda$ is a set of positions containing all its nonzero entries (it may contain others).
--
--   **Formalization Note.** A parameterized circuit on $N$ wires is a list of gates `PGate N` (H, T, T† on a wire; CNOT; a uniformly controlled gate with an ordered control list and a target not among the controls). Parameters are a function `W i y ∈ U(2)` of the gate's position `i` in the list and of the control string `y`. A register holding the integer $v$ has bit $q$ of $v$ on its $q$-th wire. Sparsity patterns are given row by row as finite sets of column indices.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §3.1, p. 15 (uniformly controlled gates, parameterized circuits); §3.3, p. 20 (near-isometry, sparsity pattern); Lemma 3.6, p. 21 (ι_in, ι_out)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity
open scoped ComplexOrder

namespace PSPACEOracleSynth.Main

/-!
# Uniformly controlled gates, parameterized circuits, near-isometries and sparsity patterns

Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission #1740 (October 2026),
§3.1, p. 15; §3.3, p. 20; Lemma 3.6, p. 21.

* A **uniformly controlled gate** has a control register, a one-qubit target and a unitary `W_y`
  for every control string `y`; it acts as `⊕_y W_y := Σ_y |y⟩⟨y| ⊗ W_y` (p. 15).
* A **parameterized circuit** is a unitary circuit over `G = {H, T, T†, CNOT}` and uniformly
  controlled gates with one-qubit targets in which the unitaries `W_y` are left unspecified; these
  unitaries are its parameters (p. 15). Here a parameterized circuit on `N` wires is the list of its
  gates (`PCirc N`), and an assignment of parameters gives, for the gate at position `i` of the list
  and the control string `y`, a unitary `W_{i,y} ∈ U(2)`.
* `Λ` is an **`ε`-near-isometry** if `(1 − ε) I ⪯ Λ†Λ ⪯ I`; a **sparsity pattern** of `Λ` is a set
  of positions containing all its nonzero entries (p. 20).
-/

/-- A gate of a parameterized circuit on `N` wires: `H`, `T` or `T†` on one wire, `CNOT` with
control `c` and target `t`, or a uniformly controlled gate with the control wires `ctrl` (in order)
and the one-qubit target `tgt`, not among the controls. -/
inductive PGate (N : ℕ)
  | had (q : Fin N)
  | tg (q : Fin N)
  | tdg (q : Fin N)
  | cnot (c t : Fin N) (h : c ≠ t)
  | uc (m : ℕ) (ctrl : Fin m ↪ Fin N) (tgt : Fin N) (h : tgt ∉ Set.range ctrl)

/-- A parameterized circuit on `N` wires: its gates, applied first to last. The list fixes the
registers (wires), the gate order and the control lists. -/
abbrev PCirc (N : ℕ) := List (PGate N)

/-- An assignment of parameters: `W i y` is the unitary that the gate at position `i` applies to its
target when its control register holds the string `y` (read in the order of its control list). -/
abbrev PParams := ℕ → List Bool → Matrix.unitaryGroup Bool ℂ

/-- A one-qubit matrix `M` acting on wire `q` of `N` wires. -/
def onWire {N : ℕ} (q : Fin N) (M : Matrix Bool Bool ℂ) : Matrix (Bits N) (Bits N) ℂ :=
  Matrix.of fun i j => if ∀ r, r ≠ q → i r = j r then M (i q) (j q) else 0

namespace PGate

/-- `true` exactly for uniformly controlled gates. -/
def isUC {N : ℕ} : PGate N → Bool
  | .uc _ _ _ _ => true
  | _ => false

/-- The `2^N × 2^N` matrix of the gate at position `i` under the parameters `W`. -/
noncomputable def mat {N : ℕ} (W : PParams) (i : ℕ) : PGate N → Matrix (Bits N) (Bits N) ℂ
  | .had q => onWire q hMat
  | .tg q => onWire q tMat
  | .tdg q => onWire q tMat.conjTranspose
  | .cnot c t _ => Matrix.of fun x y =>
      if (∀ r, r ≠ c → r ≠ t → x r = y r) ∧ x c = y c ∧ x t = xor (y t) (y c) then 1 else 0
  | .uc m ctrl tgt _ => Matrix.of fun x y =>
      if ∀ r, r ≠ tgt → x r = y r then
        ((W i (List.ofFn fun k : Fin m => y (ctrl k)) : Matrix Bool Bool ℂ)) (x tgt) (y tgt)
      else 0

end PGate

/-- The unitary of a parameterized circuit under the parameters `W`: the product of its gates, the
first gate rightmost. -/
noncomputable def PCirc.unitary {N : ℕ} (C : PCirc N) (W : PParams) : Matrix (Bits N) (Bits N) ℂ :=
  C.zipIdx.foldl (fun acc gi => gi.1.mat W gi.2 * acc) 1

/-- The number of uniformly controlled gates of a parameterized circuit. -/
def PCirc.ucCount {N : ℕ} (C : PCirc N) : ℕ := (C.filter PGate.isUC).length

/-- The basis state `|v⟩|0^w⟩|0⟩|0⟩` on an index register of `n` qubits (wires `0, …, n − 1`, wire
`q` holding bit `q` of `v`), a row register of `w` qubits (wires `n, …, n + w − 1`) and two flag
qubits (wires `n + w`, `n + w + 1`). -/
def encodeIn (n w : ℕ) (v : ℕ) : Bits (n + w + 2) :=
  fun q => if q.val < n then v.testBit q.val else false

/-- The basis state `|0^n⟩|u⟩|1⟩|1⟩` (wire `n + q` holding bit `q` of `u`). -/
def encodeOut (n w : ℕ) (u : ℕ) : Bits (n + w + 2) :=
  fun q => if q.val < n then false else if q.val < n + w then u.testBit (q.val - n) else true

/-- The embedding `ι_in |v⟩ = |v⟩|0^w⟩|0⟩|0⟩` of Lemma 3.6, for `v < d`. -/
def iotaIn (n w d : ℕ) : Matrix (Bits (n + w + 2)) (Fin d) ℂ :=
  Matrix.of fun z v => if z = encodeIn n w v.val then 1 else 0

/-- The embedding `ι_out |u⟩ = |0^n⟩|u⟩|1⟩|1⟩` of Lemma 3.6, for `u < 2^w`. -/
def iotaOut (n w : ℕ) : Matrix (Bits (n + w + 2)) (Fin (2 ^ w)) ℂ :=
  Matrix.of fun z u => if z = encodeOut n w u.val then 1 else 0

/-- `Λ` is an **`ε`-near-isometry** (p. 20): `(1 − ε) I ⪯ Λ†Λ ⪯ I` in the Loewner order. -/
def IsNearIsometry {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι] (ε : ℝ)
    (Λ : Matrix κ ι ℂ) : Prop :=
  (Λ.conjTranspose * Λ - ((1 - ε : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef ∧
    ((1 : Matrix ι ι ℂ) - Λ.conjTranspose * Λ).PosSemidef

/-- `P` is a **sparsity pattern** of `Λ` (p. 20): row by row, a set of positions containing all
nonzero entries of `Λ` (it may contain others). -/
def IsSparsityPattern {κ ι : Type} (Λ : Matrix κ ι ℂ) (P : κ → Finset ι) : Prop :=
  ∀ u v, Λ u v ≠ 0 → v ∈ P u

end PSPACEOracleSynth.Main


