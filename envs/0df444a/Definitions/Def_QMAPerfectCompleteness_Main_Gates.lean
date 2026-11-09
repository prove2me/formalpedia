-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Main_Gates
-- name    : QMAPerfectCompleteness_Main_Gates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:19.560432+00:00
-- url     : https://prove2.me/theorems/df5a532b-1b6b-427c-88e5-dc66d65b357a
-- title:
--   Gates, gate sets, circuits, and the gate sets $\{H,\Lambda(P)\}$, $\mathcal G_2$ and $HT$
-- statement:
--   Qubits are labelled by $\{0,\dots,n-1\}$ and a computational basis state of $n$ qubits is a bit string $x\in\{0,1\}^n$. A **gate** is an exact unitary matrix on a constant number of qubits. A **gate set** is a finite list of gates. An **instruction** places one gate of the set on pairwise distinct wires of a register, and its matrix on the register is the gate on those wires tensored with the identity on the others. A **circuit** is an ordered list of instructions: the list $[g_1,\dots,g_r]$ has the unitary $g_r\cdots g_1$.
--
--   The concrete gates are
--
--   $$
--   H=\frac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
--   \Lambda(P)=\operatorname{diag}(1,1,1,i),\qquad
--   \langle y|H\otimes H|x\rangle=\frac{(-1)^{y_0x_0+y_1x_1}}{2},
--   $$
--
--   together with $X|u\rangle=|\neg u\rangle$, $\mathrm{CNOT}|u,v\rangle=|u,v\oplus u\rangle$ and $\mathrm{Toffoli}|u,v,w\rangle=|u,v,w\oplus(u\wedge v)\rangle$. They form the gate sets
--
--   $$
--   \{H,\Lambda(P)\},\qquad
--   \mathcal G_2=\{X,\mathrm{CNOT},\mathrm{Toffoli},H\otimes H\},\qquad
--   HT=\{H,\mathrm{Toffoli}\}.
--   $$
--
--   The first is the universal gate set with which the proof of Lemma 3.1 starts, the second is the arithmetic gate set of the proof, and the third is the gate set of the final theorem. The definition also fixes a self-delimiting binary code of instruction lists.
--
--   **Formalization Note** Every gate carries a proof of unitarity. A gate of a list is named by its position, so position 3 of $\mathcal G_2$ is $H\otimes H$. The clause of §2 on approximating gate entries is not a field: every statement of this mission uses one of the three sets above.
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), §2, p. 6; gate set $\mathcal G_2$, p. 2; $HT$, p. 2; $\{H,\Lambda(P)\}$, p. 7

import Definitions.Def_QAlgorithms_Defs_Complexity

open Matrix

/-!
# Gates, gate sets and circuits

Sabee Grewal, Dorian Rudolph, *QMA has perfect completeness*, STOC 2027 submission #490
(October 2026), §2 (p. 6), the gate set `𝒢₂` (p. 2), the gate set `{H, Λ(P)}` (p. 7).

Qubits are labelled by `Fin n`; a computational basis state of `n` qubits is a function
`Fin n → Bool`. A gate is an exact unitary matrix on a constant number of qubits, an instruction
puts a gate on pairwise distinct wires, and a circuit is an ordered list of instructions whose
first element acts first.
-/

namespace QMAPerfectCompleteness.Main

open QAlgorithms.Complexity (Str encNat)

/-- The computational basis of `n` qubits. -/
abbrev Basis (n : ℕ) := Fin n → Bool

/-- A gate: a unitary matrix on `arity` qubits (row index first: `matrix y x = ⟨y|U|x⟩`). -/
structure Gate where
  /-- The number of qubits the gate acts on. -/
  arity : ℕ
  /-- The exact matrix of the gate. -/
  matrix : Matrix (Basis arity) (Basis arity) ℂ
  /-- Gates are unitary. -/
  unitary : matrix ∈ Matrix.unitaryGroup (Basis arity) ℂ

/-- A finite gate set, as a list; a gate is named by its position in the list. -/
abbrev GateSet := List Gate

/-- One gate of `G` placed on pairwise distinct wires of an `n`-qubit register. -/
structure Instr (G : GateSet) (n : ℕ) where
  /-- Which gate of `G`. -/
  gate : Fin G.length
  /-- The wires it acts on: `targets a` carries the gate's `a`-th qubit. -/
  targets : Fin (G.get gate).arity ↪ Fin n

/-- The matrix of an instruction on the whole register: the gate on the target wires tensored with
the identity on all other wires. -/
noncomputable def Instr.matrix {G : GateSet} {n : ℕ} (i : Instr G n) :
    Matrix (Basis n) (Basis n) ℂ :=
  Matrix.of fun y x =>
    if ∀ w, (∀ a, i.targets a ≠ w) → y w = x w then
      (G.get i.gate).matrix (y ∘ i.targets) (x ∘ i.targets)
    else 0

/-- Relabel the wires of an instruction along an injection of registers. -/
def Instr.mapWires {G : GateSet} {n n' : ℕ} (e : Fin n ↪ Fin n') (i : Instr G n) : Instr G n' :=
  ⟨i.gate, i.targets.trans e⟩

/-- The unitary of a circuit: the ordered product of its instructions, the head of the list acting
first, so `[g₁, …, g_r]` is `g_r ⋯ g₁`. -/
noncomputable def circuitMatrix {G : GateSet} {n : ℕ} : List (Instr G n) → Matrix (Basis n) (Basis n) ℂ
  | [] => 1
  | g :: gs => circuitMatrix gs * g.matrix

/-- Self-delimiting binary code of an instruction: the gate's position and each target wire, all
in unary. (The gate determines how many target wires follow.) -/
def Instr.encode {G : GateSet} {n : ℕ} (i : Instr G n) : Str :=
  encNat i.gate.val ++ (List.ofFn fun a => encNat (i.targets a).val).flatten

/-- Self-delimiting binary code of a list of instructions: its length, then the instructions. -/
def encodeGates {G : GateSet} {n : ℕ} (gs : List (Instr G n)) : Str :=
  encNat gs.length ++ gs.flatMap Instr.encode

/-! ### Concrete gates -/

/-- The matrix of a classical reversible map on basis states: `⟨y|M|x⟩ = 1` iff `y = σ x`. -/
def classicalMatrix {n : ℕ} (σ : Basis n → Basis n) : Matrix (Basis n) (Basis n) ℂ :=
  Matrix.of fun y x => if y = σ x then 1 else 0

theorem classicalMatrix_mem_unitaryGroup {n : ℕ} (σ : Basis n → Basis n)
    (hσ : Function.Involutive σ) : classicalMatrix σ ∈ Matrix.unitaryGroup (Basis n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext y y'
  simp only [Matrix.mul_apply, Matrix.star_apply, classicalMatrix, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ y)]
  · simp only [hσ y, if_true]
    by_cases h : y = y' <;> simp [h, eq_comm]
  · intro x _ hx
    have : y ≠ σ x := fun h => hx (by rw [h, hσ x])
    simp [this]
  · simp

/-- The Pauli `X` gate: `|u⟩ ↦ |¬u⟩`. -/
def gateX : Gate :=
  ⟨1, classicalMatrix fun x => ![!x 0], classicalMatrix_mem_unitaryGroup _ (by
    intro x; funext i; fin_cases i; simp)⟩

/-- The `CNOT` gate, control on qubit `0`, target qubit `1`: `|u,v⟩ ↦ |u, v ⊕ u⟩`. -/
def gateCNOT : Gate :=
  ⟨2, classicalMatrix fun x => ![x 0, xor (x 1) (x 0)], classicalMatrix_mem_unitaryGroup _ (by
    intro x; funext i; fin_cases i <;> simp)⟩

/-- The Toffoli gate, controls on qubits `0, 1`, target qubit `2`: `|u,v,w⟩ ↦ |u,v,w ⊕ (u ∧ v)⟩`. -/
def gateToffoli : Gate :=
  ⟨3, classicalMatrix fun x => ![x 0, x 1, xor (x 2) (x 0 && x 1)],
    classicalMatrix_mem_unitaryGroup _ (by intro x; funext i; fin_cases i <;> simp)⟩

/-- The matrix of the Hadamard gate, `2^{-1/2} [[1, 1], [1, -1]]`. -/
noncomputable def hadamardMatrix : Matrix (Basis 1) (Basis 1) ℂ :=
  Matrix.of fun y x =>
    if y 0 && x 0 then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The matrix of `H ⊗ H`: `⟨y|H ⊗ H|x⟩ = (-1)^{y₀x₀ + y₁x₁} / 2`. -/
noncomputable def hadamardTwoMatrix : Matrix (Basis 2) (Basis 2) ℂ :=
  Matrix.of fun y x => if xor (y 0 && x 0) (y 1 && x 1) then -(1 / 2) else 1 / 2

/-- The matrix of the controlled phase `Λ(P)` with `P = diag(1, i)`: `diag(1, 1, 1, i)`. -/
noncomputable def controlledPhaseMatrix : Matrix (Basis 2) (Basis 2) ℂ :=
  Matrix.of fun y x => if y = x then (if x 0 && x 1 then Complex.I else 1) else 0

private theorem sum_basis_one (f : Basis 1 → ℂ) :
    ∑ x, f x = f ![false] + f ![true] := by
  have : (Finset.univ : Finset (Basis 1)) = {![false], ![true]} := by decide
  rw [this, Finset.sum_pair (by decide)]

private theorem sum_basis_two (f : Basis 2 → ℂ) :
    ∑ x, f x = f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  have : (Finset.univ : Finset (Basis 2)) =
      {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [this, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide)]
  ring

theorem hadamardMatrix_mem_unitaryGroup : hadamardMatrix ∈ Matrix.unitaryGroup (Basis 1) ℂ := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [Matrix.mem_unitaryGroup_iff]
  ext y y'
  simp only [Matrix.mul_apply, Matrix.star_apply, hadamardMatrix, Matrix.of_apply, sum_basis_one]
  obtain ⟨a, rfl⟩ : ∃ a, y = ![a] := ⟨y 0, by funext i; fin_cases i; rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b, y' = ![b] := ⟨y' 0, by funext i; fin_cases i; rfl⟩
  cases a <;> cases b <;>
    simp [hs, Complex.conj_ofReal, -one_div]

theorem hadamardTwoMatrix_mem_unitaryGroup :
    hadamardTwoMatrix ∈ Matrix.unitaryGroup (Basis 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext y y'
  simp only [Matrix.mul_apply, Matrix.star_apply, hadamardTwoMatrix, Matrix.of_apply, sum_basis_two]
  obtain ⟨a, b, rfl⟩ : ∃ a b, y = ![a, b] := ⟨y 0, y 1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨c, d, rfl⟩ : ∃ c d, y' = ![c, d] := ⟨y' 0, y' 1, by funext i; fin_cases i <;> rfl⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp <;> norm_num

theorem controlledPhaseMatrix_mem_unitaryGroup :
    controlledPhaseMatrix ∈ Matrix.unitaryGroup (Basis 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext y y'
  simp only [Matrix.mul_apply, Matrix.star_apply, controlledPhaseMatrix, Matrix.of_apply,
    sum_basis_two]
  obtain ⟨a, b, rfl⟩ : ∃ a b, y = ![a, b] := ⟨y 0, y 1, by funext i; fin_cases i <;> rfl⟩
  obtain ⟨c, d, rfl⟩ : ∃ c d, y' = ![c, d] := ⟨y' 0, y' 1, by funext i; fin_cases i <;> rfl⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Complex.conj_I]

/-- The Hadamard gate `H`. -/
noncomputable def gateH : Gate := ⟨1, hadamardMatrix, hadamardMatrix_mem_unitaryGroup⟩

/-- The two-qubit gate `H ⊗ H`. -/
noncomputable def gateHH : Gate := ⟨2, hadamardTwoMatrix, hadamardTwoMatrix_mem_unitaryGroup⟩

/-- The controlled-phase gate `Λ(P)`, `P = diag(1, i)`. -/
noncomputable def gateControlledPhase : Gate :=
  ⟨2, controlledPhaseMatrix, controlledPhaseMatrix_mem_unitaryGroup⟩

/-- The universal gate set `{H, Λ(P)}` with which the source's Lemma 3.1 starts (p. 7). -/
noncomputable def gatesHP : GateSet := [gateH, gateControlledPhase]

/-- The gate set `𝒢₂ = {X, CNOT, Toffoli, H ⊗ H}` (p. 2). Position `3` is `H ⊗ H`. -/
noncomputable def gatesG2 : GateSet := [gateX, gateCNOT, gateToffoli, gateHH]

/-- The gate set `𝐻𝑇 = {H, Toffoli}` (p. 2). -/
noncomputable def gatesHT : GateSet := [gateH, gateToffoli]

end QMAPerfectCompleteness.Main


