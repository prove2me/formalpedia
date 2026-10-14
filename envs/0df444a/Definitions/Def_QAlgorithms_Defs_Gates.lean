-- Prove2me | Definitions.Def_QAlgorithms_Defs_Gates
-- name    : QAlgorithms_Defs_Gates
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:24:26.35413+00:00
-- url     : https://prove2.me/theorems/3507e42d-a7e0-4877-bf94-5b4eaa226919
-- title:
--   Elementary gates (shared definition layer)
-- statement:
--   Elementary gates (shared definition layer)
--
--   ### QAlgorithms.hadamard
--
--   This is a $2 \times 2$ complex matrix whose rows and columns are indexed by the Booleans $\{\text{false}, \text{true}\}$. Its entry at row $a$, column $b$ is
--
--   $$
--   H_{ab} \;=\; \begin{cases} -\dfrac{1}{\sqrt 2} & \text{if } a = b = \text{true},\\[2mm] \dfrac{1}{\sqrt 2} & \text{otherwise.}\end{cases}
--   $$
--
--   With the ordering false $\mapsto 0$, true $\mapsto 1$, this is
--
--   $$
--   H = \frac{1}{\sqrt 2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}.
--   $$
--
--   ### QAlgorithms.hadamardN
--
--   Fix $n \in \mathbb{N}$. This is a complex square matrix whose rows and columns are both indexed by $n$-bit strings, i.e. functions $\{0, \dots, n-1\} \to \{\text{false}, \text{true}\}$; it has size $2^n \times 2^n$.
--
--   Its entry at row $j$, column $i$ is
--
--   $$
--   (H^{\otimes n})_{j,i} \;=\; \begin{cases} -\big(2^{-1/2}\big)^n & \text{if } \operatorname{dotBits}(i,j) = \text{true},\\[1mm] \big(2^{-1/2}\big)^n & \text{otherwise,}\end{cases}
--   $$
--
--   which is the same as $(-1)^{i \cdot j}/2^{n/2}$. Here $\operatorname{dotBits}(i, j)$ is the exclusive-or over all positions $k$ of $i_k \wedge j_k$, i.e. the parity of the number of positions where both strings are true. The scalar $(1/\sqrt2)^n$ is computed as a real number and then viewed as a complex number.
--
--   For $n = 0$ there is exactly one (empty) bit string, and the matrix is the $1 \times 1$ matrix $(1)$.
--
--   ### QAlgorithms.pauliX
--
--   This is a $2 \times 2$ complex matrix indexed by the Booleans. Its entry at row $a$, column $b$ is $0$ if $a = b$ and $1$ if $a \neq b$. With the ordering false $\mapsto 0$, true $\mapsto 1$:
--
--   $$
--   X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}.
--   $$
--
--   ### QAlgorithms.pauliY
--
--   This is a $2 \times 2$ complex matrix indexed by the Booleans. Its entry at row $a$, column $b$ is:
--
--   - $0$ if $a = b$;
--   - $i$ (the imaginary unit) if $a = \text{true}$ and $b = \text{false}$;
--   - $-i$ if $a = \text{false}$ and $b = \text{true}$.
--
--   With the ordering false $\mapsto 0$, true $\mapsto 1$:
--
--   $$
--   Y = \begin{pmatrix} 0 & -i \\ i & 0 \end{pmatrix}.
--   $$
--
--   ### QAlgorithms.pauliZ
--
--   This is a $2 \times 2$ complex diagonal matrix indexed by the Booleans. Its diagonal entry is $1$ at false and $-1$ at true, and its off-diagonal entries are $0$. With the ordering false $\mapsto 0$, true $\mapsto 1$:
--
--   $$
--   Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}.
--   $$
--
--   ### QAlgorithms.phaseS
--
--   This is a $2 \times 2$ complex diagonal matrix indexed by the Booleans. Its diagonal entry is $1$ at false and $i$ (the imaginary unit) at true, and its off-diagonal entries are $0$. With the ordering false $\mapsto 0$, true $\mapsto 1$:
--
--   $$
--   S = \begin{pmatrix} 1 & 0 \\ 0 & i \end{pmatrix}.
--   $$
--
--   ### QAlgorithms.gateT
--
--   This is a $2 \times 2$ complex diagonal matrix indexed by the Booleans. Its diagonal entry is $1$ at false and $e^{i\pi/4}$ at true, and its off-diagonal entries are $0$. With the ordering false $\mapsto 0$, true $\mapsto 1$:
--
--   $$
--   T = \begin{pmatrix} 1 & 0 \\ 0 & e^{i\pi/4} \end{pmatrix}.
--   $$
--
--   ### QAlgorithms.cnot
--
--   This defines a $4\times 4$ complex matrix $\mathrm{CNOT}$ whose rows and columns are indexed by pairs $(a,b)\in\{\mathsf{false},\mathsf{true}\}^2$. Below, $\mathsf{false}$ is written as $0$, $\mathsf{true}$ as $1$, and $\oplus$ denotes exclusive-or. For a row index $p=(p_1,p_2)$ and a column index $q=(q_1,q_2)$, the entry is
--
--   $$
--   \mathrm{CNOT}_{p,q} \;=\; \begin{cases} 1 & \text{if } p_1 = q_1 \text{ and } p_2 = q_2 \oplus q_1,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   Equivalently, column $(a,b)$ has a single $1$, located in row $(a,\, b\oplus a)$. So the matrix sends the basis vector $|a,b\rangle$ to $|a, b\oplus a\rangle$. The **first** component is left unchanged and acts as the control. The **second** component is flipped exactly when the first is $1$.
--
--   ### QAlgorithms.swapGate
--
--   This defines a $4\times 4$ complex matrix $\mathrm{SWAP}$ with rows and columns indexed by pairs $(a,b)\in\{0,1\}^2$ (identifying $\mathsf{false}=0$, $\mathsf{true}=1$). For a row index $p$ and a column index $q=(q_1,q_2)$:
--
--   $$
--   \mathrm{SWAP}_{p,q} \;=\; \begin{cases} 1 & \text{if } p = (q_2, q_1),\\ 0 & \text{otherwise.}\end{cases}
--   $$
--
--   Column $(a,b)$ therefore has a single $1$, in row $(b,a)$. The matrix maps $|a,b\rangle$ to $|b,a\rangle$.
--
--   ### QAlgorithms.rotR
--
--   For each natural number $s$, this defines the $2\times 2$ complex diagonal matrix $R_s$, with rows and columns indexed by $\{\mathsf{false},\mathsf{true}\}$ (in that order, read as $0,1$):
--
--   $$
--   R_s \;=\; \begin{pmatrix} 1 & 0 \\ 0 & e^{2\pi i / 2^s} \end{pmatrix}.
--   $$
--
--   Here $2^s$ is computed as a complex power. The diagonal entry at index $\mathsf{false}$ is $1$, and the entry at index $\mathsf{true}$ is $\exp(2\pi i/2^s)$. Every $s\in\mathbb{N}$ is allowed, including $s=0$. In that case the phase is $e^{2\pi i}=1$, so $R_0$ is the identity matrix. For $s=1$ the phase is $-1$.
--
--   ### QAlgorithms.controlled
--
--   The input is:
--
--   - an arbitrary type $\kappa$ with decidable equality, and
--   - an arbitrary complex matrix $U$ indexed by $\kappa\times\kappa$.
--
--   No finiteness of $\kappa$ and no unitarity of $U$ is assumed.
--
--   The output is the matrix $C(U)$ with rows and columns indexed by pairs $(b,i)\in\{0,1\}\times\kappa$ (identifying $\mathsf{false}=0$, $\mathsf{true}=1$). Its entries are
--
--   $$
--   C(U)_{(b,i),(b',j)} \;=\; \begin{cases} 0 & \text{if } b \neq b',\\ U_{i,j} & \text{if } b = b' = 1,\\ \delta_{i,j} & \text{if } b = b' = 0,\end{cases}
--   $$
--
--   where $\delta_{i,j}$ is $1$ if $i=j$ and $0$ otherwise (the entry of the identity matrix on $\kappa$).
--
--   In block form, ordering the first component $0$ before $1$:
--
--   $$
--   C(U)=\begin{pmatrix} I & 0\\ 0 & U\end{pmatrix}.
--   $$
--
--   The **first** (Boolean) component is the control: $U$ acts on the second component exactly when the control is $1$.
--
--   ### QAlgorithms.reflAt
--
--   The input is:
--
--   - an arbitrary type $\iota$ with decidable equality, and
--   - an element $z\in\iota$.
--
--   The output is the diagonal complex matrix $\mathrm{Refl}_z$ indexed by $\iota\times\iota$. Its diagonal entry at $i$ is $+1$ if $i=z$ and $-1$ if $i\neq z$, and all off-diagonal entries are $0$.
--
--   In terms of the identity $I$ and the basis projector $|z\rangle\langle z|$:
--
--   $$
--   \mathrm{Refl}_z \;=\; 2|z\rangle\langle z| - I.
--   $$
--
--   This fixes the basis vector $|z\rangle$ and negates every other basis vector. If $\iota$ has a single element, $\mathrm{Refl}_z$ is the $1\times1$ identity.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Gates.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Basic
/-!
# Elementary gates (shared definition layer)

Single-qubit gates are matrices indexed by `Bool` (`false` is `|0⟩`, row/column 0); two-qubit
gates are indexed by `Bool × Bool` with the first factor the first qubit (the control, for
controlled gates).
-/

namespace QAlgorithms

/-- de Wolf p.26 (§2.1), p.41 (§4.1): the Hadamard gate `H = (1/√2) [[1, 1], [1, -1]]`. -/
noncomputable def hadamard : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a && b then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)

/-- de Wolf p.26 (§2.1, (2.1)), Childs p.133 (§26.1, (26.2)): the `n`-fold Hadamard transform
`H^{⊗n}`, with `H^{⊗n} |i⟩ = 2^{-n/2} Σ_j (-1)^{i·j} |j⟩`; its `(j, i)` entry is
`2^{-n/2} (-1)^{i·j}`, written `(1/√2)ⁿ (-1)^{i·j}`. -/
noncomputable def hadamardN (n : ℕ) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun j i =>
    if dotBits i j then -(((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ) else (((Real.sqrt 2)⁻¹ ^ n : ℝ) : ℂ)

/-- de Wolf p.185 (§20.1), Childs p.152 (§29.1): the Pauli matrix `X = [[0, 1], [1, 0]]`
(bit flip). `pauliY` and `pauliZ` are defined next to it. -/
def pauliX : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then 0 else 1

/-- de Wolf p.185 (§20.1): the Pauli matrix `Y = [[0, -i], [i, 0]]`. -/
def pauliY : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = b then 0 else if a then Complex.I else -Complex.I

/-- de Wolf p.185 (§20.1), Childs p.152 (§29.1): the Pauli matrix `Z = diag(1, -1)`
(phase flip). -/
def pauliZ : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then -1 else 1

/-- de Wolf p.186 (§20.2): the phase gate `S = diag(1, i)`. -/
def phaseS : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then Complex.I else 1

/-- de Wolf p.121 (§13.1), p.186 (§20.2): the `T` gate `diag(1, e^{iπ/4})`. -/
noncomputable def gateT : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then Complex.exp (Complex.I * Real.pi / 4) else 1

/-- de Wolf p.26 (§2.1): the controlled-NOT gate `|c, t⟩ ↦ |c, t ⊕ c⟩`, control = first qubit. -/
def cnot : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2 = xor q.2 q.1 then 1 else 0

/-- de Wolf p.32 (exercise 2.3), p.45 (§4.5): the SWAP gate `|a, b⟩ ↦ |b, a⟩`. -/
def swapGate : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p = (q.2, q.1) then 1 else 0

/-- de Wolf p.44 (§4.5): `R_s = diag(1, e^{2πi/2^s})` (sign `+`, as printed). -/
noncomputable def rotR (s : ℕ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then Complex.exp (2 * Real.pi * Complex.I / (2 : ℂ) ^ s) else 1

/-- de Wolf p.44 (§4.5), p.46 (§4.6): the controlled version `|0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ U` of an
operator `U`, the control being the first factor: `|c⟩|ψ⟩ ↦ |c⟩ U^c |ψ⟩`. -/
def controlled {κ : Type*} [DecidableEq κ] (U : Matrix κ κ ℂ) : Matrix (Bool × κ) (Bool × κ) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (if p.1 then U p.2 q.2 else (1 : Matrix κ κ ℂ) p.2 q.2)
    else 0

/-- de Wolf p.65 (§7.2): the reflection `2|z⟩⟨z| - I`, which leaves `|z⟩` fixed and puts `-1` in
front of every other basis state. De Wolf's `R_0` on `n` qubits is `reflAt (fun _ => false)`. -/
def reflAt {ι : Type*} [DecidableEq ι] (z : ι) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => if i = z then 1 else -1

/-! ### Sanity tests -/

theorem hadamard_mul_self : hadamard * hadamard = 1 := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  ext a b
  cases a <;> cases b <;>
    simp [hadamard, Matrix.mul_apply, Fintype.sum_bool, ← two_mul] <;>
    field_simp <;> simp [h2]

/-- `H^{⊗n}` is real and symmetric, hence self-adjoint (de Wolf p.26: "Hadamard happens to be its
own inverse"). -/
theorem hadamardN_star (n : ℕ) : star (hadamardN n) = hadamardN n := by
  ext i j
  have h : dotBits j i = dotBits i j := by simp only [dotBits, Bool.and_comm]
  simp only [Matrix.star_apply, hadamardN, Matrix.of_apply, h]
  split_ifs <;> simp [Complex.conj_ofReal]

example : hadamardN 0 = 1 := by
  ext i j
  have : i = j := Subsingleton.elim _ _
  subst this
  simp [hadamardN, dotBits]

/-- `H^{⊗1}` is the Hadamard gate, under `{0,1}¹ ≃ {0,1}`. -/
example (i j : Qubits 1) : hadamardN 1 j i = hadamard (j 0) (i 0) := by
  simp only [hadamardN, hadamard, dotBits, Matrix.of_apply, Fin.sum_univ_one, pow_one]
  cases i 0 <;> cases j 0 <;> simp

example : pauliX * pauliX = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliX, Matrix.mul_apply, Fintype.sum_bool]

example : pauliZ * pauliZ = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliZ]

example : phaseS * phaseS = pauliZ := by
  ext a b; cases a <;> cases b <;> simp [phaseS, pauliZ]

example : rotR 1 = pauliZ := by
  ext a b
  cases a <;> cases b <;> simp [rotR, pauliZ]
  rw [show (2 * Real.pi * Complex.I / 2 : ℂ) = Real.pi * Complex.I by ring]
  exact Complex.exp_pi_mul_I

example : cnot (true, false) (true, true) = 1 ∧ cnot (false, true) (false, true) = 1 := by
  simp [cnot]

example : reflAt (fun _ : Fin 2 => false) (fun _ => false) (fun _ => false) = 1 ∧
    reflAt (fun _ : Fin 2 => false) ![true, false] ![true, false] = -1 := by
  refine ⟨by simp [reflAt], ?_⟩
  have : (![true, false] : Fin 2 → Bool) ≠ fun _ => false := by
    intro h; have := congrFun h 0; simp at this
  simp [reflAt, this]

example {κ : Type*} [DecidableEq κ] : controlled (1 : Matrix κ κ ℂ) = 1 := by
  ext p q
  rcases p with ⟨a, x⟩; rcases q with ⟨b, y⟩
  by_cases h : a = b
  · subst h; cases a <;> simp [controlled, Matrix.one_apply]
  · simp [controlled, h, Matrix.one_apply]

end QAlgorithms


