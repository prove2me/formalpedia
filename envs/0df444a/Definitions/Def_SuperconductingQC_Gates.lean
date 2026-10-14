-- Prove2me | Definitions.Def_SuperconductingQC_Gates
-- name    : SuperconductingQC_Gates
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T01:23:36.153606+00:00
-- url     : https://prove2.me/theorems/a3d5afe8-a98f-47e5-965c-c32a062ca5b9
-- title:
--   Gate-model definitions for superconducting qubits
-- statement:
--   Gate-model vocabulary for qubits realised in superconducting circuits.
--
--   1. **Pauli matrices.** $\sigma^x=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $\sigma^y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix}$.
--   2. **Two-transmon coupling Hamiltonian.** For real parameters $\hbar$ and $J$, on $\mathbb C^2\otimes\mathbb C^2$,
--   $$H=\frac{\hbar J}{2}\left(\sigma^x_1\sigma^x_2+\sigma^y_1\sigma^y_2\right),\qquad \sigma^a_1\sigma^b_2:=\sigma^a\otimes\sigma^b .$$
--   3. **Time evolution.** For a Hermitian matrix $H$, $U(t)=\exp\left(-\tfrac{i t}{\hbar}H\right)$ (matrix exponential).
--   4. **Two-qubit gates** in the computational basis $|ab\rangle$, $a,b\in\{0,1\}$ (first label = first qubit):
--      - $\mathrm{iSWAP}$: $|00\rangle\mapsto|00\rangle$, $|01\rangle\mapsto i|10\rangle$, $|10\rangle\mapsto i|01\rangle$, $|11\rangle\mapsto|11\rangle$;
--      - $\mathrm{CNOT}$ (control = first qubit): $|c,t\rangle\mapsto|c,\,t\oplus c\rangle$.
--   5. **Toffoli gate** on three qubits $0,1,2$: $|a,b,c\rangle\mapsto|a,b,\,c\oplus ab\rangle$.
--   6. **Gates on an $n$-qubit register.** The register's basis states are bit strings $x\in\{0,1\}^n$. For a $2\times2$ matrix $U$ and a qubit $k$, $U^{(k)}$ applies $U$ to qubit $k$ and the identity elsewhere: $\langle x|U^{(k)}|y\rangle=U_{x_k y_k}$ if $x_j=y_j$ for all $j\ne k$, and $0$ otherwise. For a $4\times4$ matrix $G$ and qubits $i\neq j$, $G^{(i,j)}$ applies $G$ to the ordered pair $(i,j)$: $\langle x|G^{(i,j)}|y\rangle=G_{(x_i x_j),(y_i y_j)}$ if $x_l=y_l$ for all $l\notin\{i,j\}$, and $0$ otherwise.
--   7. **Gate sets** inside the unitary group $U(2^n)$: $\mathcal S_n$, the set of all $U^{(k)}$ with $U\in U(2)$ and $k$ any qubit; and $\mathcal G_n(G)$, the set of all $G^{(i,j)}$ with $i\ne j$.
--   8. **Two-level unitaries** on $\mathbb C^\iota$ ($\iota$ a finite index set): unitaries that act as the identity outside the span of at most two basis vectors $e_a,e_b$, i.e. $W_{xy}=\delta_{xy}$ whenever $x\notin\{a,b\}$ or $y\notin\{a,b\}$.
--
--   These objects are the shared vocabulary for every statement of the mission.
--
--   **Formalization Note** States of $n$ qubits are indexed by functions `Fin n → Fin 2`; two-qubit operators by `Fin 2 × Fin 2` (Kronecker product `⊗ₖ`, first factor = first qubit). The matrix exponential is Mathlib's `NormedSpace.exp`. Gate sets are subsets of `Matrix.unitaryGroup`, so a member is a unitary together with a witness that it equals the stated matrix.
-- source:
--   Wikipedia, "Superconducting quantum computing" (PDF snapshot supplied by the mission author, retrieved 2026-10-13), https://en.wikipedia.org/wiki/Superconducting_quantum_computing; sections 'Quantum gates', 'Criteria for a viable quantum processor', 'Transmon' (coupling Hamiltonian H = (ħJ/2)(σ1x σ2x + σ1y σ2y)); gate conventions as in Nielsen–Chuang §4.3, §4.5

import Mathlib

/-!
# Superconducting quantum computing: gate-model definitions

Definitions for the Prove2Me mission draft "Universality of single-qubit gates and iSWAP",
drawn from the Wikipedia article *Superconducting quantum computing*
(sections "Quantum gates", "Criteria for a viable quantum processor", "Transmon").
-/

open scoped Kronecker

namespace SuperconductingQC

/-- The Pauli matrix `σˣ`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli matrix `σʸ`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- The Hamiltonian of two capacitively coupled transmons,
`H = (ħJ/2) (σ₁ˣ σ₂ˣ + σ₁ʸ σ₂ʸ)`, acting on `ℂ² ⊗ ℂ²`
(basis indexed by `Fin 2 × Fin 2`, first component = qubit 1). -/
noncomputable def couplingHamiltonian (hbar J : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((hbar * J / 2 : ℝ) : ℂ) • (pauliX ⊗ₖ pauliX + pauliY ⊗ₖ pauliY)

/-- The Schrödinger time-evolution operator `U(t) = exp(-i t H / ħ)` of a
time-independent Hamiltonian `H`. -/
noncomputable def timeEvolution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hbar t : ℝ) (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((-(Complex.I * ((t / hbar : ℝ) : ℂ))) • H)

/-- The iSWAP gate: `|00⟩ ↦ |00⟩`, `|01⟩ ↦ i|10⟩`, `|10⟩ ↦ i|01⟩`, `|11⟩ ↦ |11⟩`. -/
def iSWAP : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun p q =>
  if p = q ∧ p.1 = p.2 then 1
  else if p.1 ≠ p.2 ∧ p = q.swap then Complex.I
  else 0

/-- The controlled-NOT gate with control qubit 1 and target qubit 2:
`|c, t⟩ ↦ |c, t ⊕ c⟩`. -/
def CNOT : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun p q =>
  if p.1 = q.1 ∧ p.2 = q.2 + q.1 then 1 else 0

/-- The Toffoli (CCNOT) gate on three qubits, controls `0, 1`, target `2`:
`|a, b, c⟩ ↦ |a, b, c ⊕ (a ∧ b)⟩`. Basis states are `Fin 3 → Fin 2`. -/
def toffoli : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ := fun x y =>
  if x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 + y 0 * y 1 then 1 else 0

/-- The operator on an `n`-qubit register (basis states `Fin n → Fin 2`) that applies the
single-qubit matrix `U` to qubit `k` and the identity to every other qubit. -/
def onQubit {n : ℕ} (k : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun x y =>
  if ∀ j, j ≠ k → x j = y j then U (x k) (y k) else 0

/-- The operator on an `n`-qubit register that applies the two-qubit matrix `G` to the
ordered pair of qubits `(i, j)` (qubit `i` = first tensor factor of `G`) and the identity to
every other qubit. Meaningful for `i ≠ j`. -/
def onPair {n : ℕ} (i j : Fin n) (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun x y =>
  if ∀ l, l ≠ i → l ≠ j → x l = y l then G (x i, x j) (y i, y j) else 0

/-- All single-qubit gates on an `n`-qubit register: an arbitrary `2 × 2` unitary applied to
any one qubit. -/
def singleQubitGates (n : ℕ) : Set (Matrix.unitaryGroup (Fin n → Fin 2) ℂ) :=
  {W | ∃ (k : Fin n) (U : Matrix (Fin 2) (Fin 2) ℂ),
    U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ (W : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) = onQubit k U}

/-- All placements of a fixed two-qubit gate `G` on an ordered pair of distinct qubits of an
`n`-qubit register. -/
def twoQubitGateInstances (n : ℕ) (G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Set (Matrix.unitaryGroup (Fin n → Fin 2) ℂ) :=
  {W | ∃ i j : Fin n, i ≠ j ∧ (W : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) = onPair i j G}

/-- Two-level unitaries on a finite-dimensional space with basis `ι`: unitaries that act as
the identity outside the span of (at most) two basis vectors `e_a, e_b`. -/
def twoLevelUnitaries (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Set (Matrix.unitaryGroup ι ℂ) :=
  {W | ∃ a b : ι, ∀ x y : ι, (x ≠ a ∧ x ≠ b) ∨ (y ≠ a ∧ y ≠ b) →
    (W : Matrix ι ι ℂ) x y = (1 : Matrix ι ι ℂ) x y}

end SuperconductingQC


