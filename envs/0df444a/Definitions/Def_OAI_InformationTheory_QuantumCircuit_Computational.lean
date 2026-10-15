-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational
-- name    : OAI_InformationTheory_QuantumCircuit_Computational
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:26:25.152724+00:00
-- url     : https://prove2.me/theorems/28754b0f-af5f-4fe0-b926-3472a4620655
-- title:
--   Computational-basis counts, bit flips, and Hadamard and Pauli layers on the input register
-- statement:
--   Let $N$ be the number of qubits and $n$ the number of input qubits, which occupy the positions $i<n$; the remaining positions are ancillas. The file defines:
--
--   1. **Computational count.** For a word $z\in\{0,1\}^N$, $C_z$ is the count with full support $[N]$ and vector $|z_i\rangle$ at qubit $i$. Its zero projection is $|z\rangle\langle z|$, and its mismatch count is the Hamming distance to $z$.
--
--   2. **Basis projection.** $|z\rangle\langle z|$, the diagonal matrix with a single entry $1$ at position $(z,z)$.
--
--   3. **Partial complement.** For $F\subseteq[N]$, $z^{\oplus F}$ is the word with $z^{\oplus F}_i=1-z_i$ for $i\in F$ and $z^{\oplus F}_i=z_i$ for $i\notin F$.
--
--   4. **Input positions.** $I_{n,N}=\{i\in[N]:\ i<n\}$.
--
--   5. **Sign of a bit.** $\chi(b)=(-1)^b$, i.e. $\chi(0)=1$ and $\chi(1)=-1$, as a real number.
--
--   6. **One-qubit gates.** The Pauli matrices and the Hadamard matrix
--   $$
--   X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad H=\frac{1}{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},
--   $$
--   with the facts $(1/\sqrt2)^2=1/2$ in $\mathbb{C}$, $H^*=H$ and $H^2=I$, so that $H$ is unitary; $H$ is also packaged as an element of $U(2)$.
--
--   7. **Input layers.** The local layer $\mathcal H_{n,N}$ that applies $H$ to every input qubit and the identity to every ancilla, and the operators
--   $$
--   \mathcal X_{n,N}=\bigotimes_{i}\begin{cases}X & i<n\\ I & i\ge n\end{cases},\qquad \mathcal Z_{n,N}=\bigotimes_{i}\begin{cases}Z & i<n\\ I & i\ge n.\end{cases}
--   $$
--
--   These objects carry the Fourier-analytic part of the parity argument. Conjugation by the Hadamard layer turns the bit-flip operator $\mathcal X_{n,N}$ into the phase operator $\mathcal Z_{n,N}$, whose diagonal is the parity character of the input bits. An entry $B_{z^{\oplus F},z}$ of an operator $B$ is controlled by the localization of $B$ with respect to the computational count $C_z$, because $z^{\oplus F}$ has exactly $|F|$ mismatches with $z$.
--
--   **Formalization Note** The Lean names are `computationalCount`, `basisProjection`, `flipWord`, `inputSet`, `bitSign`, `bitX`, `bitZ`, `bitH`, `halfScale_complex_sq`, `bitH_star`, `bitH_sq`, `bitH_unitary`, `hadamardGate`, `inputHadamard`, `inputFlip` and `inputPhase`. Positions are elements of `Fin N`, compared with $n$ through their values; if $n>N$ every position is an input position. The identities in the last paragraph are proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Computational.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Computational.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

/-- A full computational-basis count. -/
def computationalCount {N : ℕ} (z : Word N) : Count N where
  support := Finset.univ
  vector i := basisVector (z i)
  normalized i _ := basisVector_normalized (z i)

def basisProjection {N : ℕ} (z : Word N) : Operator N :=
  Matrix.diagonal (fun x => if x=z then 1 else 0)

/-- Complement selected computational bits. -/
def flipWord {N : ℕ} (F : Finset (Fin N)) (z : Word N) : Word N :=
  fun i => if i ∈ F then 1-z i else z i

/-- Input positions; ancillas occupy the other positions. -/
def inputSet (n N : ℕ) : Finset (Fin N) := Finset.univ.filter (fun i => i.val<n)

/-- The real character of a single bit. -/
def bitSign (b : Bit) : ℝ := if b=0 then 1 else -1

def bitX : QubitOperator := !![0,1;1,0]
def bitZ : QubitOperator := Matrix.diagonal (fun b => (bitSign b:ℂ))
def bitH : QubitOperator := !![(halfScale:ℂ),(halfScale:ℂ);(halfScale:ℂ),-(halfScale:ℂ)]

lemma halfScale_complex_sq : (halfScale:ℂ)^2=1/2 := by
  rw [← Complex.ofReal_pow,halfScale_sq]
  norm_num

lemma bitH_star : star bitH=bitH := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bitH,Matrix.star_apply]

lemma bitH_sq : bitH*bitH=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bitH,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals linear_combination 2*halfScale_complex_sq

lemma bitH_unitary : bitH ∈ unitary QubitOperator := by
  simp only [Unitary.mem_iff,bitH_star,bitH_sq,and_self]

def hadamardGate : Matrix.unitaryGroup Bit ℂ := ⟨bitH,bitH_unitary⟩

def inputHadamard (n N : ℕ) : LocalLayer N := fun i => if i.val<n then hadamardGate else 1

def inputFlip (n N : ℕ) : Operator N := tensorMatrix (fun i => if i.val<n then bitX else 1)
def inputPhase (n N : ℕ) : Operator N := tensorMatrix (fun i => if i.val<n then bitZ else 1)

end QAC

end

end OAI


