-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Computational__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:26:22.708162+00:00
-- url     : https://prove2.me/theorems/7ebbb5a9-a5cd-4ad7-becf-6b62a96b8c42
-- title:
--   Computational-basis projections and Pauli and Hadamard layers on the input qubits
-- statement:
--   This file collects the computational-basis objects used to analyse a circuit on $N$ qubits whose first $n$ qubits carry the input.
--
--   1. **Computational count.** For $z\in\{0,1\}^N$, the count $M_z$ has full support $\{0,\dots,N-1\}$ and axis $|z_i\rangle$ on qubit $i$; its mismatch count is the Hamming distance to $z$.
--   2. **Basis projection.** $|z\rangle\langle z|$, the diagonal matrix with a single $1$ at position $z$.
--   3. **Flipping bits.** For a set $F$ of qubits, $z\oplus\mathbf 1_F$ is the word with $(z\oplus\mathbf 1_F)_i=1-z_i$ for $i\in F$ and $z_i$ otherwise.
--   4. **Input positions.** $\mathrm{In}_{n,N}=\{i\in\{0,\dots,N-1\}: i<n\}$; the remaining qubits are ancillas.
--   5. **Bit sign.** $\operatorname{sgn}(b)=(-1)^b\in\mathbb R$ for $b\in\{0,1\}$.
--   6. **Pauli and Hadamard matrices.**
--   $$
--   X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\qquad H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},
--   $$
--   with $Z=\operatorname{diag}(\operatorname{sgn}(0),\operatorname{sgn}(1))$; it is recorded that $H^{\ast}=H$, $H^2=I$, hence $H$ is unitary and defines a one-qubit gate.
--   7. **Input layers.** The local layer $H_{\mathrm{in}}$ applies $H$ to each qubit $i<n$ and the identity elsewhere; similarly $X_{\mathrm{in}}=\bigotimes_i(X\text{ if }i<n,\ I\text{ otherwise})$ and $Z_{\mathrm{in}}=\bigotimes_i(Z\text{ if }i<n,\ I\text{ otherwise})$.
--
--   These objects connect matrix entries to the localization framework: the pattern projections of $M_z$ are the basis projections $|z\oplus\mathbf 1_F\rangle\langle z\oplus\mathbf 1_F|$, so an entry $B_{z\oplus\mathbf 1_F,\,z}$ with $|F|\ge r$ is controlled by $\bigl\|[\mathcal N_{M_z}\ge r]\,B\,P^0_{M_z}\bigr\|$. The Hadamard layer converts flips of all input bits ($X_{\mathrm{in}}$) into the parity character ($Z_{\mathrm{in}}$), which is the Fourier step of the parity lower bound.
--
--   **Formalization Note** The definitions are `computationalCount`, `basisProjection`, `flipWord`, `inputSet`, `bitSign`, `bitX`, `bitZ`, `bitH`, `hadamardGate`, `inputHadamard`, `inputFlip`, `inputPhase`; the lemmas `halfScale_complex_sq`, `bitH_star`, `bitH_sq` and `bitH_unitary` record $h^2=\tfrac12$ in $\mathbb C$ and the properties of $H$ in item 6.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Computational.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Computational.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RegularParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical__RegularParity

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


