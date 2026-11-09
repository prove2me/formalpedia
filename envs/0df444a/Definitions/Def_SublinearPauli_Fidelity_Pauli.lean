-- Prove2me | Definitions.Def_SublinearPauli_Fidelity_Pauli
-- name    : SublinearPauli_Fidelity_Pauli
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:36:40.575957+00:00
-- url     : https://prove2.me/theorems/a401c491-ca5b-4400-b3f7-7ec1a8ac4a12
-- title:
--   §§4.1, 4.3 — Pauli words, normalized Pauli coefficients, weight, compatible pairs and $\cap,\cup,\Delta$
-- statement:
--   Fix a number of qubits $N\ge 0$ and write $d=2^N$. Operators on $N$ qubits are complex $d\times d$ matrices indexed by bit strings $\{0,1\}^N$.
--
--   A **Pauli word** is $Q=Q_1\otimes\cdots\otimes Q_N\in\mathcal Q=\{X,Y,Z,I\}^{\otimes N}$, built from the single-qubit matrices
--   $$I=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.$$
--   For a Hermitian $d\times d$ matrix $O$ its **Pauli coefficients** are
--   $$\hat O(Q)=\frac{\operatorname{Tr}[OQ]}{\sqrt d},\qquad Q\in\mathcal Q,$$
--   so that $O=\frac1{\sqrt d}\sum_{Q}\hat O(Q)\,Q$ and, for Hermitian $O$, $\|O\|_2^2=\sum_Q\hat O(Q)^2$.
--
--   The **weight** $w(Q)=\sum_{i=1}^N\mathbf 1\{Q_i\ne I\}$ counts the non-identity letters. A pair $(Q,Q')$ belongs to $\mathcal S$ when the two words share a Pauli measurement basis, i.e. at every qubit the letters agree or at least one of them is $I$. On such pairs:
--   1. $Q\cap Q'$ keeps the common letter where $Q_i=Q'_i$ and is $I$ elsewhere;
--   2. $Q\cup Q'$ keeps the non-identity letter of either word;
--   3. $Q\,\Delta\,Q'$ is $I$ where the letters agree and is the non-identity letter where exactly one of them is $I$.
--
--   Finally $\|O\|_2^2=\sum_{a,b}|O_{ab}|^2=\operatorname{Tr}[O^\dagger O]$ is the squared Frobenius (Schatten-2) norm.
--
--   These are the combinatorial objects in which the paper's variance analysis is written.
--
--   **Formalization Note** A Pauli word is a function from the qubits $\{0,\dots,N-1\}$ to the four letters; its matrix is the published Pauli string `ShallowShadows.ShadowNorm.pauli` at the bit-pair label $I=(0,0)$, $X=(1,0)$, $Z=(0,1)$, $Y=(1,1)$, a bijection. The coefficient is the real part of $\operatorname{Tr}[OQ]/\sqrt d$, which is the coefficient itself for Hermitian $O$; note the normalization by $\sqrt d$, not $d$. The operations $\cap,\cup,\Delta$ are total functions that agree with the paper on compatible pairs, the only pairs on which the paper defines and uses them.
--   The squared Frobenius norm reuses the published `QAlgorithms.Papers.Independent.Advance50.P38.frobSq`, specialized to the bit-string carrier.
--
--   The coefficient reuses `DirectFidelity.State.chi` at the labels I=0, X=1, Y=2, Z=3. Its matrix entries and √d normalization agree exactly with the bit-pair Pauli tensors; this primitive has no purity hypothesis.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, §4.1 p.8 (Pauli matrices, Pauli coefficients ρ̂(Q), ∥ρ∥₂² = Σρ̂(Q)²) and §4.3 p.9 (w(Q), Q∆Q′, Q∪Q′, Q∩Q′, the set S)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShallowShadows_ShadowNorm_pauli
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38
import Definitions.Def_DirectFidelity_State_Setting

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- The four single-qubit Pauli letters `I, X, Y, Z` (Dharmavarapu–Acharya–Yu–Liu, STOC 2027
submission #230, §4.1, p.8). -/
inductive Letter
  | I | X | Y | Z
  deriving DecidableEq, Repr

instance : Fintype Letter :=
  ⟨{Letter.I, Letter.X, Letter.Y, Letter.Z}, by intro L; cases L <;> simp⟩

/-- The bit-pair label `(x, z)` of a letter in the convention of the published Pauli strings
`ShallowShadows.ShadowNorm.pauli`, whose single-qubit factor is `i^{xz} X^x Z^z`:
`I = (0,0)`, `X = (1,0)`, `Z = (0,1)`, `Y = (1,1)`. This is a bijection
`{I,X,Y,Z} ≃ {0,1}²`. -/
def Letter.bits : Letter → Fin 2 × Fin 2
  | .I => (0, 0)
  | .X => (1, 0)
  | .Y => (1, 1)
  | .Z => (0, 1)

/-- The inverse of `Letter.bits`. -/
def Letter.ofBits (b : Fin 2 × Fin 2) : Letter :=
  if b.1 = 0 then (if b.2 = 0 then .I else .Z) else (if b.2 = 0 then .X else .Y)

/-- Reindex the four letters by the published direct-fidelity convention `I,X,Y,Z = 0,1,2,3`.
No purity condition is part of its coefficient or Pauli matrix definitions. -/
def Letter.index : Letter → Fin 4
  | .I => 0
  | .X => 1
  | .Y => 2
  | .Z => 3

/-- An `N`-qubit Pauli word `Q ∈ 𝒬 = {X, Y, Z, I}^{⊗N}` (p.8); qubit `j` is index `j : Fin N`. -/
abbrev PauliString (N : ℕ) := Fin N → Letter

/-- The label `(x, z) ∈ {0,1}^N × {0,1}^N` of a Pauli word. -/
def PauliString.label {N : ℕ} (Q : PauliString N) : Bits N × Bits N :=
  (fun j => (Q j).bits.1, fun j => (Q j).bits.2)

/-- The `2^N × 2^N` matrix `Q = Q_1 ⊗ ⋯ ⊗ Q_N` of a Pauli word, via the published Pauli strings
(`I = [[1,0],[0,1]]`, `X = [[0,1],[1,0]]`, `Y = [[0,-i],[i,0]]`, `Z = [[1,0],[0,-1]]`). -/
noncomputable def PauliString.mat {N : ℕ} (Q : PauliString N) : Op N :=
  ShallowShadows.ShadowNorm.pauli Q.label

/-- The Pauli coefficient `Ô(Q) = Tr[O Q] / √d`, `d = 2^N` (p.8), so that
`O = (1/√d) Σ_Q Ô(Q) Q`. The real part is taken; for Hermitian `O` the trace is real.
This specializes the published √d-normalized characteristic function, with the same four matrices. -/
noncomputable def coeff {N : ℕ} (O : Op N) (Q : PauliString N) : ℝ :=
  DirectFidelity.State.chi O (fun j => (Q j).index)

/-- The Pauli weight `w(Q) = Σ_i 1{Q_i ≠ I}` (§4.3, p.9). -/
def weight {N : ℕ} (Q : PauliString N) : ℕ :=
  (Finset.univ.filter fun j => Q j ≠ Letter.I).card

/-- `(Q, Q') ∈ 𝒮`: the two words share a measurement basis, i.e. at every qubit the letters agree
or at least one of them is `I` (§4.3, p.9). -/
def Compatible {N : ℕ} (Q Q' : PauliString N) : Prop :=
  ∀ j, Q j = Q' j ∨ Q j = Letter.I ∨ Q' j = Letter.I

instance {N : ℕ} (Q Q' : PauliString N) : Decidable (Compatible Q Q') := by
  unfold Compatible; infer_instance

/-- `Q ∩ Q'` (p.9): keeps the common letter where `Q_i = Q'_i`, and `I` elsewhere. -/
def inter {N : ℕ} (Q Q' : PauliString N) : PauliString N :=
  fun j => if Q j = Q' j then Q j else Letter.I

/-- `Q ∪ Q'` (p.9): keeps the non-identity letter of either word (on compatible pairs). -/
def union {N : ℕ} (Q Q' : PauliString N) : PauliString N :=
  fun j => if Q j = Letter.I then Q' j else Q j

/-- `Q Δ Q'` (p.9): `I` where the letters agree, and the non-identity letter where exactly one of
them is `I` (on compatible pairs). -/
def symmDiff {N : ℕ} (Q Q' : PauliString N) : PauliString N :=
  fun j => if Q j = Q' j then Letter.I else if Q j = Letter.I then Q' j else Q j

/-- The squared Frobenius (Schatten-2) norm `‖O‖₂² = Tr[O†O] = Σ_{a,b} |O_{ab}|²`. -/
noncomputable def frobSq {N : ℕ} (O : Op N) : ℝ :=
  QAlgorithms.Papers.Independent.Advance50.P38.frobSq O

end SublinearPauli.Fidelity


