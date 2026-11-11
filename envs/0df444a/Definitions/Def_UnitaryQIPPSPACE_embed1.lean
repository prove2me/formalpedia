-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_embed1
-- name    : UnitaryQIPPSPACE_embed1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:05.836475+00:00
-- url     : https://prove2.me/theorems/3cbe36e9-71b4-4bd6-8f82-e7e682526f86
-- title:
--   Gates $H$, $T$, $\mathrm{CNOT}$ and their embeddings into $k$ qubits
-- statement:
--   The gate set is $G=\{H,T,\mathrm{CNOT}\}$ with
--   $$H=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\quad T=\begin{pmatrix}1&0\\0&e^{i\pi/4}\end{pmatrix},\quad \mathrm{CNOT}=|0\rangle\langle0|\otimes I+|1\rangle\langle1|\otimes\begin{pmatrix}0&1\\1&0\end{pmatrix}.$$
--
--   A one-qubit gate on qubit $i$ of a $k$-qubit register is $I\otimes\cdots\otimes G\otimes\cdots\otimes I$; a two-qubit gate on the ordered pair $(i,j)$ acts with qubit $i$ as its first factor. A gate naming a qubit that does not exist is the zero matrix (such circuits are ill formed and excluded).
--
--   **Formalization Note** The paper fixes $G$ "without loss of generality, … for example, $\{H,T,\mathrm{CNOT}\}$"; this is that set.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §2, Quantum circuits, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_Bits

open Matrix

namespace UnitaryQIPPSPACE

/-- The **Hadamard gate** `H = (1/√2)(1 1; 1 −1)` (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, §2 Quantum circuits, p. 9 (PDF p. 11)). Rows and
columns are indexed by the bit `false = |0⟩`, `true = |1⟩`. -/
noncomputable def gateH : Matrix Bool Bool ℂ :=
  fun a b => (1 / (Real.sqrt 2 : ℂ)) * (if a && b then -1 else 1)

/-- The **T gate** `T = (1 0; 0 e^{iπ/4})` (p. 9, PDF p. 11). -/
noncomputable def gateT : Matrix Bool Bool ℂ :=
  fun a b => if a = b then (if a then Complex.exp (↑(Real.pi / 4) * Complex.I) else 1) else 0

/-- The **CNOT gate** `CNOT = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ (0 1; 1 0)` (p. 9, PDF p. 11): the first bit
is the control, the second the target; entry `((a, b), (a', b'))` is `1` iff `a = a'` and
`b = b' ⊕ a`. -/
def gateCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  fun x y => if x.1 = y.1 ∧ x.2 = Bool.xor y.2 y.1 then 1 else 0

open Classical in
/-- A single-qubit gate `G` acting on qubit `i` of a `k`-qubit register, as a `2^k × 2^k` matrix
(`I ⊗ ⋯ ⊗ G ⊗ ⋯ ⊗ I`): entry `(x, x')` is `G(x_i, x'_i)` if `x` and `x'` agree off qubit `i`, and
`0` otherwise. (The zero matrix if `i ≥ k`; circuits that name such a qubit are ill-formed.) -/
noncomputable def embed1 (G : Matrix Bool Bool ℂ) (k i : ℕ) : Matrix (Bits k) (Bits k) ℂ :=
  fun x x' => if hi : i < k then
    (if ∀ j : Fin k, j.val ≠ i → x j = x' j then G (x ⟨i, hi⟩) (x' ⟨i, hi⟩) else 0) else 0

open Classical in
/-- A two-qubit gate `G` acting on the ordered pair of qubits `(i, j)` of a `k`-qubit register
(qubit `i` is the first tensor factor of `G`): entry `(x, x')` is `G((x_i, x_j), (x'_i, x'_j))` if
`x` and `x'` agree off `{i, j}`, and `0` otherwise. (The zero matrix if `i` or `j` is out of
range; circuits that name such qubits, or `i = j`, are ill-formed.) -/
noncomputable def embed2 (G : Matrix (Bool × Bool) (Bool × Bool) ℂ) (k i j : ℕ) :
    Matrix (Bits k) (Bits k) ℂ :=
  fun x x' => if h : i < k ∧ j < k then
    (if ∀ l : Fin k, l.val ≠ i → l.val ≠ j → x l = x' l then
      G (x ⟨i, h.1⟩, x ⟨j, h.2⟩) (x' ⟨i, h.1⟩, x' ⟨j, h.2⟩) else 0) else 0

end UnitaryQIPPSPACE


