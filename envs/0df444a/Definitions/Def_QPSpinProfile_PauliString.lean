-- Prove2me | Definitions.Def_QPSpinProfile_PauliString
-- name    : QPSpinProfile_PauliString
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:18.836192+00:00
-- url     : https://prove2.me/theorems/e754712b-fe3d-4a3d-9c80-146e836ff14d
-- title:
--   Weight-$p$ Pauli strings $\mathcal P_{n,p}$ and their matrices
-- statement:
--   Let $[n]$ be a set of $n$ qubits, so that $n$-qubit operators act on $(\mathbb C^2)^{\otimes n}$ and are $2^n\times 2^n$ matrices indexed by bit strings $x\in\{0,1\}^n$. The one-qubit Pauli matrices are
--   $$
--   I=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix},\quad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
--   $$
--   For a $p$-element subset $I=\{i_1<\dots<i_p\}\subseteq[n]$ and $a=(a_1,\dots,a_p)\in\{X,Y,Z\}^p$, the **Pauli string** $P^a_I$ acts as $a_j$ on qubit $i_j$ and as the identity on every other qubit; its **support** is $\mathrm{supp}(P^a_I)=I$. The set of weight-$p$ Pauli strings is
--   $$
--   \mathcal P_{n,p}=\Big\{P^a_I : I\in\tbinom{[n]}{p},\ a\in\{X,Y,Z\}^p\Big\},\qquad |\mathcal P_{n,p}|=3^p\binom np .
--   $$
--   The matrix of a string is the tensor product of its letters, with entries $\prod_i \sigma_{w_i}(x_i,y_i)$.
--
--   These strings index the couplings of the dense quantum $p$-spin model and the coordinates of every Pauli profile in this mission.
--
--   **Formalization Note** A string is a word $w:\mathrm{Fin}\,n\to\mathrm{Fin}\,4$ ($0=I$, $1=X$, $2=Y$, $3=Z$) with exactly $p$ non-identity letters; $(I,a)\mapsto w$ is a bijection. Qubits are labelled $0,\dots,n-1$ and a basis vector is a word $x:\mathrm{Fin}\,n\to\mathrm{Fin}\,2$ (`Qubits n`).
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §1.1, p.2–3 (PDF p.5–6)

import Mathlib

namespace QPSpinProfile

open Matrix

/-- The computational-basis index set of `n` qubits, `(ℂ²)^{⊗n}`: a basis vector is a word
`x : Fin n → Fin 2` (Al-Ghattas, Gamarnik, Kiani, *Beyond light cones: State preparation complexity
in quantum spin glasses*, arXiv:2610.02166, held version sha256 a0a1ec89…, §1.1, p.2–3, PDF p.5–6).
An `n`-qubit operator is a `Matrix (Qubits n) (Qubits n) ℂ`.

**Formalization Note** Qubits are labelled `0, …, n-1` (the paper's `1, …, n`). -/
abbrev Qubits (n : ℕ) : Type := Fin n → Fin 2

/-- The one-qubit Pauli matrices (arXiv:2610.02166, held version sha256 a0a1ec89…, §1.1, p.2,
PDF p.5): `0 ↦ I`, `1 ↦ X = [[0,1],[1,0]]`, `2 ↦ Y = [[0,-i],[i,0]]`, `3 ↦ Z = [[1,0],[0,-1]]`. -/
def pauliMat : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- The set `𝒫_{n,p}` of weight-`p` Pauli strings on `n` qubits (arXiv:2610.02166, held version
sha256 a0a1ec89…, §1.1, p.2–3, PDF p.5–6): the operators `P^a_I` acting as `a_j ∈ {X,Y,Z}` on
qubit `i_j` of a `p`-subset `I = {i_1 < ⋯ < i_p}` and as the identity elsewhere.

**Formalization Note** A string is a word `w : Fin n → Fin 4` (`0 = I`, `1 = X`, `2 = Y`,
`3 = Z`) with exactly `p` non-identity letters; `(I, a) ↦ w` with `I = {i | w i ≠ 0}` and
`a_j = w i_j` is a bijection with the paper's pairs, so `|𝒫_{n,p}| = 3^p C(n,p)`. -/
abbrev PauliString (n p : ℕ) : Type :=
  {w : Fin n → Fin 4 // (Finset.univ.filter (fun i => w i ≠ 0)).card = p}

/-- The support `supp(P^a_I) = I` of a Pauli string: the qubits it acts on nontrivially
(arXiv:2610.02166, §1.1, p.3, PDF p.6). -/
def PauliString.supp {n p : ℕ} (P : PauliString n p) : Finset (Fin n) :=
  Finset.univ.filter (fun i => P.1 i ≠ 0)

/-- The `2^n × 2^n` matrix of a Pauli string: the tensor product `⊗_i σ_{w i}` of its letters,
with entries `∏_i σ_{w i}(x_i, y_i)` (arXiv:2610.02166, §1.1, p.2–3, PDF p.5–6). -/
def PauliString.mat {n p : ℕ} (P : PauliString n p) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => ∏ i, pauliMat (P.1 i) (x i) (y i)

end QPSpinProfile


