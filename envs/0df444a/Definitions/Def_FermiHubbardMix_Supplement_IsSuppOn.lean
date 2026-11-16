-- Prove2me | Definitions.Def_FermiHubbardMix_Supplement_IsSuppOn
-- name    : FermiHubbardMix_Supplement_IsSuppOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:00:49.869354+00:00
-- url     : https://prove2.me/theorems/c6dee26e-beb4-4cb5-9d86-fe036a217ae7
-- title:
--   Qubit support of an operator, qubit partial trace $\mathrm{tr}_S$, single-site Paulis $\sigma_P^{(j)}$
-- statement:
--   Operators on $n$ qubits are complex $2^n\times 2^n$ matrices indexed by bitstrings $x\in\{0,1\}^n$, coordinate $k$ being qubit $k$.
--
--   1. An operator $P$ is **supported on** $S\subseteq[n]$ if $P=O_S\otimes I_{[n]\setminus S}$ for some operator $O_S$ on the qubits of $S$. The support $\mathrm{supp}(P)$ is the least such set, so "$P$ is supported on $X$" means $\mathrm{supp}(P)\subseteq X$.
--   2. For $S\subseteq[n]$, the **partial trace** $\mathrm{tr}_S(X)$ over the qubits of $S$ is the unique linear map with $\mathrm{tr}(M\,\mathrm{tr}_S(X))=\mathrm{tr}((M\otimes I_S)X)$ for every operator $M$ on the remaining qubits. It is recorded here as the $n$-qubit operator $\mathrm{tr}_S(X)\otimes I_S$, with entries
--   $$
--   (\mathrm{tr}_S(X)\otimes I_S)_{x,y}=[x_S=y_S]\sum_{z\in\{0,1\}^S}X_{x[S:=z],\,y[S:=z]} .
--   $$
--   3. For a qubit $j$ and $P\in\{\sigma_X,\sigma_Y,\sigma_Z\}$, with
--   $$
--   \sigma_X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad \sigma_Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\quad \sigma_Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
--   $$
--   $\sigma_P^{(j)}$ is the $n$-qubit operator acting as $\sigma_P$ on qubit $j$ and as the identity elsewhere.
--
--   These are the qubit notions of Part I of the paper (spin systems), separate from the fermionic local algebras of Part II.
--
--   **Formalization Note** Support is written entrywise: $P_{x,y}=O(x|_S,y|_S)$ when $x,y$ agree off $S$, and $0$ otherwise. The partial trace operator vanishes exactly when $\mathrm{tr}_S(X)$ does, which is the only way the partial trace enters the theorems. The $2\times2$ Paulis and the tensor product are the published `FermiCap.Gaussian.pauliX/Y/Z` and `pauliString`.
-- source:
--   Bakshi, Moitra, Tan, Algorithmic Aspects of the Fermi–Hubbard Model, arXiv:2604.08408 (held version, sha256 055b8f8f…), Definition 5.1, p.16; Definition 5.2, p.17; Definition 5.3, p.17

import Mathlib
import Definitions.Def_FermiCap_Gaussian_Majorana
import Definitions.Def_FermiHubbardMix_parityOp
open scoped BigOperators
open Matrix
noncomputable section

namespace FermiHubbardMix.Supplement

open scoped Classical in
/-- **Definition 5.1 (Support of an operator)** (Bakshi, Moitra, Tan, *Algorithmic Aspects of the
Fermi–Hubbard Model*, arXiv:2604.08408 (held version, sha256 055b8f8f…), p.16): an `n`-qubit operator
`P` is supported on `S ⊆ [n]` if `P = O_S ⊗ I_{[n]∖S}` for some operator `O` on the qubits of `S`;
`supp(P)` is the least such `S`, so "`P` is supported on `X`" in the paper's theorems means
`supp(P) ⊆ X`, i.e. `IsSuppOn P X`.

**Formalization Note** Operators on `n` qubits are the published `FermiHubbardMix.Op n =
Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ`, coordinate `k` of a bitstring being qubit `k`.
`P = O ⊗ I` is written entrywise: `P x y = O (x|_S) (y|_S)` when `x` and `y` agree off `S`, and
`P x y = 0` otherwise. -/
def IsSuppOn {n : ℕ} (P : Op n) (S : Set (Fin n)) : Prop :=
  ∃ O : Matrix (S → Fin 2) (S → Fin 2) ℂ, ∀ x y : Fin n → Fin 2,
    P x y = if (∀ k, k ∉ S → x k = y k) then O (fun k => x k) (fun k => y k) else 0

/-- The bitstring `x` with its coordinates in `S` replaced by `z`. -/
def overwrite {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Fin 2) (z : S → Fin 2) : Fin n → Fin 2 :=
  fun k => if h : k ∈ S then z ⟨k, h⟩ else x k

open scoped Classical in
/-- **Definition 5.2 (Partial trace)** (arXiv:2604.08408, held version sha256 055b8f8f…, p.17): the
partial trace `tr_S(X)` over the qubits of `S`, returned as the `n`-qubit operator `tr_S(X) ⊗ I_S`.

**Formalization Note** Entry `(x, y)` is `[x|_S = y|_S] · ∑_{z ∈ {0,1}^S} X(x[S := z], y[S := z])`, which
depends only on `x|_{S^c}, y|_{S^c}` and is the matrix of `tr_S(X)` (the unique map with
`tr(M tr_S(X)) = tr((M ⊗ I_S) X)`) tensored with `I_S`. In particular `ptrQ S X = 0` if and only if
`tr_S(X) = 0`, which is the only way the partial trace enters the theorems (`tr_i(X_i) = 0`,
Definition 7.1). -/
def ptrQ {n : ℕ} (S : Finset (Fin n)) (X : Op n) : Op n := fun x y =>
  if (∀ k ∈ S, x k = y k) then ∑ z : S → Fin 2, X (overwrite S x z) (overwrite S y z) else 0

/-- **Definition 5.3 (Pauli matrices)** (arXiv:2604.08408, held version sha256 055b8f8f…, p.17):
`σ_P^{(j)}`, the `n`-qubit operator acting as the `2 × 2` matrix `P` on qubit `j` and as the identity on
all other qubits.

**Formalization Note** `P` is one of the published `FermiCap.Gaussian.pauliX = [[0,1],[1,0]]`,
`pauliY = [[0,-i],[i,0]]`, `pauliZ = diag(1,-1)` (exactly the paper's `σ_X, σ_Y, σ_Z`), and the tensor
product is the published `FermiCap.Gaussian.pauliString`. -/
def sitePauli {n : ℕ} (j : Fin n) (P : Matrix (Fin 2) (Fin 2) ℂ) : Op n :=
  FermiCap.Gaussian.pauliString (fun k => if k = j then P else 1)

end FermiHubbardMix.Supplement


