-- Prove2me | Definitions.Def_BaconThesis_WeakUniv_embed
-- name    : BaconThesis_WeakUniv_embed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:36:44.227105+00:00
-- url     : https://prove2.me/theorems/b9f9091b-8454-48c1-b255-7b66d6c19902
-- title:
--   A two-qubit operator acting on qubits $k,l$ of an $n$-qubit register
-- statement:
--   The $n$-qubit Hilbert space has the computational basis $|x\rangle=|x_0\rangle\otimes\cdots\otimes|x_{n-1}\rangle$, $x\in\{0,1\}^n$. For two distinct qubits $k\neq l$ and a two-qubit operator $M$, the operator $M^{(kl)}$ acts as $M$ on qubits $k,l$ and as the identity on all others:
--   $$
--   \langle x|M^{(kl)}|y\rangle=\begin{cases}\langle x_kx_l|M|y_ky_l\rangle & \text{if } x_m=y_m \text{ for all } m\notin\{k,l\},\\ 0&\text{otherwise.}\end{cases}
--   $$
--   This is how the book's $E_{i,i+1}$, $T^P_{i,i+1}$, $T^Q_{i,i+1}$, $\bar Z_{i,i+1}$ act on the whole register.
--
--   **Formalization Note** Qubits are numbered $0,\dots,n-1$ instead of the book's $1,\dots,n$. The definition is used only for $k\neq l$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §9.1.1, p.125 (PDF p.142), and §9.2, eqs. (9.9)–(9.10), p.126 (PDF p.143)

import Mathlib

namespace BaconThesis.WeakUniv

/-- **A two-qubit operator acting on qubits `k` and `l` of an `n`-qubit register.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§9.1.1, p.125 (PDF p.142): "a two qubit Hamiltonian acting between the kth and lth qubit", and
§9.2, eqs. (9.9)–(9.10), p.126 (PDF p.143), where `diag_ij(a, b, c, d)` and `E_{i,i+1}` act on
qubits `i, j` of the `n` qubits (and as the identity on the others).

The `n`-qubit space has the computational basis `|x⟩ = |x_0⟩ ⊗ ⋯ ⊗ |x_{n−1}⟩`, `x : Fin n → Fin 2`.
For a two-qubit operator `M` (basis `|ab⟩`, `a` on qubit `k`, `b` on qubit `l`),
`embed n k l M` is `M` on qubits `k, l` tensored with the identity on all other qubits:
`⟨x| embed n k l M |y⟩ = ⟨x_k x_l| M |y_k y_l⟩` if `x_m = y_m` for every `m ∉ {k, l}`, and `0`
otherwise.

**Formalization Note.** Qubits are indexed `0, …, n−1` (`Fin n`), the book's `1, …, n`. The
definition is meant for `k ≠ l` (every use has `k ≠ l`); for `k = l` its value is not used. -/
def embed (n : ℕ) (k l : Fin n) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => if (∀ m, m ≠ k → m ≠ l → x m = y m) then M (x k, x l) (y k, y l) else 0

end BaconThesis.WeakUniv


