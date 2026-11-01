-- Prove2me | Definitions.Def_BaconThesis_Universality_embedPair
-- name    : BaconThesis_Universality_embedPair
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:06.329274+00:00
-- url     : https://prove2.me/theorems/28ffe6c3-cd87-48e7-bac8-2b9de03af8a0
-- title:
--   An operator $V$ on subsystems $a,b$, tensored with the identity on the others
-- statement:
--   Consider $n$ subsystems of dimensions $d_0,\dots,d_{n-1}$ and the global space $\mathcal H=\bigotimes_{i}\mathbb C^{d_i}$, whose computational basis is indexed by strings $x=(x_0,\dots,x_{n-1})$ with $x_i\in\{0,\dots,d_i-1\}$. For two distinct subsystems $a\ne b$ and an operator $V$ on $\mathcal H_a\otimes\mathcal H_b=\mathbb C^{d_a}\otimes\mathbb C^{d_b}$, the operator $V_{ab}$ acts as $V$ on the factors $a,b$ and as the identity on all others:
--   $$
--   \langle x|V_{ab}|y\rangle=\begin{cases}\langle x_a x_b|V|y_a y_b\rangle & \text{if } x_k=y_k \text{ for every } k\notin\{a,b\},\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   Up to the ordering of tensor factors this is $V\otimes I$. If $V$ is unitary (special unitary), so is $V_{ab}$.
--
--   These are the "operators on the combined Hilbert space $\mathcal H_a\otimes\mathcal H_b$" of Lemma 4.3.2.
--
--   **Formalization Note** Subsystems are indexed $0,\dots,n-1$ (`Fin n`), the book's $1,\dots,n$. The basis of $V$ is ordered (factor $a$, factor $b$). The definition is intended for $a\ne b$, which every use requires; for $a=b$ its value is not used.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Lemma 4.3.2, p.52 (PDF p.69); full tensor product subsystems, §4.1, p.46 (PDF p.63)

import Mathlib

namespace BaconThesis.Universality

/-- **An operator on two subsystems, tensored with the identity on the others.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§4.3.1, Lemma 4.3.2, p.52 (PDF p.69): "operators on the combined Hilbert space H_a ⊗ H_b", acting
on the global space `H = ⊗_{i=1}^n H_i` (see §4.1, p.46, PDF p.63, "full tensor product
subsystems").

The global space of `n` subsystems of dimensions `d 0, …, d (n-1)` is `ℂ^{∏ d_i}`, with basis
indexed by the strings `x = (x_0, …, x_{n-1})`, `x_i ∈ {0, …, d_i - 1}`. For subsystems `a ≠ b` and
an operator `V` on `H_a ⊗ H_b` (basis `(x_a, x_b)`), `embedPair d a b V` is `V ⊗ I` with `V` on the
factors `a, b` and the identity on all others:
`⟨x| embedPair d a b V |y⟩ = ⟨x_a x_b|V|y_a y_b⟩` if `x_k = y_k` for every `k ∉ {a, b}`, and `0`
otherwise.

**Formalization Note.** Subsystems are indexed `0, …, n-1` (`Fin n`), the book's `1, …, n`.
The index of `V` is the pair (factor `a`, factor `b`) in that order. The definition is meant for
`a ≠ b` (every use requires it); for `a = b` it is an unused junk value. -/
def embedPair {n : ℕ} (d : Fin n → ℕ) (a b : Fin n)
    (V : Matrix (Fin (d a) × Fin (d b)) (Fin (d a) × Fin (d b)) ℂ) :
    Matrix ((i : Fin n) → Fin (d i)) ((i : Fin n) → Fin (d i)) ℂ :=
  fun x y => if (∀ k, k ≠ a → k ≠ b → x k = y k) then V (x a, x b) (y a, y b) else 0

end BaconThesis.Universality


