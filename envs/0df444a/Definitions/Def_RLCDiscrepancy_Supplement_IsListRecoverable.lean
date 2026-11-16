-- Prove2me | Definitions.Def_RLCDiscrepancy_Supplement_IsListRecoverable
-- name    : RLCDiscrepancy_Supplement_IsListRecoverable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:47:56.383197+00:00
-- url     : https://prove2.me/theorems/a32c1c46-a33c-4bdb-a921-bb58cd90c23f
-- title:
--   Zero-error $(\ell,L)$-list-recoverable code
-- statement:
--   A code $C\subseteq\mathbb F_q^n$ is **$(\ell,L)$-list-recoverable** (zero-error) if for every collection of sets $S_1,\dots,S_n\subseteq\mathbb F_q$ with $|S_i|\le\ell$ for all $i\in[n]$,
--   $$
--   |(S_1\times\cdots\times S_n)\cap C|\le L.
--   $$
--   $\ell$ is the input list size and $L$ the output list size. This is the notion of Theorem 2.12.
--
--   **Formalization Note** The combinatorial rectangle $S_1\times\cdots\times S_n=\{x:\ x_i\in S_i\ \forall i\}$ is Mathlib's `Fintype.piFinset`.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.11, p.17

import Mathlib

namespace RLCDiscrepancy.Supplement

/-- **Zero-error (ℓ, L)-list-recoverable code** (Definition 2.11). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.11, p.17:
"A code C ⊆ F^n_q is (ℓ, L)-list-recoverable if, for every collection of sets
S_1, S_2, …, S_n ⊆ F_q with |S_i| ≤ ℓ for all i ∈ [n], |(S_1 × S_2 × ⋯ × S_n) ∩ C| ≤ L."

**Formalization Note.** The combinatorial rectangle S_1 × ⋯ × S_n = {x : ∀ i, x_i ∈ S_i} is
Mathlib's `Fintype.piFinset S`; a code is a `Finset (Fin n → F)`. -/
def IsListRecoverable {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ} (C : Finset (Fin n → F))
    (ℓ L : ℕ) : Prop :=
  ∀ S : Fin n → Finset F, (∀ i, (S i).card ≤ ℓ) → (Fintype.piFinset S ∩ C).card ≤ L

end RLCDiscrepancy.Supplement


