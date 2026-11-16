-- Prove2me | Definitions.Def_RLCDiscrepancy_Supplement_IsErasureListRecoverable
-- name    : RLCDiscrepancy_Supplement_IsErasureListRecoverable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:48:12.815813+00:00
-- url     : https://prove2.me/theorems/5b4c498c-f286-4e11-b342-187d6b680496
-- title:
--   Erasure $(\zeta,\ell,L)$-list-recoverable code
-- statement:
--   A code $C\subseteq\mathbb F_q^n$ is **$(\zeta,\ell,L)$-list-recoverable** (with erasures) if for every collection of sets $S_1,\dots,S_n\subseteq\mathbb F_q$ such that $|S_i|\le\ell$ for at least $(1-\zeta)n$ of the indices $i$ (the other $S_i$ arbitrary),
--   $$
--   |(S_1\times\cdots\times S_n)\cap C|\le L.
--   $$
--   This is the notion of Theorem 2.14.
--
--   **Formalization Note** "At least $(1-\zeta)n$ of the $i$'s" compares the number of indices with $|S_i|\le\ell$ with the real number $(1-\zeta)n$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.13, p.18

import Mathlib

namespace RLCDiscrepancy.Supplement

/-- **(ζ, ℓ, L)-list-recoverable code, erasures** (Definition 2.13). Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), Definition 2.13, p.18:
"A code C ⊆ F^n_q is (ζ, ℓ, L)-list-recoverable if for every collection of sets
S_1, S_2, …, S_n ⊆ F_q with |S_i| ≤ ℓ for at least (1 − ζ)n of the i's it holds that
|(S_1 × S_2 × ⋯ × S_n) ∩ C| ≤ L."

**Formalization Note.** "At least (1 − ζ)n of the i's" compares the number of indices with
|S_i| ≤ ℓ with the real number (1 − ζ)n; the other S_i are arbitrary. The rectangle is
`Fintype.piFinset S`; a code is a `Finset (Fin n → F)`. -/
def IsErasureListRecoverable {F : Type*} [Fintype F] [DecidableEq F] {n : ℕ}
    (C : Finset (Fin n → F)) (ζ : ℝ) (ℓ L : ℕ) : Prop :=
  ∀ S : Fin n → Finset F,
    (1 - ζ) * n ≤ ((Finset.univ.filter (fun i => (S i).card ≤ ℓ)).card : ℝ) →
      (Fintype.piFinset S ∩ C).card ≤ L

end RLCDiscrepancy.Supplement


