-- Prove2me | Definitions.Def_RLCDiscrepancy_IsNormalized
-- name    : RLCDiscrepancy_IsNormalized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:14.973535+00:00
-- url     : https://prove2.me/theorems/05b808b6-f692-40c1-bd77-84d9e74bfbb8
-- title:
--   Normalized function on $\mathbb F_q^n$
-- statement:
--   Let $\mathbb F_q$ be a finite field with $q$ elements and $n\ge 0$. A function $f:\mathbb F_q^n\to\mathbb R$ is **normalized** if it is nonnegative and its expectation under the uniform distribution is $1$:
--
--   $$
--   f(x)\ge 0\ \text{ for all } x,\qquad \mathbb E_{x\sim\mathbb F_q^n}[f(x)]=q^{-n}\sum_{x\in\mathbb F_q^n} f(x)=1 .
--   $$
--
--   Normalized functions are the weighted tests against which the discrepancy of a code is measured; the normalized indicator $f_B=(q^n/|B|)\mathbf 1_B$ of a nonempty set $B$ recovers set-based discrepancy.
--
--   **Formalization Note** $\mathbb F_q^n$ is `Fin n → F` for a finite field `F` with $q$ = `Fintype.card F`; the expectation condition is written $\sum_x f(x)=q^n$.
-- source:
--   Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, Discrepancy for Random Linear Codes, arXiv:2606.24471 (PDF sha256 f03561c3…), §2.1, p.13

import Mathlib

namespace RLCDiscrepancy

/-- **Normalized function.** Doron, Leonov, Mosheiff, Navas, Resch, Ribeiro, *Discrepancy for Random Linear Codes*,
arXiv:2606.24471 (PDF sha256 f03561c3…), §2.1, p.13: "A nonnegative function f : F^n_q → R≥0 is
normalized if its expectation is 1, i.e., ∥f∥_1 = E_{x∼F^n_q}[f(x)] = 1."

**Formalization Note.** F^n_q is `Fin n → F` for a finite field `F`, with q = `Fintype.card F`
(every prime power arises this way). The function is real valued with an explicit
nonnegativity clause, and "expectation 1" is written as `∑ x, f x = q ^ n`. -/
def IsNormalized {F : Type*} [Fintype F] {n : ℕ} (f : (Fin n → F) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∑ x, f x = (Fintype.card F : ℝ) ^ n

end RLCDiscrepancy


