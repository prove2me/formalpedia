-- Prove2me | Definitions.Def_FairShares_Supplement_nestedShare
-- name    : FairShares_Supplement_nestedShare
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:28:06.694018+00:00
-- url     : https://prove2.me/theorems/befcc424-11be-4003-be19-c014b48df670
-- title:
--   Nested share $NS_{n,q}$
-- statement:
--   Sort the goods by non-increasing singleton value. For a cut rank $k$ with $n-q<k\le m$, each of the $n$ bundles receives one consecutive interval from the prefix ranks and one interval from the suffix ranks, with suffix intervals assigned in reverse order; the first $n-q$ prefix intervals are singletons. The **nested share** $NS_{n,q}$ maximizes the minimum bundle value over all such cuts and partitions.
--
--   If $m<n$, its value is zero, as in the paper.
--
--   **Formalization Note** Intervals use half-open natural cut positions and may be empty. The value ranges over every compatible sorted permutation, making tie independence explicit.
-- source:
--   Babaioff & Feige, arXiv:2205.07519v1, Section 6.3, pp.21-22

import Mathlib

set_option autoImplicit false

namespace FairShares.Supplement

/-- **Nested share `NS_{n,q}`.**
Babaioff & Feige, arXiv:2205.07519v1, Section 6.3, pp.21--22.

For a cut `k` with `n-q < k ≤ m`, each bundle consists of one interval of prefix ranks below
`k` and one interval of suffix ranks at or above `k`.  Prefix intervals occur in increasing
bundle order and suffix intervals in reverse bundle order.  The first `n-q` prefix intervals
are the singleton ranks `0, …, n-q-1`.  The value is the ordinal maximin over the union of these
families over all legal `k`.

**Formalization Note.** The interval endpoints are natural cut positions and intervals are
half-open.  Empty intervals are allowed.  When `m < n`, the paper defines the value to be zero;
that case is explicit.  The results use `q = 3` and assume `3 ≤ n`. -/
noncomputable def nestedShare (n q m : ℕ) (v : Finset (Fin m) → ℝ) : ℝ := by
  classical
  exact
    if m < n then 0
    else
      ⨆ (σ : Equiv.Perm (Fin m))
          (_ : ∀ a b : Fin m, a.val < b.val → v {σ a} ≥ v {σ b})
          (P : Fin m → Fin n)
          (_ : P ∈ Finset.univ.filter (fun P : Fin m → Fin n =>
            ∃ k : ℕ, n - q < k ∧ k ≤ m ∧
              (∀ j : Fin n, ∃ a b : ℕ, a ≤ b ∧ b ≤ k ∧
                ∀ r : Fin m, r.val < k → (P r = j ↔ a ≤ r.val ∧ r.val < b)) ∧
              (∀ i j : Fin n, i.val < j.val → ∀ r s : Fin m,
                r.val < k → s.val < k → P r = i → P s = j → r.val < s.val) ∧
              (∀ j : Fin n, j.val < n - q → ∀ r : Fin m,
                r.val < k → (P r = j ↔ r.val = j.val)) ∧
              (∀ j : Fin n, ∃ a b : ℕ, k ≤ a ∧ a ≤ b ∧ b ≤ m ∧
                ∀ r : Fin m, k ≤ r.val → (P r = j ↔ a ≤ r.val ∧ r.val < b)) ∧
              (∀ i j : Fin n, i.val < j.val → ∀ r s : Fin m,
                k ≤ r.val → k ≤ s.val → P r = i → P s = j → s.val < r.val))),
        ⨅ i : Fin n, v (Finset.univ.filter (fun g => P (σ.symm g) = i))

end FairShares.Supplement


