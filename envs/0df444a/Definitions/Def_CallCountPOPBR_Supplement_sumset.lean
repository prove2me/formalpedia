-- Prove2me | Definitions.Def_CallCountPOPBR_Supplement_sumset
-- name    : CallCountPOPBR_Supplement_sumset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:02:11.058563+00:00
-- url     : https://prove2.me/theorems/61f8cb87-3351-4a76-9632-da60088d6138
-- title:
--   Earlier-call-count sumsets $jS_n$
-- statement:
--   For an integer sequence $c=(c_n)$, natural numbers $n$ and $j$, the set $jS_n$ consists of all sums
--
--   $$
--   c_{k_1}+\cdots+c_{k_j},\qquad k_1,\ldots,k_j<n,
--   $$
--
--   with repetitions permitted. For $j=0$ the only sum is zero. This is the sumset used in the bounded-branching realisability criterion.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Section 5.1, p.9

import Mathlib

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **The sumset `jS_n`** (§5.1, p.9). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), §5.1, p.9: "Define S_n = {c_0, …, c_{n−1}} and the
sumsets jS_n = {s_1 + ⋯ + s_j : s_i ∈ S_n}, with 0S_n = {0}."

`sumset c n j` is the set of sums `c_{k_1} + ⋯ + c_{k_j}` with `k_1, …, k_j < n` (repetitions
allowed); for `j = 0` it is `{0}`.

**Formalization Note.** Choosing elements `s_i ∈ S_n` is choosing indices `k_i < n` with
`s_i = c_{k_i}`; the indices form a list of length `j`. -/
def sumset (c : ℕ → ℤ) (n j : ℕ) : Set ℤ :=
  {x | ∃ l : List ℕ, l.length = j ∧ (∀ k ∈ l, k < n) ∧ x = (l.map c).sum}

end CallCountPOPBR.Supplement


