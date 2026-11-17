-- Prove2me | Definitions.Def_GSRandomOrder_Supplement_cn
-- name    : GSRandomOrder_Supplement_cn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:07:58.297602+00:00
-- url     : https://prove2.me/theorems/8eae8e0f-9ab4-40d8-85bf-92c57110af10
-- title:
--   The cutoff constant $c_n(s)=\frac sn\sum_{j=s}^{n-1}\frac1j$
-- statement:
--   For a cutoff $s\in\{1,\dots,n-1\}$ put $a_k=s/(k-1)$ for $k>s$ and
--   $$
--   c_n(s)=\frac1n\sum_{k=s+1}^n a_k=\frac sn\sum_{j=s}^{n-1}\frac1j .
--   $$
--   It is the probability with which the classical cutoff rule selects the best of $n$ candidates in random order, and the welfare guarantee of Theorems 4.5 and E.1. Some cutoff gives $c_n(s)\ge1/e$ (Lemma D.1).
--
--   **Formalization Note** The second form is used, with $\{s,\dots,n-1\}$ as `Finset.Ico s n`.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §4.3, p.15, "Prefix proposals"; Theorem E.1, p.32

import Mathlib

set_option autoImplicit false

namespace GSRandomOrder.Supplement

/-- **The cutoff constant** `c_n(s)` (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare
in Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §4.3, p.15, "Prefix
proposals"; Theorem E.1, p.32): with `a_k = s/(k − 1)` for `k > s`,
`c_n(s) = (1/n) Σ_{k=s+1}^n a_k = (s/n) Σ_{j=s}^{n−1} 1/j`.

**Formalization Note.** The second printed form is used: `Finset.Ico s n` is `{s, …, n − 1}`. The
constant is used for cutoffs `s ∈ {1, …, n − 1}`, where no division by zero occurs. -/
noncomputable def cn (n s : ℕ) : ℝ :=
  (s : ℝ) / n * ∑ j ∈ Finset.Ico s n, (1 : ℝ) / j

end GSRandomOrder.Supplement


