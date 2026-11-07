-- Prove2me | Definitions.Def_SmoothedNash_R
-- name    : SmoothedNash_R
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:41.002639+00:00
-- url     : https://prove2.me/theorems/b167a1dd-4058-430b-92cd-3f65a441662b
-- title:
--   Dimension $R = \sum_i (|A_i| - 1)$ of $K_A$
-- statement:
--   For a support profile $A = (A_1, \dots, A_m)$,
--   $$
--   R := \sum_{i=1}^m \bigl(|A_i| - 1\bigr),
--   $$
--   the dimension of the product of simplices $K_A$. It governs the size of the grids ($|N_t(A)| \le C^{mn} 2^{tR}$), the number of children of a grid point ($\le 2^R$) and the survival probability $M^{mn}(2\tau)^R$ of Lemma 2.8.
--
--   **Formalization Note** Computed in $\mathbb N$; each $|A_i| \ge 1$, so the subtraction is exact.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), §2.1.1, p.13

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile

namespace SmoothedNash

/-- The dimension `R := Σ_{i=1}^m (|A_i| − 1)` of `K_A` (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), §2.1.1, p.13).

**Formalization Note** Computed in `ℕ`; the truncated subtraction is exact because every `A_i`
is nonempty. -/
def R {m n : ℕ} (A : SupportProfile m n) : ℕ :=
  ∑ i, ((A.1 i).card - 1)

end SmoothedNash


