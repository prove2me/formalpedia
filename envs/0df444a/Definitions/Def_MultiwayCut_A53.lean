-- Prove2me | Definitions.Def_MultiwayCut_A53
-- name    : MultiwayCut_A53
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:05.170241+00:00
-- url     : https://prove2.me/theorems/0cc80945-6732-457c-b00b-38accbee7580
-- title:
--   The matrix $A$ of (5.3)
-- statement:
--   **The matrix (5.3)** (§5.1, p.8). The symmetric matrix $A=(a_{ij})$ with
--   $$a_{11}=1,\quad a_{1j}=a_{j1}=\tfrac5{27}\ (j\ge2),\quad a_{22}=a_{33}=\tfrac19,\quad a_{44}=-\tfrac5{18},$$
--   $a_{ij}=\tfrac5{108}$ for $i\ne j$, $i,j\ge2$, $\min(i,j)\in\{2,3\}$, and all other entries $0$: "the (symmetric) matrix $A$ has non-zero entries only in the first 3 rows (and columns) and in coordinate $a_{44}$".
--
--   Together with $p=121/229$ it defines the 297/229-approximation algorithm of Theorem 1.2.
--
--   **Formalization Note** Indices are 0-based (`A53 k 0 0` is $a_{11}$, `A53 k 3 3` is $a_{44}$). The paper prints the pattern with "…" for a general $k$; `A53 k` is defined for every $k$ by the entry formula, i.e. the top-left $k\times k$ block of the printed pattern.
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, §5.1, (5.3), p.8

import Mathlib

namespace MultiwayCut

/-- **The matrix (5.3)**, Buchbinder, Schwartz & Weizman, *Simplex Transformations and the
Multiway Cut Problem*, manuscript of Nov. 1, 2016, §5.1, p.8 (1-based entries):
`a₁₁ = 1`; `a₁ⱼ = aⱼ₁ = 5/27` for `j ≥ 2`; `a₂₂ = a₃₃ = 1/9`; `a_ij = 5/108` for `i ≠ j`,
`i, j ≥ 2`, `min(i, j) ∈ {2, 3}`; `a₄₄ = −5/18`; every other entry `0`. "The (symmetric) matrix A
has non-zero entries only in the first 3 rows (and columns) and in coordinate a44."

**Formalization Note.** 0-based indices (`A53 k 0 0` is `a₁₁`, `A53 k 3 3` is `a₄₄`). The
paper prints the pattern for a general `k` with "…"; for every `k` the matrix is defined by the
entry formula, i.e. the top-left `k × k` block of the printed pattern. -/
noncomputable def A53 (k : ℕ) : Matrix (Fin k) (Fin k) ℝ := fun m n =>
  if m.val = 0 ∧ n.val = 0 then 1
  else if m.val = 0 ∨ n.val = 0 then 5 / 27
  else if m = n ∧ (m.val = 1 ∨ m.val = 2) then 1 / 9
  else if m.val = 3 ∧ n.val = 3 then -5 / 18
  else if m.val ≤ 2 ∨ n.val ≤ 2 then 5 / 108
  else 0

end MultiwayCut


