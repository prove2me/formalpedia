-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_lpFeasible
-- name    : KallMayerSLP_Bonferroni_lpFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:05.046384+00:00
-- url     : https://prove2.me/theorems/7a3fe009-6dc3-4a62-a147-509bc88a33ee
-- title:
--   Feasible set of the linear program (3.14)
-- statement:
--   The feasible set of the linear program (3.14) consists of the vectors $(v_1,\dots,v_r)$ with
--   $$
--   \sum_{i=1}^r i\,v_i=S_1,\qquad \sum_{i=1}^r\binom{i}{2}v_i=S_2,\qquad v_i\ge0\quad(i=1,\dots,r).
--   $$
--
--   **Formalization Note** The book's $v_i$ is the coordinate of index $i-1$ of a vector `v : Fin r → ℝ`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.14), p.288 (PDF 297)

import Mathlib

namespace KallMayerSLP.Bonferroni

/-- The feasible set of the linear program (3.14) in the variables `v₁, …, v_r`:
`v₁ + 2 v₂ + ⋯ + r v_r = S₁`, `v₂ + ⋯ + (r choose 2) v_r = S₂`, `v_i ≥ 0`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.14), p.288 (PDF 297).

**Formalization Note.** The book's variable `v_i`, `i = 1, …, r`, is `v ⟨i - 1, _⟩ : ℝ`: the
coefficient of `v i` for `i : Fin r` is `i + 1` in the first equation and `(i + 1) choose 2` in the
second. The variable `v₀` of (3.13) does not occur in (3.14). -/
def lpFeasible (r : ℕ) (S₁ S₂ : ℝ) : Set (Fin r → ℝ) :=
  {v | (∑ i : Fin r, ((i : ℕ) + 1 : ℝ) * v i = S₁) ∧
      (∑ i : Fin r, (((i : ℕ) + 1).choose 2 : ℝ) * v i = S₂) ∧ ∀ i, 0 ≤ v i}

end KallMayerSLP.Bonferroni


