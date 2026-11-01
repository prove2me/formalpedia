-- Prove2me | Definitions.Def_AndOrSched_cand
-- name    : AndOrSched_cand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:50.859368+00:00
-- url     : https://prove2.me/theorems/7283f9cb-aff6-40e1-a553-2ad7bb4c2133
-- title:
--   Candidate values of $\beta$
-- statement:
--   As $\beta$ increases, the key of $a\in A$ changes only at the values $\Delta\sum_{s\le t}x_{as}$ and the key of $b\in B$ only at the values $\sum_{s\le t}x_{bs}$. The candidate set is
--   $$\{1\}\cup\Bigl(\{\Delta\textstyle\sum_{s\le t}x_{as}\}\cup\{\textstyle\sum_{s\le t}x_{bs}\}\Bigr)\cap(0,1],\qquad t\in[M],$$
--   with $M=T$ for LP (1) and $M=L$ for LP (5). The derandomized algorithm evaluates the $\beta$-schedule for every candidate and keeps the best.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.8, Lemma 2 and "List all possible schedules that occur as β goes from 0 to 1, and pick the best one"; p.10

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_delta
import Definitions.Def_AndOrSched_cum
open scoped Classical NNReal

namespace AndOrSched

/-- The candidate values of `β` for the derandomization (Happach, Schulz, arXiv:2001.07011v1, §2, p.8, Lemma 2 and its proof,
"List all possible schedules that occur as β goes from 0 to 1, and pick the best one"; p.10 for
Algorithm 2). As `β` grows, the key of `a ∈ A` changes only at the values `Δ · Σ_{s≤t} x_{as}` and
the key of `b ∈ B` only at the values `Σ_{s≤t} x_{bs}`, `t ∈ [M]`. The candidates are these values in
`(0, 1]`, together with `1`.

**Formalization Note** `M` is the number of time slots (`T` for LP (1)) or intervals (`L` for LP (5)).
The derandomized algorithm computes the `β`-schedule for every candidate and returns the best one;
its cost is at most that of the `β`-schedule of any single candidate. -/
noncomputable def cand (I : Instance) (x : I.N → ℕ → ℝ) (M : ℕ) : Finset ℝ :=
  insert 1 ((((Finset.univ ×ˢ Finset.Icc 1 M).image
      fun q : I.A × ℕ => (delta I : ℝ) * cum x (Sum.inl q.1) q.2) ∪
    ((Finset.univ ×ˢ Finset.Icc 1 M).image
      fun q : I.B × ℕ => cum x (Sum.inr q.1) q.2)).filter fun β => 0 < β ∧ β ≤ 1)

end AndOrSched


