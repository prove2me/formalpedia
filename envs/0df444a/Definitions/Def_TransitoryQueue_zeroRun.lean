-- Prove2me | Definitions.Def_TransitoryQueue_zeroRun
-- name    : TransitoryQueue_zeroRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:22.000775+00:00
-- url     : https://prove2.me/theorems/99b42131-79c0-4a44-9e3b-5b61844885a2
-- title:
--   Longest run of zero service requirements
-- statement:
--   For $V_1,\dots,V_n$, $R$ is the length of the longest run of consecutive zeros: the largest $k$ such that $V_{i+1}=\dots=V_{i+k}=0$ for some $i$ (and $R=0$ if no $V_i$ is zero).
--
--   It measures how far (117)–(118) are off when the service law has an atom at $0$, which Assumption 2.7 allows.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, used in the correction of eqs. (117)–(118), p.38

import Mathlib

namespace TransitoryQueue

open Classical in
/-- The length of the longest run of consecutive zero service requirements in
`V_1, …, V_n`: the largest `k` such that `V_{i+1} = ⋯ = V_{i+k} = 0` for some `i`.
Used in the correction of (117)–(118) of Chakraborty and Honnappa, *Strong Embeddings for
Transitory Queueing Models*, arXiv:1906.06740v1, p.38, which fail when `V_i = 0` occurs.

**Formalization Note** 0-based indices `j : Fin n`; `k = 0` always qualifies. -/
noncomputable def zeroRun {n : ℕ} (V : Fin n → ℝ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun k => ∃ i : ℕ, i + k ≤ n ∧
    ∀ j : Fin n, i ≤ j.val → j.val < i + k → V j = 0)).sup id

end TransitoryQueue


