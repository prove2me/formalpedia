-- Prove2me | Definitions.Def_LawLocalComp_condSurvival
-- name    : LawLocalComp_condSurvival
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:12.665788+00:00
-- url     : https://prove2.me/theorems/b43527ca-5a0b-4e17-80b7-d56fbee4d593
-- title:
--   Conditional survival $S_i=\mathbb P(K\ge i\mid K>0)$
-- statement:
--   For masses $p_0,\dots,p_h$ of $K$,
--   $$S_i=\frac{\sum_{k=i}^h p_k}{\sum_{k=1}^h p_k},$$
--   which for $i\ge1$ is $\mathbb P(K\ge i\mid K>0)$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 8.1, p.14

import Mathlib

namespace LawLocalComp

/-- **Conditional survival `S_i = P(K ≥ i | K > 0)`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 8.1, p.14.

For masses `p 0, …, p h`, `condSurvival h p i = (∑_{k=i}^h p_k) / (∑_{k=1}^h p_k)`; for `i ≥ 1` this is
`P(K ≥ i | K > 0)`. -/
noncomputable def condSurvival (h : ℕ) (p : ℕ → ℚ) (i : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc i h, (p k : ℝ)) / ∑ k ∈ Finset.Icc 1 h, (p k : ℝ)

end LawLocalComp


