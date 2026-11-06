-- Prove2me | Definitions.Def_LawLocalComp_IsIFRSeq
-- name    : LawLocalComp_IsIFRSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:09:58.75947+00:00
-- url     : https://prove2.me/theorems/9c8cc19a-b52f-465d-984e-ed37aa435976
-- title:
--   Nonincreasing conditional survival ratios
-- statement:
--   For masses $p_0,\dots,p_h$ let $T_i=\sum_{k=i}^h p_k$, so that $S_i=\mathbb P(K\ge i\mid K>0)=T_i/T_1$ for $i\ge1$. The positive conditional survival ratios $S_{i+1}/S_i$ ($1\le i<h$) are **nonincreasing** when
--   $$T_{i+2}\,T_i\le T_{i+1}^2\qquad(1\le i,\ i+2\le h).$$
--   This is the conditional-IFR (increasing failure rate) condition of Corollary 8.2, checked by rational survival comparisons.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Corollary 8.2, p.16; Lemma 8.1, p.14

import Mathlib

namespace LawLocalComp

/-- **Nonincreasing positive conditional survival ratios.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Corollary 8.2, p.16 ("whose positive conditional survival ratios Si+1/Si are nonincreasing";
"Membership uses rational survival comparisons"), with `S_i = P(K ≥ i | K > 0)` (Lemma 8.1, p.14).

With tail sums `T_i = ∑_{k = i}^h p_k`, `S_i = T_i / T_1`, and the positive ratios are
`S_{i+1}/S_i` for `1 ≤ i < h`. `IsIFRSeq h p` says they are nonincreasing:
`T_{i+2} T_i ≤ T_{i+1}²` for `1 ≤ i` and `i + 2 ≤ h`. -/
def IsIFRSeq (h : ℕ) (p : ℕ → ℚ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i + 2 ≤ h →
    (∑ k ∈ Finset.Icc (i + 2) h, p k) * (∑ k ∈ Finset.Icc i h, p k) ≤ (∑ k ∈ Finset.Icc (i + 1) h, p k) ^ 2

end LawLocalComp


