-- Prove2me | Definitions.Def_SecondBestBT_Supplement_IsAdmissible
-- name    : SecondBestBT_Supplement_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:32:54.690192+00:00
-- url     : https://prove2.me/theorems/cee7888c-0da7-44ee-9305-5e165c498a55
-- title:
--   Admissible global ratio vector $(0,r_1,\dots,r_m)$
-- statement:
--   A finite global ratio vector $v=(0,r_1,\dots,r_m)$ with entries in $[0,\infty]$ is **admissible** (for a fixed $\alpha\ge0$) if
--
--   1. its first entry is $0$;
--   2. its positive finite ratios form an initial segment $r_1,\dots,r_n$ ($0\le n\le m$), and the remaining ratios $r_{n+1},\dots,r_m$ are infinite;
--   3. $(1+\alpha)i+\alpha r_i$ is weakly increasing in $i$ on the finite segment $0\le i\le n$ (with $r_0=0$).
--
--   Admissible vectors are exactly the ratio vectors of $\alpha$-weakly regular sellers with full support on an initial integer interval, and they are the inputs of the state-transition procedure ALG2.
--
--   **Formalization Note** The vector is a list whose head is $0$; $n$ is the index of the last finite entry.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 5.1, p.16

import Mathlib

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- An **admissible** finite global ratio vector `v = (0, r_1, …, r_m)` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 5.1,
p.16): its first entry is `0`, its positive finite ratios form an initial segment
`r_1, …, r_n`, its remaining ratios `r_{n+1}, …, r_m` are infinite, and `(1 + α) i + α r_i` is
weakly increasing in `i` on the finite segment `0 ≤ i ≤ n` (index `0`, with `r_0 = 0`, included).

**Formalization Note** The vector is a list `v` with `v[0] = 0`; `n` is the index of the last
finite entry (`n = 0` when every `r_i`, `i ≥ 1`, is infinite). Out-of-range defaults of
`List.getD` are never read: every index used is `< v.length`. -/
def IsAdmissible (α : ℝ) (v : List ℝ≥0∞) : Prop :=
  v.head? = some 0 ∧
  ∃ n, n < v.length ∧
    (∀ i, 1 ≤ i → i ≤ n → 0 < v.getD i ⊤ ∧ v.getD i ⊤ ≠ ⊤) ∧
    (∀ i, n < i → i < v.length → v.getD i 0 = ⊤) ∧
    ∀ i j, i ≤ j → j ≤ n →
      (1 + α) * i + α * (v.getD i 0).toReal ≤ (1 + α) * j + α * (v.getD j 0).toReal

end SecondBestBT.Supplement


