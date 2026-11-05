-- Prove2me | Definitions.Def_ReusableMatching_ThreeRegimes
-- name    : ReusableMatching_ThreeRegimes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:34:32.190892+00:00
-- url     : https://prove2.me/theorems/a89eec72-062f-4433-aaf6-952bf60863e4
-- title:
--   The three regimes of $y^1$ in Lemma 7
-- statement:
--   Fix an edge $(i,j)$ and the seeds $Y_{-i,j}$. Values $z_1,z_2\in[0,1]$ **cut $y^1$ into the three regimes of Lemma 7** if, in the run $\mathrm{PR}(y^1,1)$:
--
--   1. for every $y^1\in(z_2,1]$, $i\in S_{p(j)}(y^1,1)$ and $i$ is not matched in period $k(j)-1$;
--   2. for every $y^1\in(z_1,z_2)$, $i\notin S_{p(j)}(y^1,1)$ and $i$ is matched in period $k(j)-1$;
--   3. for every $y^1\in[0,z_1)$, $i\in S_{p(j)}(y^1,1)$ and $i$ is matched in period $k(j)-1$.
--
--   Lemma 7 asserts that such $z_1\le z_2$ exist; Lemma 8 is stated for them.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, Lemma 7, pp.10–11

import Mathlib
import Definitions.Def_ReusableMatching_availableInSubperiod
import Definitions.Def_ReusableMatching_MatchedInPrevPeriod
import Definitions.Def_ReusableMatching_twoSeed

namespace ReusableMatching

/-- **The three regimes of `y¹` cut out by `z1 ≤ z2`** (arXiv:2110.07084v2, Lemma 7, pp.10–11),
for the edge `(i, j)` and the seeds `Y_{−i,j}` (all coordinates of `Y` except `(i, k(j) − 1)` and
`(i, k(j))`). In the run `PR(y¹, 1)`:

a) for every `y¹ ∈ (z2, 1]`, `i ∈ S_{p(j)}(y¹, 1)` and `i` is not matched to any arrival in period
   `k(j) − 1`;
b) for every `y¹ ∈ (z1, z2)`, `i ∉ S_{p(j)}(y¹, 1)` and `i` is matched to some arrival in period
   `k(j) − 1`;
c) for every `y¹ ∈ [0, z1)`, `i ∈ S_{p(j)}(y¹, 1)` and `i` is matched to some arrival in period
   `k(j) − 1`.

Lemma 7 asserts that such `z1 ≤ z2` exist, and Lemma 8 is stated for them.

**Formalization Note.** `z1, z2, y¹` range over `unitInterval`, so `y¹ ∈ (z2, 1]` is `z2 < y¹` and
`y¹ ∈ [0, z1)` is `y¹ < z1`. "Matched in period `k(j) − 1`" is about the run `PR(y¹, 1)`, as the
paper's `S_{p(j)}(y¹, 1)` (that period does not read `y²`). -/
def ThreeRegimes {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (i : V) (j : Fin n)
    (z1 z2 : unitInterval) : Prop :=
  (∀ y1 : unitInterval, z2 < y1 →
      i ∈ availableInSubperiod I β (twoSeed I Y i j y1 1) j ∧
      ¬ MatchedInPrevPeriod I β (twoSeed I Y i j y1 1) i j) ∧
  (∀ y1 : unitInterval, z1 < y1 → y1 < z2 →
      i ∉ availableInSubperiod I β (twoSeed I Y i j y1 1) j ∧
      MatchedInPrevPeriod I β (twoSeed I Y i j y1 1) i j) ∧
  (∀ y1 : unitInterval, y1 < z1 →
      i ∈ availableInSubperiod I β (twoSeed I Y i j y1 1) j ∧
      MatchedInPrevPeriod I β (twoSeed I Y i j y1 1) i j)

end ReusableMatching


