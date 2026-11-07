-- Prove2me | Definitions.Def_PrivOptTest_searchRun
-- name    : PrivOptTest_searchRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:01.558406+00:00
-- url     : https://prove2.me/theorems/977d0b85-dc97-407d-a296-7c87b1ec4e5d
-- title:
--   The run of the private binary search and the bad event (8)
-- statement:
--   For a run of Algorithm 2 on blocks $A,B$ of size $k$, the search state $(L,H,\hat F(L),\hat F(H))$ after $i$ passes, the depth $\ell_i=\lfloor(L+H)/2\rfloor$ queried in pass $i$, and the estimate $\hat F(\ell_i)$ computed from that pass's two releases. The **bad event** (8) is
--   $$\mathcal B_{bs}=\{\exists\,t\le T:\ |F(\ell_t)-\hat F(\ell_t)|\ge\alpha/20\},$$
--   the $\ell_t$ being the adaptively chosen depths.
--
--   **Formalization Note** Passes are numbered $0,\dots,T-1$, and a pass counts only while the search is running ($H-L>1$).
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), proof of Theorem 3.12, Step 1, (8), p.21

import Mathlib
import Definitions.Def_PrivOptTest_algo2

open MeasureTheory

namespace PrivOptTest

/-- Message `j` of a run of Algorithm 2 (`algo2`, p.20 of arXiv:2611.03599, manuscript sha256
4ac94dcf…) on the blocks `A` (Alice) and `B` (Bob) and the coins `ω`. -/
noncomputable def algo2Msg (b k : ℕ) (ε β : ℝ) (A B : List ℕ) (ω : (algo2 b k ε β).Coins) (j : ℕ) :
    ℝ × (ℕ → ℝ) :=
  (algo2 b k ε β).msg A B ω j

/-- **The state `(L, H, F̂(L), F̂(H))` of the private binary search after `i` passes** (Algorithm 2,
lines 3–11, p.20; proof of Theorem 3.12, Step 1, p.21), read from the messages of the run. After
`T = ⌈log₂ b⌉` passes the search has ended (`H − L ≤ 1`). -/
noncomputable def searchRun (b k : ℕ) (ε β : ℝ) (A B : List ℕ) (ω : (algo2 b k ε β).Coins) (i : ℕ) :
    SearchState ℝ :=
  searchAt (realParams b k ε β) (algo2Msg b k ε β A B ω) i

/-- The depth `ℓ_i = ⌊(L + H)/2⌋` queried in pass `i` (line 5). -/
noncomputable def searchDepth (b k : ℕ) (ε β : ℝ) (A B : List ℕ) (ω : (algo2 b k ε β).Coins) (i : ℕ) : ℕ :=
  ((searchRun b k ε β A B ω i).L + (searchRun b k ε β A B ω i).H) / 2

/-- The estimate `F̂(ℓ_i) = n − A_PCF(S^{ℓ_i}_A, S^{ℓ_i}_B; ε₀, β₀)` computed in pass `i` (line 7),
from the two releases of that pass. -/
noncomputable def searchEstimate (b k : ℕ) (ε β : ℝ) (A B : List ℕ) (ω : (algo2 b k ε β).Coins) (i : ℕ) : ℝ :=
  fHat (realParams b k ε β) (searchDepth b k ε β A B ω i)
    (algo2Msg b k ε β A B ω (2 * i)).2 (algo2Msg b k ε β A B ω (2 * i + 1)).2

/-- **The bad event (8) of the proof of Theorem 3.12, p.21**:
`B_bs = {∃ t ≤ T : |F(ℓ_t) − F̂(ℓ_t)| ≥ α/20}`, where `ℓ_t` is the depth queried by the private binary
search in its `t`-th pass and `F(ℓ) = n − max_{p∈{0,1}^ℓ} min{|A^ℓ_p|, |B^ℓ_p|}` (Lemma 3.10).

**Formalization Note.** Passes are numbered `0, …, T − 1`. A pass is counted only while the search is
running (`H − L > 1`), since only then is a depth queried; `n` is the block size `k`. -/
def searchBad (b k : ℕ) (ε β : ℝ) (A B : List ℕ) : Set (algo2 b k ε β).Coins :=
  {ω | ∃ i < (realParams b k ε β).T,
    1 < (searchRun b k ε β A B ω i).H - (searchRun b k ε β A B ω i).L ∧
    (realParams b k ε β).α / 20 ≤
      |(escaped k b (searchDepth b k ε β A B ω i) A B : ℝ) - searchEstimate b k ε β A B ω i|}

end PrivOptTest


