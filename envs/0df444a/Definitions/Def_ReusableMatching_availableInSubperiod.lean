-- Prove2me | Definitions.Def_ReusableMatching_availableInSubperiod
-- name    : ReusableMatching_availableInSubperiod
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:33:24.158177+00:00
-- url     : https://prove2.me/theorems/f3b2469f-37b7-4bfd-9442-80faa78bd21b
-- title:
--   The set $S_{p(j)}$ of resources available at some time of $p(j)$
-- statement:
--   Let $p(j)$ be the arrivals of the period $k(j)$ that come no later than $j$. Then
--
--   $$
--   S_{p(j)}=\bigcup_{t\in p(j)} S_t
--   $$
--
--   is the set of resources available at some arrival of $p(j)$. The analysis uses $S_{p(j)}(y^1,1)$, the set for the run $\mathrm{PR}(y^1,1)$.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, p.9

import Mathlib
import Definitions.Def_ReusableMatching_availableSet

namespace ReusableMatching

/-- **The set `S_{p(j)}` of resources available at some point of the sub-interval `p(j)`**
(arXiv:2110.07084v2, p.9): "Let `p(j) = {1, ⋯, j} ∩ k(j)` denote the sub-interval of period `k(j)`
that includes all arrivals prior to (and including) `j`. We let
`S_{p(j)}(y¹, 1) = ∪_{t ∈ p(j)} S_t(y¹, 1)` i.e., `S_{p(j)}(y¹, 1)` denotes the set of all
resources that are available at some point of time in interval `p(j)`."

`availableInSubperiod I β Y j` is the union of the available sets `S_t` (in the run with seed
vector `Y`) over the arrivals `t ≤ j` of the period of `j`; the paper's `S_{p(j)}(y¹, 1)` is
`availableInSubperiod I β (twoSeed I Y i j y¹ 1) j`. -/
noncomputable def availableInSubperiod {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
    (I : OBMRRInstance V n) (β : ℝ) (Y : Seeds V n) (j : Fin n) : Finset V := by
  classical
  exact Finset.univ.filter
    (fun v => ∃ t : Fin n, period I t = period I j ∧ t ≤ j ∧ v ∈ availableSet I β Y t)

end ReusableMatching


