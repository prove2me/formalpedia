-- Prove2me | Definitions.Def_DecDynMatch_busRank
-- name    : DecDynMatch_busRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:20.340963+00:00
-- url     : https://prove2.me/theorems/bdab50cc-b246-4519-935a-d155d3ebc840
-- title:
--   BUS rank, offsets $\delta_i$ and the root
-- statement:
--   In round $t$, the **root** is the active player most preferred by BUS (arm $0$). In the analysis, the players of a fixed market are labeled $1,\dots,n$ from most to least preferred by BUS, and player $i$ has offset $\delta_i=2(i-1)$.
--
--   Here $\operatorname{busRank}_t(i)$ is the number of active players that BUS prefers to $i$, so the label of $i$ is $\operatorname{busRank}_t(i)+1$ and $\delta_i=2\operatorname{busRank}_t(i)$; the root is the player of BUS rank $0$.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §3.1, p.7; App. A.1, p.14

import Mathlib
import Definitions.Def_DecDynMatch_Instance

namespace DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- **BUS rank and root.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*,
arXiv:2610.41912 (held version, sha256 6a27277e…), §3.1, p.7 ("In a given round, call the active
player most preferred by BUS the root") and App. A.1, p.14 ("we have n ≤ K players, labeled
1, …, n from most to least preferred by BUS. Player 1 is the root … define δᵢ = 2(i − 1)").

`busRank I t i` is the number of active players at round `t` that BUS (arm 0) prefers to `i`;
it is the paper's label minus one, so `δᵢ = 2 * busRank I t i`. -/
noncomputable def busRank (I : Instance K ι) (t : ℕ) (i : ι) : ℕ :=
  ((active I t).filter (fun j => I.π (bus I) i < I.π (bus I) j)).card

/-- `i` is the root at round `t`: the active player most preferred by BUS. -/
def IsRoot (I : Instance K ι) (t : ℕ) (i : ι) : Prop :=
  i ∈ active I t ∧ busRank I t i = 0

end DecDynMatch


