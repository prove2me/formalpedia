-- Prove2me | Definitions.Def_MulticastPoS_tailCount
-- name    : MulticastPoS_tailCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:35.825003+00:00
-- url     : https://prove2.me/theorems/a0365ac2-1731-44b6-9542-ab9187e0324c
-- title:
--   Copied-tail count $D_e$
-- statement:
--   Let $P$ be a profile and fix a representative selection $(p_g)_{g\in G^+}$. Every member of a nonresidual group $g$ copies the path $P_{p_g}$ of its representative, so the number of copied tails using edge $e$ is
--
--   $$
--   D_e=\sum_{g\in G^+} |g|\,\mathbf 1[e\in P_{p_g}].
--   $$
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 5.1, p.9

import Mathlib
import Definitions.Def_MulticastPoS_Selection

namespace MulticastPoS

/-- The copied-tail count `D_e` (Huang–Yuan, *An O(log log n) Upper Bound on the Price of
Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256
dd0e08d0…f6d4), Section 5.1, p.9): for a representative selection `σ`,
`D_e = Σ_{g ∈ G⁺} |g| · 1[e ∈ P_{p_g}]`, since all `|g|` members of `g` copy the path of its
representative `p_g = σ g`. -/
def tailCount {V ι : Type*} [DecidableEq V] [Fintype ι] [DecidableEq ι]
    {π : Finpartition (Finset.univ : Finset ι)} {g₀ : Option (Finset ι)}
    (P : ι → Finset (Sym2 V)) (σ : Selection π g₀) (e : Sym2 V) : ℕ :=
  ∑ g : ↥(nonresidual π g₀), if e ∈ P (σ g).1 then g.1.card else 0

end MulticastPoS


