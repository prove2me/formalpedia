-- Prove2me | Definitions.Def_DisruptReroute_Resil_Diversification
-- name    : DisruptReroute_Resil_Diversification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:42.478776+00:00
-- url     : https://prove2.me/theorems/de94b397-b181-42a0-a56b-a82c933ba01d
-- title:
--   Definition 5.3 — buyer and supplier diversification
-- statement:
--   Let $A$ and $B$ be tiered order networks on the same firms and goods, with the same tier assignment. Network $B$ is more diversified than $A$ when, for every firm $i$: total incoming and outgoing orders agree; its supplier and buyer sets in $A$ are contained in those in $B$; and a strict expansion replaces each old order by quantities no larger than every old order on that side. If a neighbor set is unchanged, the corresponding order quantities agree individually.
--
--   For the supplier side the compared quantities are orders of the good bought by $i$, namely good $m_i-1$; for the buyer side they are orders of the good supplied by $i$, namely good $m_i$.
--
--   This is the paper's joint buyer and supplier diversification condition, used in the cost comparison.
--
--   **Formalization Note** Definition 5.3 prints $m_i$ on the supplier side, although §5.2 defines that good as $m_i-1$. The formalization corrects that index. Its minimum–maximum clauses are expressed as pairwise inequalities, which avoid empty-set extrema.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), p. 27, Definition 5.3

import Mathlib
import Definitions.Def_DisruptReroute_Resil_OrderNetwork
noncomputable section

namespace DisruptReroute.Resil

/-- Definition 5.3 for a pair of tiered networks sharing a tier map. -/
def MoreDiversified {N M : ℕ} (A B : OrderNetwork N M)
    (tier : Fin N → ℕ) : Prop :=
  ∀ i : Fin N,
    (∑ j ∈ suppliers A tier i, A.order (tier i - 1) j i) =
      (∑ j ∈ suppliers B tier i, B.order (tier i - 1) j i) ∧
    (∑ j ∈ buyers A tier i, A.order (tier i) i j) =
      (∑ j ∈ buyers B tier i, B.order (tier i) i j) ∧
    suppliers A tier i ⊆ suppliers B tier i ∧
    buyers A tier i ⊆ buyers B tier i ∧
    (if suppliers A tier i ⊂ suppliers B tier i then
       ∀ j ∈ suppliers A tier i, ∀ k ∈ suppliers B tier i,
         B.order (tier i - 1) k i ≤ A.order (tier i - 1) j i
     else
       ∀ j ∈ suppliers A tier i,
         A.order (tier i - 1) j i = B.order (tier i - 1) j i) ∧
    (if buyers A tier i ⊂ buyers B tier i then
       ∀ j ∈ buyers A tier i, ∀ k ∈ buyers B tier i,
         B.order (tier i) i k ≤ A.order (tier i) i j
     else
       ∀ j ∈ buyers A tier i,
         A.order (tier i) i j = B.order (tier i) i j)

end DisruptReroute.Resil


