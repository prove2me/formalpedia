-- Prove2me | Definitions.Def_LogStarBinPacking_fiveClassOutput
-- name    : LogStarBinPacking_fiveClassOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:30:22.661014+00:00
-- url     : https://prove2.me/theorems/1e6aa425-856b-4d7d-a4b4-2b3e57ab1fc3
-- title:
--   The output of the algorithm $A$ of [OAI26], grouped into five classes
-- statement:
--   For a gap parameter $c\ge0$, a parameter $\rho$ and an input $(G,k)$ (a simple graph with at least one edge and $0\le k\le|V(G)|$), the algorithm $A$ of [OAI26] produces an integer $N\ge1$ and a bin packing instance $I$ with a partition $I=I_1\,\dot\cup\cdots\dot\cup\,I_5$.
--
--   This definition records that output as an instance with five classes: $N$ is the published bin bound of the construction, and the classes are the items of the five published roles (in the order x, anchor, global, local, flag), each item given by its published raw size $(p,q)$ meaning $p/q$.
--
--   It is the object Proposition 3.1 and Lemma 3.3 speak about, and the input of Lemma 2.2 in the proof of Theorem 1.1.
--
--   **Formalization Note** $A$ is the published construction `reductionInventory c ρ G k` of the `OAIQ082C*` definitions; its published machine `graphPackingComputation c ρ` outputs the same items as one unlabelled list (`graphPackingOutput`). Here the items are grouped by their published role, keeping the published order within a class. The classes $I_1,\dots,I_5$ are read as the five roles: each published integral packing builds every bin from exactly one item per role.
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Proposition 3.1, p.12

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C014
import Definitions.Def_LogStarBinPacking_FiveClassRaw

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- The order of the five classes: the published roles `x`, `anchor`, `global`, `local`, `flag`. -/
def roleOrder : List Role := [.x, .anchor, .«global», .«local», .flag]

/-- **The output of the algorithm `A` of [OAI26], grouped into its five classes.** Doron-Arad,
*Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript
(sha256 1d88425d…), Proposition 3.1, p.12: on input `(G, k, c)` the algorithm `A` produces an
integer `N ≥ 1` and a bin packing instance `I` with a partition `I = I₁ ∪̇ ⋯ ∪̇ I₅`.

**Formalization Note** `A` is the published construction of [OAI26] (namespace
`OAI.BinPackingGap`, bundle `OAIQ082C014`) at the parameter `ρ`: `N` is
`(reductionInventory c ρ G k).B` (= `reductionBinBound c ρ G k`) and the items are its published
raw items `itemRawPair` (pairs `(p, q)` for the size `p/q`). The published machine
`graphPackingComputation c ρ` outputs these items as one list (`graphPackingOutput`); here they are
grouped by their published role, in the order `roleOrder`, and the classes `I₁, …, I₅` are the five
roles. Within a class the items keep the order of the published `itemList`. -/
noncomputable def fiveClassOutput (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) : FiveClassRaw :=
  let D := reductionInventory c ρ x.graph x.k
  (D.B, roleOrder.map fun r => (D.itemList.filter fun i => D.itemRole i = r).map D.itemRawPair)

end LogStarBinPacking


