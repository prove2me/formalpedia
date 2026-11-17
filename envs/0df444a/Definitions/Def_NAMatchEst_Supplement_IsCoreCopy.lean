-- Prove2me | Definitions.Def_NAMatchEst_Supplement_IsCoreCopy
-- name    : NAMatchEst_Supplement_IsCoreCopy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:38:42.444202+00:00
-- url     : https://prove2.me/theorems/cc4a81a1-7ec5-4bb9-b072-bbc9e94b65c3
-- title:
--   An input carrying a publicly labelled copy of a core
-- statement:
--   Let $F$ be a graph on the core vertex set $U^L\sqcup U^R$ and let $P_L,P_R$ be the public core label sets of an input on $n'$ labelled vertices. An input graph $G$ **carries a publicly labelled copy of $F$ with padded degree $t$** if there is an injective labelling $\sigma$ of the core vertices, sending $U^L$ into $P_L$ and $U^R$ into $P_R$, such that
--
--   1. two core labels $\sigma(c),\sigma(d)$ are adjacent in $G$ exactly when $c,d$ are adjacent in $F$, and
--   2. every core label has degree exactly $t$ in $G$.
--
--   Every repaired padded graph of §7.1 obtained from $F$, under every permitted public relabelling and every adjacency-list ordering (with the isolated vertices added), carries such a copy: padding and repairs keep every sparse edge, every other edge has a dummy endpoint, and every core vertex has total degree $t$. The predicate places no condition on the dummy and isolated vertices, so it defines a class containing the paper's repaired padded graphs. It is used to state Theorem 10.
--
--   **Formalization Note** The labelling is an embedding of the core vertex type into `Fin n'`; its image is all of $P_L\cup P_R$ when these have size $n/2$ each.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, pp.93–95 (PDF 97–99) and proof of Theorem 10, p.123 (PDF 127)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_Supplement_HINode

namespace NAMatchEst.Supplement

/-- The input `G` on `n'` labelled vertices **carries a publicly labelled copy of the core
`F` with padded degree `t`**, for the public core label sets `PL` (left) and `PR` (right):
there is a labelling `σ` of the core vertices, injective, sending left core vertices into `PL` and
right core vertices into `PR`, such that two core labels are adjacent in `G` exactly when the
corresponding core vertices are adjacent in `F`, and every core label has degree `t` in `G`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §7.1, pp.93–95
(PDF 97–99) and proof of Theorem 10, p.123 (PDF 127): "Fix four disjoint public label sets of sizes
n/2, n/2, t, t, corresponding to U^L, U^R, D^L, D^R. After all repairs, independently choose a
uniform bijection from each underlying vertex class to its prescribed label set." and "The public
label sets identify core and dummy vertices. Every padded core row has exactly t entries, and its
neighbors with core labels are exactly its neighbors in F."

**Formalization Note** Every repaired padded graph obtained from `F` (§7.1), under every permitted
public relabelling and every adjacency-list ordering, with the isolated vertices added, satisfies
this predicate: padding and repairs keep every sparse edge, all other edges have a dummy endpoint
(p.94–95, Lemma 7.1), and the degree table gives every core vertex total degree `t` (p.94). The
predicate does not constrain the dummy and isolated vertices, so the class it defines contains
the class of repaired padded graphs. -/
def IsCoreCopy {α r t n' : ℕ} (F : SimpleGraph (Bool × HINode α r × Fin t))
    (PL PR : Finset (Fin n')) (G : AdjList n') : Prop :=
  ∃ σ : (Bool × HINode α r × Fin t) ↪ Fin n',
    (∀ c, σ c ∈ (if c.1 then PR else PL)) ∧
    (∀ c d, G.toGraph.Adj (σ c) (σ d) ↔ F.Adj c d) ∧
    ∀ c, (G.adj (σ c)).length = t

end NAMatchEst.Supplement


