-- Prove2me | Definitions.Def_MetricMSO_ctw
-- name    : MetricMSO_ctw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:30.174343+00:00
-- url     : https://prove2.me/theorems/17ea86fe-94cc-47e2-85d2-965e4ce21b4b
-- title:
--   Bag-connected treewidth $\mathrm{ctw}(G)$
-- statement:
--   A tree decomposition of $G$ has width $\max_t|B_t|-1$. It is **bag-connected** if every nonempty bag induces a connected subgraph of $G$, and the **bag-connected treewidth** $\mathrm{ctw}(G)$ is the minimum width of such a decomposition.
--
--   With the treewidth $\mathrm{tw}(G)$ (the published `PlantedSubgraphLD.tw`, the minimum width of any tree decomposition), these are the two width parameters of part (i) of the goal.
--
--   **Formalization Note** Built on the published `IsTreeDecomposition`. Bags may be empty, so decompositions of the components can be joined through empty bags. Hence the direct minimum equals the page's maximum over the connected components, and every finite graph has a bag-connected decomposition. The graph with no vertex gets the value $0$.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §2.3, p.13 (PDF 15)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition

namespace MetricMSO

open RobertsonSeymour1986.GM5 (IsTreeDecomposition)

/-- **Bag-connected treewidth `ctw(G)`.**

§2.3, p.13 (PDF 15): "We call a tree decomposition bag-connected if every nonempty bag induces a
connected subgraph of G, and we write ctw(G) for the minimum width of such a decomposition. …
For disconnected graphs, we obtain both parameters by taking the maximum over the connected
components."

`ctw G` is the least `k` such that `G` has a tree decomposition over a finite tree with bags of at
most `k + 1` vertices in which every nonempty bag induces a connected subgraph of `G`.

**Formalization Note** Empty bags are allowed (the published `IsTreeDecomposition` allows them), so
the decompositions of the components can be joined through empty bags. Hence the direct definition
equals the page's maximum over the components, and every finite graph has a bag-connected
decomposition. The graph with no vertex gets `0` (instead of `−1`). Treewidth `tw(G)` is the
published `PlantedSubgraphLD.tw` (`sInf {w | TreewidthLE G w}`), the same object with bags not
required to be connected. -/
noncomputable def ctw {V : Type} [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ (T : Type) (_ : Fintype T) (t : SimpleGraph T) (X : T → Finset V),
    IsTreeDecomposition G t X ∧ (∀ s, (X s).card ≤ k + 1) ∧
    ∀ s, (X s).Nonempty → (G.induce ((X s : Finset V) : Set V)).Connected}

end MetricMSO


