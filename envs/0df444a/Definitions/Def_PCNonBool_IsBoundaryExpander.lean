-- Prove2me | Definitions.Def_PCNonBool_IsBoundaryExpander
-- name    : PCNonBool_IsBoundaryExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:39.036215+00:00
-- url     : https://prove2.me/theorems/45cde734-a565-4624-86e3-bcb96e7f952a
-- title:
--   $(s,\Delta,c)$-boundary expander
-- statement:
--   A bipartite graph $G=(U\sqcup V,E)$ is an **$(s,\Delta,c)$-boundary expander** if the degree of every vertex of $U$ is at most $\Delta$ and, for each set $W\subseteq U$ of size at most $s$,
--   $$|\partial W|\ \ge\ c\,|W| .$$
--   Boundary expanders with $c\ge5$, $\Delta=O(1)$ and $s=\Omega(n)$ are the graphs on which the functional pigeonhole principle is shown to be hard for polynomial calculus.
--
--   **Formalization Note** $s,\Delta\in\mathbb N$ and $c\in\mathbb R$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2 (Boundary expansion), p.10 (PDF p.13)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_IsBoundaryExpanderOn

namespace PCNonBool

/-- `G` is an `(s, Δ, c)`-boundary expander (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2, p.10 (PDF p.13)): "the degree of
all vertices in U is at most Δ and for each set W ⊆ U of size at most s, it holds that
|∂W| ≥ c|W|". This is `IsBoundaryExpanderOn` for the whole graph. -/
def IsBoundaryExpander {U V : Type*} [Fintype U] [Fintype V] (G : BipGraph U V) (s Δ : ℕ)
    (c : ℝ) : Prop :=
  IsBoundaryExpanderOn G Finset.univ Finset.univ s Δ c

end PCNonBool


