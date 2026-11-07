-- Prove2me | Definitions.Def_PCNonBool_IsBoundaryExpanderOn
-- name    : PCNonBool_IsBoundaryExpanderOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:28:48.296629+00:00
-- url     : https://prove2.me/theorems/416e6ce5-b40b-4a9a-aaa8-0bffed4d498d
-- title:
--   $(s,\Delta,c)$-boundary expansion of an induced subgraph $G[U_a\sqcup V_a]$
-- statement:
--   Let $U_a\subseteq U$ and $V_a\subseteq V$, and consider the induced subgraph $G[U_a\sqcup V_a]$. For $s,\Delta\in\mathbb N$ and $c\in\mathbb R$, it is an **$(s,\Delta,c)$-boundary expander** if
--
--   1. every pigeon $i\in U_a$ has at most $\Delta$ neighbours in $V_a$, and
--   2. every set $W\subseteq U_a$ with $|W|\le s$ satisfies $|\partial W|\ge c\,|W|$, where the boundary is taken in $G[U_a\sqcup V_a]$.
--
--   This is the paper's definition of boundary expansion applied to an induced subgraph; Algorithm 1 shrinks the graph and must restore this property after each round.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2 (Boundary expansion), p.10 (PDF p.13)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_boundaryOn

namespace PCNonBool

/-- The induced subgraph `G[Ua ⊔ Va]` is an `(s, Δ, c)`-boundary expander
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2, p.10 (PDF p.13)): every pigeon of `Ua` has at most `Δ` holes in `Va`, and every
set `W ⊆ Ua` with `|W| ≤ s` has at least `c · |W|` boundary holes in `Va`.

**Formalization Note** `s` and `Δ` are natural numbers and `c` is real, compared after casting.
Algorithm 1 (p.30) works with the subgraphs `G_ℓ = G[U_ℓ ⊔ V_ℓ]` and `G'_ℓ`; they are described
here by the vertex sets `Ua`, `Va` inside the fixed graph `G`. -/
def IsBoundaryExpanderOn {U V : Type*} (G : BipGraph U V) (Ua : Finset U) (Va : Finset V)
    (s Δ : ℕ) (c : ℝ) : Prop :=
  (∀ i ∈ Ua, (nbrOn G Va i).card ≤ Δ) ∧
  ∀ W : Finset U, W ⊆ Ua → W.card ≤ s → c * (W.card : ℝ) ≤ ((boundaryOn G Va W).card : ℝ)

end PCNonBool


