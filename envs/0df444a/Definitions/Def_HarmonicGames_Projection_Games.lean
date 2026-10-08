-- Prove2me | Definitions.Def_HarmonicGames_Projection_Games
-- name    : HarmonicGames_Projection_Games
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:21.296101+00:00
-- url     : https://prove2.me/theorems/4e19368a-9d8a-47de-9a7d-fdda0f396bd5
-- title:
--   Every graph of $m$-comparable strategy profiles is a subgraph of the game graph
-- statement:
--   Fix a finite set of players $\mathcal M$ and, for each player $m$, a finite strategy set $E^m$, with strategy profiles $E = \prod_m E^m$. Two profiles $p, q$ are **$m$-comparable** if $p \ne q$ and $p^k = q^k$ for every $k \ne m$; the **game graph** has node set $E$, and $p, q$ are adjacent iff they are $m$-comparable for some player $m$ (Section 2.2). For every player $m$,
--
--   $$
--   A^m \subseteq A ,
--   $$
--
--   i.e. the graph of $m$-comparable profiles is a subgraph of the game graph. This is what makes $D_m$ (20) an operator into the edge flows $C_1$ of the whole game graph.
--
--   **Formalization Note** The game graph, the operators $D_m$, $D$, $\Pi_m$, $\Pi$, the subspaces $\mathcal P$, $\mathcal H$, $\mathcal N$ of (28) and $\varphi = \delta_0^\dagger D u$ are defined in the shared module `HarmonicGames.Decomposition.Games`, which this file imports; this file only restates the subgraph lemma in the namespace `HarmonicGames.Projection`.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 6, Section 2.2 (comparable and m-comparable strategy profiles), and p. 12, (20)

import Mathlib
import Definitions.Def_HarmonicGames_Projection_Pinv
import Definitions.Def_HarmonicGames_Projection_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games

/-!
Finite games as flows on the game graph (Sections 2.1, 2.2 and 4.1 of Candogan, Menache,
Ozdaglar, Parrilo): the game graph, the operators `D_m` (20) and `D` (21), the projections
`Π_m = D_m† D_m` and `Π = diag(Π_1, …, Π_M)`, the potential, harmonic and nonstrategic
subspaces `P`, `H`, `N` (Definition 4.2, (28)), and the function `φ = δ0† D u` of Theorem 4.1.
-/

noncomputable section

namespace HarmonicGames.Projection

open scoped InnerProductSpace

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

theorem mGraph_le_gameGraph (m : ι) : HarmonicGames.Decomposition.mGraph E m ≤ HarmonicGames.Decomposition.gameGraph E := fun _ _ h => ⟨m, h⟩

end HarmonicGames.Projection

end


