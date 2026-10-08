-- Prove2me | Definitions.Def_HarmonicGames_Pareto_Games
-- name    : HarmonicGames_Pareto_Games
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:46:24.746284+00:00
-- url     : https://prove2.me/theorems/540928b4-c7a8-4940-83f9-c78dc67b5d95
-- title:
--   Every m-comparability graph is a subgraph of the game graph
-- statement:
--   Fix a finite set of players $\mathcal M$ and, for each player $m$, a finite strategy set $E^m$; strategy profiles are $p \in E = \prod_m E^m$. Two profiles $p, q$ are **$m$-comparable** if $p \ne q$ and $p^k = q^k$ for every $k \ne m$; the **game graph** has node set $E$, and $p, q$ are adjacent iff they are $m$-comparable for some $m$ (Section 2.2).
--
--   For every player $m$, the graph of $m$-comparable pairs is a subgraph of the game graph: if $p$ and $q$ are $m$-comparable, they are adjacent in the game graph.
--
--   This is what lets the operator $D_m$ of (20), the gradient along the $m$-comparable edges, take values in the edge flows $C_1$ of the whole game graph.
--
--   **Formalization Note** The game graph, $D_m$, $D$ and the potential and harmonic components $u_{\mathcal P} = D^\dagger \delta_0 \delta_0^\dagger D u$, $u_{\mathcal H} = D^\dagger (I - \delta_0 \delta_0^\dagger) D u$ of Theorem 4.1 are the shared definitions in `HarmonicGames.Decomposition.Games`, which this module imports; the module itself contains only the subgraph lemma.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, pp. 5–6 (Sections 2.1–2.2), pp. 12–13 (Section 4.1, (20), (21)), p. 17 (Theorem 4.1, potential and harmonic components)

import Mathlib
import Definitions.Def_HarmonicGames_Pareto_Pinv
import Definitions.Def_HarmonicGames_Pareto_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games
import Definitions.Def_HarmonicGames_GenericPure_Games

/-!
Finite games as flows on the game graph (Sections 2.1, 2.2, 4.1 and 4.2 of Candogan, Menache,
Ozdaglar, Parrilo): the game graph, the operators `D_m` (20) and `D` (21), and the potential and
harmonic components `u_P = D† δ0 δ0† D u`, `u_H = D† (I - δ0 δ0†) D u` of Theorem 4.1.
-/

noncomputable section

namespace HarmonicGames.Pareto

open scoped InnerProductSpace

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

theorem mGraph_le_gameGraph (m : ι) : HarmonicGames.Decomposition.mGraph E m ≤ HarmonicGames.Decomposition.gameGraph E := fun _ _ h => ⟨m, h⟩

end HarmonicGames.Pareto

end


