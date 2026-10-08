-- Prove2me | Definitions.Def_StrongPerfectGraph_LineGraph_Appears
-- name    : StrongPerfectGraph_LineGraph_Appears
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:48:20.690585+00:00
-- url     : https://prove2.me/theorems/b7a0975c-f5e4-48e1-bbd5-32d11bb370fe
-- title:
--   Appearances of a graph and J-enlargements
-- statement:
--   Let $G, J$ be graphs. $J$ **appears** in $G$ if there is a bipartite subdivision $H$ of $J$ such that $L(H)$ is isomorphic to an induced subgraph of $G$; $L(H)$ is then an **appearance** of $J$ in $G$. The appearance is **nondegenerate** when it is not degenerate in the sense of the preceding definition.
--
--   If $J$ is $3$-connected, a graph $J'$ is a **$J$-enlargement** if $J'$ is $3$-connected and has a proper subgraph which is isomorphic to a subdivision of $J$.
--
--   This module also names the two derived properties used by the theorems: "there is a $J$-enlargement with a nondegenerate appearance in $G$" and "some $J$-enlargement appears in $G$".
--
--   **Formalization Note** "Isomorphic to an induced subgraph" is an induced graph embedding $L(H) \hookrightarrow G$. The subdivision $H$ and the enlargement $J'$ range over graphs on $\{0,\dots,n-1\}$, which loses no generality for finite graphs.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 75, §5, definitions of appears, appearance, nondegenerate appearance, J-enlargement

import Mathlib
import Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision
import Definitions.Def_StrongPerfectGraph_LineGraph_IsDegenerate

namespace StrongPerfectGraph.LineGraph

/-- `J` **appears** in `G` (p. 75): for some bipartite subdivision `H` of `J`, `L(H)` is isomorphic
to an induced subgraph of `G` (`↪g` is an induced embedding). -/
def Appears {W V : Type*} (J : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, ∃ H : SimpleGraph (Fin n),
    IsSubdivision J H ∧ H.IsBipartite ∧ Nonempty (H.lineGraph ↪g G)

/-- `J` has a **nondegenerate appearance** in `G` (p. 75). -/
def HasNondegenerateAppearance {W V : Type*} (J : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, ∃ H : SimpleGraph (Fin n),
    IsSubdivision J H ∧ H.IsBipartite ∧ ¬ IsDegenerateAppearance J H ∧
      Nonempty (H.lineGraph ↪g G)

/-- `J'` is a **`J`-enlargement** (p. 75): `J'` is 3-connected and has a proper subgraph isomorphic
to a subdivision of `J`. -/
def IsEnlargement {W W' : Type*} (J : SimpleGraph W) (J' : SimpleGraph W') : Prop :=
  IsThreeConnected J' ∧ ∃ K : J'.Subgraph, K ≠ ⊤ ∧ IsSubdivision J K.coe

/-- There is a `J`-enlargement with a nondegenerate appearance in `G`. -/
def HasNondegenerateEnlargementAppearance {W V : Type*} (J : SimpleGraph W)
    (G : SimpleGraph V) : Prop :=
  ∃ m : ℕ, ∃ J' : SimpleGraph (Fin m), IsEnlargement J J' ∧ HasNondegenerateAppearance J' G

/-- Some `J`-enlargement appears in `G`. -/
def EnlargementAppears {W V : Type*} (J : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ m : ℕ, ∃ J' : SimpleGraph (Fin m), IsEnlargement J J' ∧ Appears J' G

end StrongPerfectGraph.LineGraph


