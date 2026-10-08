-- Prove2me | Definitions.Def_StrongPerfectGraph_LineGraph_IsDegenerate
-- name    : StrongPerfectGraph_LineGraph_IsDegenerate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:33:14.15458+00:00
-- url     : https://prove2.me/theorems/ff3b5253-a2f2-4ea0-8897-7769ca75d0f2
-- title:
--   Degenerate line graphs of subdivisions of $K_4$ and degenerate appearances
-- statement:
--   Let $H$ be a bipartite subdivision of $K_4$; it has exactly four vertices of degree three. The line graph $L(H)$ is **degenerate** if there is a cycle of $H$ of length four containing the four vertices of $H$ of degree three, and **nondegenerate** otherwise.
--
--   More generally, let $L(H)$ be an appearance of a $3$-connected graph $J$ (so $H$ is a bipartite subdivision of $J$). If $J = K_4$, degeneracy is as above. If $J \ne K_4$, the appearance is **degenerate** if $J = H = K_{3,3}$, and nondegenerate otherwise.
--
--   **Formalization Note** "$J = K_4$", "$H = K_{3,3}$" mean isomorphic to the complete graph on four vertices and to the complete bipartite graph with parts of size three. The four degree-three vertices of a subdivision of $K_4$ are its branch-vertices, so the cycle is encoded as four distinct branch-vertices $a,b,c,d$ with $ab, bc, cd, da \in E(H)$.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 72 (degenerate L(H), H a subdivision of K4) and p. 75 (degenerate appearance for J ≠ K4)

import Mathlib
import Definitions.Def_StrongPerfectGraph_LineGraph_IsTrack

namespace StrongPerfectGraph.LineGraph

/-- `J` is (isomorphic to) the complete graph `K₄`. -/
def IsK4 {W : Type*} (J : SimpleGraph W) : Prop :=
  Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4)))

/-- `J` is (isomorphic to) the complete bipartite graph `K₃,₃`. -/
def IsK33 {W : Type*} (J : SimpleGraph W) : Prop :=
  Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3))

/-- For a bipartite subdivision `H` of `K₄`, `L(H)` is **degenerate** (p. 72) if some cycle of `H`
of length four contains the four vertices of degree three of `H`: four distinct branch-vertices
`a, b, c, d` with `ab, bc, cd, da` edges of `H`. -/
def IsDegenerateK4Subdivision {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ a b c d : V, [a, b, c, d].Nodup ∧
    IsBranchVertex H a ∧ IsBranchVertex H b ∧ IsBranchVertex H c ∧ IsBranchVertex H d ∧
    H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a

/-- An appearance `L(H)` of `J` is **degenerate** (pp. 72, 75): when `J = K₄`, in the sense of
`IsDegenerateK4Subdivision`; when `J ≠ K₄`, if `J = H = K₃,₃`. -/
def IsDegenerateAppearance {W V : Type*} (J : SimpleGraph W) (H : SimpleGraph V) : Prop :=
  (IsK4 J ∧ IsDegenerateK4Subdivision H) ∨ (¬ IsK4 J ∧ IsK33 J ∧ IsK33 H)

end StrongPerfectGraph.LineGraph


