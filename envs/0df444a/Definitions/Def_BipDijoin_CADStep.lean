-- Prove2me | Definitions.Def_BipDijoin_CADStep
-- name    : BipDijoin_CADStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:49:08.492167+00:00
-- url     : https://prove2.me/theorems/b8a537d9-dd10-45e0-9911-8706fa7839e4
-- title:
--   The contraction–augmentation–deactivation process (Algorithm 3)
-- statement:
--   A state of Algorithm 3 is a graph $G_i$, a matching $M_i$ of it, an active set $A_i\subseteq V(G_i)$ and the number of contractions so far. Write $D_i=(G_i)_{M_i}$. While $A_i\ne\emptyset$, one iteration does the following.
--
--   1. Choose a nontrivial source SCC $U$ of $D_i[A_i]$ (NextSource).
--   2. If some directed path of $D_i$ leads from a vertex of $U$ to an $M_i$-unmatched right vertex, choose a shortest one $P$ (counted in arcs, vertex-simple). Record $(G_i,M_i,U)$, contract $U$ to a fresh left vertex $x$, remove the edges inside $U$ from the matching and augment it along $P$ (whose first arc now leaves $x$); the active set becomes $(A_i\setminus U)\cup\{x\}$. The iteration outputs the record and $|P|$.
--   3. Otherwise deactivate $Z=\mathrm{Reach}_{D_i}(U)$: $A_{i+1}=A_i\setminus Z$, the graph and the matching stay.
--
--   The process starts from $(G,M_0,V(G))$ with $M_0$ a maximum matching. A **complete run** ends with $A=\emptyset$; its records form $\Gamma$, and its path lengths are $|P_1|,|P_2|,\dots$.
--
--   **Formalization Note** The process is a relation: every choice of $M_0$, of $U$ and of the shortest path is allowed, so a statement about all runs covers every implementation of the subroutines. The $i$-th contraction uses the name $N_0+i$, matching the decomposition records. As in Algorithm 3, deactivated vertices stay in the graph (the analysis on p.31 deletes them; paths from $U$ never enter them).
-- source:
--   C. Nalam, T. Saranurak, Breaking the O(mn) Barrier for Minimum Bipartite Dijoin via Dynamic and Local Graph Algorithms, STOC 2027 submission (manuscript sha256 382f85e4bb71b51866bdfa1d09aa8a3e2f160dd4266b9f2c87827be49387fea6), §6.2, Algorithm 3, p.26 (PDF p.28), and p.27 (PDF p.29)

import Mathlib
import Definitions.Def_BipDijoin_BipGraph
import Definitions.Def_BipDijoin_IsMatching
import Definitions.Def_BipDijoin_IsStrongEnd
import Definitions.Def_BipDijoin_IsPartialDecomp

set_option autoImplicit false

namespace BipDijoin

/-!
# The contraction–augmentation–deactivation process (Algorithm 3)

Nalam–Saranurak, STOC 2027 submission (manuscript sha256 382f85e4…7fea6), §6.2, pp.26–27
(PDF pp.28–29):
"NextSource() Return a source strong end U in G_i[A_i] that is fitted by M_i.
ShortestPathOrReachableSet(U) Returns either Path(P, r), where P is a shortest directed path in D_i
from U ending at an unmatched vertex r, (or) Unreachable(Z), where Z = Reach_{D_i}(U) contains no
unmatched right vertex.
ContractAndAugment(U, P) Updates G_i, D_i by contracting U and the matching M_i by removing edges
internal to U and augmenting along P after contraction.
Deactivate(Z) Updates A_i, B_i by moving Z from A_i to B_i. Keeps G_i, D_i, M_i unchanged."
Algorithm 3: "1: i ← 0, Γ ← ∅ 2: G_i ← G, M_i ← MaximumMatching(G), A_i ← V_i 3: while A_i ≠ ∅ do
4: U ← NextSource() 5: Y ← ShortestPathOrReachableSet(U) 6: if Y = Path(P_i, r) then
7: Γ ← Γ ◦ (G_i, M_i, U) 8: (G_{i+1}, M_{i+1}) ← ContractAndAugment(U, P_i) 9: else ▷ Y = Unreachable(Z)
10: Deactivate(Z) 11: end if 12: i ← i + 1 13: end while 14: return (Γ, G_i, M_i)", with
`D_i = (G_i)_{M_i}`.

**Formalization Note.**
* The process is a nondeterministic step relation: every choice of the source SCC `U`, of the
  shortest path `P` and of the initial maximum matching is allowed, so a statement about all
  runs covers every implementation of the subroutines.
* `NextSource` returns a nontrivial source SCC of `D_i[A_i]` (the reading of the proof of
  Lemma 6.3, p.28).
* A path is a start vertex and a list of steps `(e, true)` (the arc `tl e → hd e`) or `(e, false)`
  (the reverse arc of `e ∈ M`); it is vertex-simple, its length is its number of arcs, and it lies
  in the whole of `D_i`. "Shortest" is minimum length among all such paths from a vertex of `U` to
  an unmatched right vertex.
* Contract-augment: `U` is contracted to the fresh left vertex `N₀ + i'` (`i'` the number of
  contractions so far, so that the recorded contractions form a partial decomposition with
  representatives `N₀, N₀ + 1, …`), the matching becomes `(M ∖ E(H[U])) ∆ E(P)` (edge
  identities are kept by contraction), and the active set becomes `(A ∖ U) ∪ {x}`. The step
  outputs the record `(left, U, M ∩ E(H[U]))` and the length `|P|`.
* Deactivate: `A` loses `Reach_{D_i}(U)`; the output is `none`.
* The paper's analysis deletes deactivated sets (`G_{i+1} = H_i`, p.31); Algorithm 3 keeps them,
  and so does this relation.
-/

namespace BipGraph

variable (G : BipGraph)

/-- `P` is a directed walk of `G_M` from `u` to `v`. -/
def AltPath (M : Finset ℕ) : ℕ → List (ℕ × Bool) → ℕ → Prop
  | u, [], v => u = v
  | u, (e, true) :: P, v => e ∈ G.E ∧ G.tl e = u ∧ AltPath M (G.hd e) P v
  | u, (e, false) :: P, v => e ∈ M ∧ G.hd e = u ∧ AltPath M (G.tl e) P v

/-- The vertices visited by the walk `P` from `u`, in order. -/
def pathVerts : ℕ → List (ℕ × Bool) → List ℕ
  | u, [] => [u]
  | u, (e, b) :: P => u :: pathVerts (if b then G.hd e else G.tl e) P

/-- `P` is a vertex-simple directed path of `G_M` from a vertex of `U` to an `M`-unmatched right
vertex. -/
def IsFreePath (M U : Finset ℕ) (P : List (ℕ × Bool)) : Prop :=
  ∃ u ∈ U, ∃ r ∈ G.right, ¬ G.covered M r ∧ G.AltPath M u P r ∧ (G.pathVerts u P).Nodup

/-- `P` is a shortest such path. -/
def IsShortestFreePath (M U : Finset ℕ) (P : List (ℕ × Bool)) : Prop :=
  G.IsFreePath M U P ∧ ∀ P', G.IsFreePath M U P' → P.length ≤ P'.length

open Classical in
/-- `Reach_{G_M}(U)`: the vertices reachable from `U` in `G_M`. -/
noncomputable def reachSet (M U : Finset ℕ) : Finset ℕ :=
  G.V.filter (fun v => ∃ u ∈ U, ReachIn (G.altArc M) G.V u v)

end BipGraph

/-- A state of Algorithm 3: the current graph `H = G_i`, matching `M = M_i`, active set `A = A_i`,
and the number `nrec` of contractions performed so far. -/
structure CADState where
  /-- The current graph `G_i`. -/
  H : BipGraph
  /-- The current matching `M_i`. -/
  M : Finset ℕ
  /-- The active set `A_i`. -/
  A : Finset ℕ
  /-- The number of contractions so far. -/
  nrec : ℕ

/-- One iteration of the while loop of Algorithm 3, with representatives `N₀, N₀ + 1, …`. The
output is `some (record, |P|)` for a contraction and `none` for a deactivation. -/
inductive CADStep (N₀ : ℕ) : CADState → Option (Rec × ℕ) → CADState → Prop
  /-- Lines 4–8: `U` a nontrivial source SCC of `D_i[A_i]`, `P` a shortest path of `D_i` from `U`
  to an unmatched right vertex; record, contract `U`, augment along `P`. -/
  | contractAugment (s : CADState) (U : Finset ℕ) (P : List (ℕ × Bool))
      (hU : 2 ≤ U.card) (hsrc : IsSourceSCC (s.H.altArc s.M) s.A U)
      (hP : s.H.IsShortestFreePath s.M U P) :
      CADStep N₀ s (some (⟨true, U, s.M ∩ (s.H.induced U).E⟩, P.length))
        ⟨s.H.contract U (N₀ + s.nrec) true,
          symmDiff (s.M \ (s.H.induced U).E) (P.map Prod.fst).toFinset,
          (s.A \ U) ∪ {N₀ + s.nrec}, s.nrec + 1⟩
  /-- Lines 4–5, 10: no path from `U` to an unmatched right vertex; deactivate `Reach_{D_i}(U)`. -/
  | deactivate (s : CADState) (U : Finset ℕ)
      (hU : 2 ≤ U.card) (hsrc : IsSourceSCC (s.H.altArc s.M) s.A U)
      (hno : ∀ P, ¬ s.H.IsFreePath s.M U P) :
      CADStep N₀ s none ⟨s.H, s.M, s.A \ s.H.reachSet s.M U, s.nrec⟩

/-- A finite run of Algorithm 3: a sequence of steps, with their outputs. -/
inductive CADRun (N₀ : ℕ) : CADState → List (Option (Rec × ℕ)) → CADState → Prop
  | nil (s : CADState) : CADRun N₀ s [] s
  | cons (s : CADState) (o : Option (Rec × ℕ)) (t : CADState) (outs : List (Option (Rec × ℕ)))
      (u : CADState) : CADStep N₀ s o t → CADRun N₀ t outs u → CADRun N₀ s (o :: outs) u

/-- Line 2 of Algorithm 3: start from `G`, the matching `M₀`, everything active, no contraction. -/
def cadStart (G : BipGraph) (M₀ : Finset ℕ) : CADState := ⟨G, M₀, G.V, 0⟩

/-- The records `Γ` of a run, in order. -/
def runRecs (outs : List (Option (Rec × ℕ))) : List Rec := outs.filterMap (Option.map Prod.fst)

/-- The lengths `|P_i|` of the augmenting paths of a run, in order. -/
def runPathLengths (outs : List (Option (Rec × ℕ))) : List ℕ :=
  outs.filterMap (Option.map Prod.snd)

end BipDijoin


