-- Prove2me | Definitions.Def_BipartiteVRM_Competitive_Paths
-- name    : BipartiteVRM_Competitive_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:34.971274+00:00
-- url     : https://prove2.me/theorems/e9c8f7c2-e125-42f6-81c5-de14b0566505
-- title:
--   Alternating paths, signed net costs, and residual cycles
-- statement:
--   For an arrived set $A$ and auxiliary matching $M$, an unmatched edge is directed from request to server, and a matched edge in the reverse direction. A simple directed path from an unsaturated request $r$ to an unsaturated server is augmenting. Write
--
--   $$\varphi_M(P)=\gamma D(P\setminus M)-D(P\cap M),\qquad M\leftarrow M\mathbin{\triangle}P.$$
--
--   The minimum is over all such paths with vertices in $A$; it is $+\infty$ if there are no paths. The module also defines terminal servers, finite path enumeration, the residual arc weights $\gamma D(r,s)$ and $-D(r,s)$, and directed cycle weights.
--
--   These definitions provide the exact local search problem used by VRM and the graph in Lemma 3.1. They contain no assertion that reachable graphs have no negative cycles. Paths are vertex lists with no repeated vertex, and their edge sets retain the source's set operations.
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), pp. 6–7, §2.2 and §3.1, equation (3.1)

import Definitions.Def_BipartiteVRM_Competitive_Input

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-! Kuo, §2.2–§3.1, pp. 6–7. Simple paths are ordered vertex lists; edges are
unoriented bipartite pairs. No negative-cycle invariant is included in these definitions. -/

def pairEdge : Vertex → Vertex → Option Edge
  | .inl r, .inr s => some (r, s)
  | .inr s, .inl r => some (r, s)
  | _, _ => none

def pathEdges (P : List Vertex) : Matching :=
  ((P.zip P.tail).filterMap (fun uv => pairEdge uv.1 uv.2)).toFinset

def saturated (M : Matching) : Vertex → Prop
  | .inl r => r ∈ M.image Prod.fst
  | .inr s => s ∈ M.image Prod.snd

def residualArc (A : Finset Vertex) (M : Matching) (u v : Vertex) : Prop :=
  u ∈ A ∧ v ∈ A ∧ match u, v with
    | .inl r, .inr s => (r, s) ∉ M
    | .inr s, .inl r => (r, s) ∈ M
    | _, _ => False

def Augmenting (A : Finset Vertex) (M : Matching) (r : ℕ) (P : List Vertex) : Prop :=
  P.Nodup ∧ P.head? = some (.inl r) ∧ ¬ saturated M (.inl r) ∧
    (∃ s, P.getLast? = some (.inr s) ∧ ¬ saturated M (.inr s)) ∧
    P.IsChain (residualArc A M) ∧ 2 ≤ P.length

noncomputable def netCost (D : Edge → ℝ) (γ : ℝ) (M : Matching) (P : List Vertex) : ℝ :=
  γ * (∑ e ∈ pathEdges P \ M, D e) - ∑ e ∈ pathEdges P ∩ M, D e

def augment (M : Matching) (P : List Vertex) : Matching :=
  (M \ pathEdges P) ∪ (pathEdges P \ M)

def terminal (P : List Vertex) : Option ℕ :=
  P.getLast?.bind (fun v => match v with | .inr s => some s | .inl _ => none)

/-- All lists of length at most n from A. Filtering by Augmenting gives exactly the
simple augmenting paths, including all path ties. This finite enumeration is local to A. -/
def listsUpTo (A : Finset Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[]}
  | n + 1 => {[]} ∪ (A ×ˢ listsUpTo A n).image (fun vp => vp.1 :: vp.2)

noncomputable def augmentingPaths (A : Finset Vertex) (M : Matching) (r : ℕ) :
    Finset (List Vertex) := by
  classical
  exact (listsUpTo A A.card).filter (Augmenting A M r)

noncomputable def minimumPaths (A : Finset Vertex) (D : Edge → ℝ)
    (γ : ℝ) (M : Matching) (r : ℕ) : Finset (List Vertex) := by
  classical
  let ps := augmentingPaths A M r
  exact ps.filter (fun P => ∀ Q ∈ ps, netCost D γ M P ≤ netCost D γ M Q)

/-- +∞ on no paths, a signed real minimum otherwise; there is no unbounded-infimum
default because the index set is finite. -/
noncomputable def minNetCost (A : Finset Vertex) (D : Edge → ℝ) (γ : ℝ)
    (M : Matching) (r : ℕ) : WithTop ℝ :=
  (augmentingPaths A M r).inf (fun P => (netCost D γ M P : WithTop ℝ))

noncomputable def arcWeight (D : Edge → ℝ) (γ : ℝ) : Vertex → Vertex → ℝ
  | .inl r, .inr s => γ * D (r, s)
  | .inr s, .inl r => -D (r, s)
  | _, _ => 0

def DirectedCycle (A : Finset Vertex) (M : Matching) (C : List Vertex) : Prop :=
  2 ≤ C.length ∧ C.Nodup ∧ (C ++ C.take 1).IsChain (residualArc A M)

noncomputable def cycleWeight (D : Edge → ℝ) (γ : ℝ) (C : List Vertex) : ℝ :=
  let closed := C ++ C.take 1
  ((closed.zip closed.tail).map (fun uv => arcWeight D γ uv.1 uv.2)).sum

end BipartiteVRM.Competitive


