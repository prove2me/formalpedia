-- Prove2me | Definitions.Def_TriangleFace
-- name    : TriangleFace
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:34.527698+00:00
-- url     : https://prove2.me/theorems/e7fd3609-7115-4aed-8aee-eb8bb709b0e1
-- statement:
--   A LooplessGraph on finite vertex type V and edge type E is given by left and right endpoint maps with left(e)≠right(e) for every edge, so parallel edges are allowed but loops are not. An edge e is incident to v if v is one of its endpoints. A perfect matching is a finite set M of edges such that every vertex lies on exactly one edge of M; the type of perfect matchings is finite, indicator(M) is the 0/1 vector of M in ℝ^E, and the polytope of G is the convex hull of all these indicator vectors. An edge crosses a vertex set S if exactly one endpoint lies in S; cut(S) is the set of crossing edges, degree(x,v) sums the coordinates x(e) over edges incident to v, and cutMass(x,S) sums x(e) over cut(S). For the triangle expansion at a vertex v, the new vertex type is V ⊕ Fin 2, with triangleTip(v,0)=v and tips 1 and 2 the two new vertices. The map reattach(v,i,w) sends w to tip i when w=v and otherwise keeps w, and triangleCollapse(v) sends both new vertices back to v; the lemma collapse_reattach states that collapsing a reattached vertex recovers it. Given a labeling c of the edges by Fin 3, triangleExpansion(G,c,v) is a loopless graph on V ⊕ Fin 2 whose edges are the old edges plus three new edges: each old edge e keeps its endpoints except that any endpoint equal to v is moved to tip c(e), and new edge i joins tips i+1 and i+2, forming a triangle. Looplessness is proved using the collapse lemma. In a separate block, facesThrough(P,x) is the family of convex extreme subsets of P containing x, in a real vector space, and minFace(P,x) is their intersection. LocalLabels(G,v,c) says that for each label i in Fin 3 exactly one edge incident to v has label i; localEdge then selects that edge by choice, localExtension is the linear map ℝ^E → ℝ^(E⊕Fin 3) keeping x on old edges and giving new edge i the value x of localEdge i, and oldRestriction is the linear map restricting a vector on E⊕Fin 3 to the old edges. The final namespace block is empty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TriangleFace.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TriangleFace.lean; bytes 16..5338
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uIndex uι

namespace MatchingEntropyBounds

structure LooplessGraph (V : Type uV) (E : Type uE) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

variable {V : Type uV} {E : Type uE}
  [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def Incident (G : LooplessGraph V E) (v : V) (e : E) : Prop :=
  G.left e = v ∨ G.right e = v

instance incidentDecidable (G : LooplessGraph V E) (v : V) (e : E) :
    Decidable (G.Incident v e) := inferInstanceAs (Decidable (G.left e = v ∨ G.right e = v))

def IsPerfectMatching (G : LooplessGraph V E) (M : Finset E) : Prop :=
  ∀ v, ∃! e, e ∈ M ∧ G.Incident v e

abbrev Matching (G : LooplessGraph V E) := {M : Finset E // G.IsPerfectMatching M}

instance matchingFintype (G : LooplessGraph V E) : Fintype G.Matching :=
  Fintype.ofFinite _

def indicator (G : LooplessGraph V E) (M : G.Matching) (e : E) : ℝ :=
  if e ∈ M.val then 1 else 0

def polytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  convexHull ℝ (Set.range G.indicator)

end LooplessGraph
end MatchingEntropyBounds
end

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def Crosses (G : LooplessGraph V E) (S : Finset V) (e : E) : Prop :=
  (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)

instance crossesDecidable (G : LooplessGraph V E) (S : Finset V) (e : E) :
    Decidable (G.Crosses S e) := inferInstanceAs (Decidable
      ((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)))

def cut (G : LooplessGraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (G.Crosses S)

def degree (G : LooplessGraph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, if G.Incident v e then x e else 0

def cutMass (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.cut S, x e

end MatchingEntropyBounds.LooplessGraph
end

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

section TriangleExpansion
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def triangleTip (v : V) (i : Fin 3) : V ⊕ Fin 2 := ![Sum.inl v, Sum.inr 0, Sum.inr 1] i

def triangleCollapse (v : V) : V ⊕ Fin 2 → V := Sum.elim id (fun _ => v)

def reattach (v : V) (i : Fin 3) (w : V) : V ⊕ Fin 2 :=
  if w = v then triangleTip v i else Sum.inl w

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem collapse_reattach (v : V) (i : Fin 3) (w : V) :
    triangleCollapse v (reattach v i w) = w := by
  by_cases h : w = v
  · subst w
    fin_cases i <;> simp [reattach,triangleTip,triangleCollapse]
  · simp [reattach,h,triangleCollapse]

def triangleExpansion (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    LooplessGraph (V ⊕ Fin 2) (E ⊕ Fin 3) where
  left := Sum.elim (fun e => reattach v (c e) (G.left e)) (fun i => triangleTip v (i + 1))
  right := Sum.elim (fun e => reattach v (c e) (G.right e)) (fun i => triangleTip v (i + 2))
  loopless := by
    intro e h
    rcases e with e | i
    · have hh := congrArg (triangleCollapse v) h
      exact G.loopless e ((collapse_reattach v (c e) (G.left e)).symm.trans
        (hh.trans (collapse_reattach v (c e) (G.right e))))
    · fin_cases i <;> simp [triangleTip] at h

def triangleVertices (v : V) : Finset (V ⊕ Fin 2) := Finset.univ.image (triangleTip v)

end TriangleExpansion
end MatchingEntropyBounds.Refined
end

namespace CanonicalFace198

variable {A B : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup B] [Module ℝ B]

def facesThrough (P : Set A) (x : A) : Set (Set A) :=
  {F | Convex ℝ F ∧ IsExtreme ℝ P F ∧ x ∈ F}

def minFace (P : Set A) (x : A) : Set A := ⋂₀ facesThrough P x

end CanonicalFace198

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def LocalLabels (G : LooplessGraph V E) (v : V) (c : E → Fin 3) : Prop :=
  ∀ i, ∃! e, G.Incident v e ∧ c e = i

def localEdge (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (i : Fin 3) : E := Classical.choose (hc i)

def localExtension (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) : (E → ℝ) →ₗ[ℝ] (E ⊕ Fin 3 → ℝ) where
  toFun x := Sum.elim x (fun i => x (localEdge G c v hc i))
  map_add' x y := by ext e; cases e <;> rfl
  map_smul' a x := by ext e; cases e <;> rfl

def oldRestriction : (E ⊕ Fin 3 → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun y e := y (Sum.inl e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end TriangleFace198

end

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]



end TriangleFace198
end
end OAI


