-- Prove2me | Definitions.Def_PfaffianRecognition_Recognition_graph_model
-- name    : PfaffianRecognition_Recognition_graph_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T04:36:45.914418+00:00
-- url     : https://prove2.me/theorems/f0249feb-d4d9-4260-ae6b-457b588e7ff6
-- title:
--   Orientations, independent matching signs, and crossing parities
-- statement:
--   Let $G$ be any finite simple graph on ordered vertices $0,\ldots,N-1$. An orientation $D$ selects exactly one direction for each edge and no direction for a nonedge; the published orientation predicate and exact-cover perfect-matching predicate are reused. For a perfect matching $M$, sort its edges by the smaller endpoint, list each edge's oriented tail and head, and take the integer sign of the resulting permutation. Write this as $\operatorname{sign}_D(M)\in\{-1,+1\}$. Define
--   $$
--   \begin{aligned}
--   D\text{ is Pfaffian}&\iff \forall M_1,M_2\in\mathcal M(G),\quad
--    \operatorname{sign}_D(M_1)=\operatorname{sign}_D(M_2),\\
--   G\text{ is Pfaffian}&\iff \exists D,\quad D\text{ is a Pfaffian orientation of }G.
--   \end{aligned}
--   $$
--   An edge is backward when directed from its larger endpoint to its smaller endpoint. Two edges cross when their four endpoints alternate. The quantities $\operatorname{rev}_D(M)$ and $\operatorname{cr}(M)$ are their respective count parities, and $s=(\operatorname{cr}(F)+\operatorname{rev}_D(F))\bmod2$ for a reference matching $F$.
--
--   These definitions make Pfaffianity mathematical and independent of any decision procedure or algebraic identity. No matching, connectivity or even-order promise is attached to the input graph.
--
--   **Formalization Note** Vertices are zero-based. Each unordered crossing pair is represented once by placing the edge with the smaller left endpoint first. Parities use their natural representatives 0 and 1. The permutation helper chooses the unique permutation with the stated sequence, and returns the identity only if no such permutation exists; this fallback concerns invalid edge sets, which all uses of matching signs exclude. At $N=0$ the empty matching has sign $+1$; if there is no perfect matching the pairwise sign condition is vacuous.
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), §1, pp. 1–2; §2.1, pp. 4–5; §2.2, p. 5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_Algorithm
import Definitions.Def_SparseDisc_IsOrientation

noncomputable section

namespace PfaffianRecognition.Recognition

/-- The source's orientation: exactly one direction per edge and no arcs on nonedges.
The general orientation predicate is reused without additional conditions. -/
abbrev Orientation {N : ℕ} (G : SimpleGraph (Fin N)) :=
  {D : Fin N → Fin N → Prop // SparseDisc.IsOrientation G D}

/-- Endpoints in the fixed increasing vertex order (source labels are these indices plus one). -/
def edgeLo {N : ℕ} {G : SimpleGraph (Fin N)} (e : G.edgeSet) : Fin N :=
  min e.val.out.1 e.val.out.2

def edgeHi {N : ℕ} {G : SimpleGraph (Fin N)} (e : G.edgeSet) : Fin N :=
  max e.val.out.1 e.val.out.2

/-- Order edge blocks by their smaller endpoint. For a perfect matching the keys are distinct. -/
def matchingEdgeOrder {N : ℕ} {G : SimpleGraph (Fin N)} (M : Finset G.edgeSet) :
    List G.edgeSet := by
  classical
  exact M.toList.mergeSort (fun e f => decide (edgeLo e ≤ edgeLo f))

/-- The one-line sequence of oriented tails and heads, in the chosen edge-block order. -/
def matchingSequence {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G)
    (M : Finset G.edgeSet) : List (Fin N) := by
  classical
  exact (matchingEdgeOrder M).flatMap fun e =>
    if D.val (edgeLo e) (edgeHi e) then [edgeLo e, edgeHi e] else [edgeHi e, edgeLo e]

/-- Recover the permutation with that one-line sequence. For perfect matchings it exists and
is unique. The identity fallback totalizes this helper on invalid matchings only; every use of
matching signs in the predicates/polynomials is restricted to genuine perfect matchings. -/
def matchingPermutation {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G)
    (M : Finset G.edgeSet) : Equiv.Perm (Fin N) := by
  classical
  exact if h : ∃ p : Equiv.Perm (Fin N), List.ofFn p = matchingSequence D M
    then Classical.choose h else Equiv.refl _

/-- Integer permutation sign, defined independently of crossing/backward-edge parity. -/
def matchingSign {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G)
    (M : Finset G.edgeSet) : ℤ :=
  (Equiv.Perm.sign (matchingPermutation D M) : ℤ)

/-- Equal integer signs for every pair of perfect matchings, including the empty family. -/
def IsPfaffianOrientation {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G) : Prop :=
  ∀ M₁ M₂ : Finset G.edgeSet,
    MulmuleyVV.Matching.IsPerfectMatchingEdges G M₁ →
    MulmuleyVV.Matching.IsPerfectMatchingEdges G M₂ → matchingSign D M₁ = matchingSign D M₂

/-- Mathematical graph Pfaffianity, independent of any recognition algorithm. -/
def IsPfaffianGraph {N : ℕ} (G : SimpleGraph (Fin N)) : Prop :=
  ∃ D : Orientation G, IsPfaffianOrientation D

/-- Vertex-disjoint edges with alternating endpoints. -/
def Crosses {N : ℕ} {G : SimpleGraph (Fin N)} (e f : G.edgeSet) : Prop :=
  (edgeLo e < edgeLo f ∧ edgeLo f < edgeHi e ∧ edgeHi e < edgeHi f) ∨
  (edgeLo f < edgeLo e ∧ edgeLo e < edgeHi f ∧ edgeHi f < edgeHi e)

/-- Each unordered crossing pair occurs once, represented with its smaller left endpoint first. -/
def crossingPairs {N : ℕ} (G : SimpleGraph (Fin N)) : Finset (G.edgeSet × G.edgeSet) := by
  classical
  exact Finset.univ.filter fun ef => edgeLo ef.1 < edgeLo ef.2 ∧ Crosses ef.1 ef.2

/-- R_D: edges oriented from the larger endpoint to the smaller endpoint. -/
def backwardEdges {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter fun e => D.val (edgeHi e) (edgeLo e)

/-- Representatives 0 and 1 of the parities in F₂, computed from separate counts. -/
def crossingParity {N : ℕ} {G : SimpleGraph (Fin N)} (M : Finset G.edgeSet) : ℕ := by
  classical
  exact ((crossingPairs G).filter fun ef => ef.1 ∈ M ∧ ef.2 ∈ M).card % 2

def backwardParity {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G)
    (M : Finset G.edgeSet) : ℕ := by
  classical
  exact (M ∩ backwardEdges D).card % 2

/-- The bit s = cr(F) + rev_D(F) in F₂, represented by its least nonnegative integer. -/
def referenceParity {N : ℕ} {G : SimpleGraph (Fin N)} (D : Orientation G)
    (F : Finset G.edgeSet) : ℕ :=
  (crossingParity F + backwardParity D F) % 2

end PfaffianRecognition.Recognition


