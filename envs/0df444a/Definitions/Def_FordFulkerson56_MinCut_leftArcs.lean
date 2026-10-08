-- Prove2me | Definitions.Def_FordFulkerson56_MinCut_leftArcs
-- name    : FordFulkerson56_MinCut_leftArcs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:50:05.995373+00:00
-- url     : https://prove2.me/theorems/037838c1-8f55-45e9-b05f-2dc0eb34ac35
-- title:
--   The proof objects S (arcs saturated by every maximal flow), left vertices, and the left arcs L
-- statement:
--   These are the objects of Ford and Fulkerson's proof of the minimal cut theorem (pp. 400–401). Let $N$ be a network with source $a$ and sink $b$.
--
--   1. $S$ is the set of arcs that are saturated in **every** maximal flow.
--   2. A vertex $v$ is a **left vertex** of an arc $\alpha$ if there are a maximal flow $f$ and a chain from $a$ to $b$, arranged as $\alpha_1(v_0v_1),\dots,\alpha_m(v_{m-1}v_m)$ with $v_0=a$, $v_m=b$, carrying a positive amount $f>0$, in which $\alpha=\alpha_i$ and $v=v_{i-1}$: the end vertex of $\alpha$ that occurs first when the chain is traversed from the source.
--   3. An arc $\alpha\in S$ is a **left arc** if it has a left vertex $v$ for which there are a maximal flow $f$ and a chain (possibly null) joining $a$ and $v$ none of whose arcs is saturated by $f$. $L$ is the set of left arcs.
--
--   The paper shows that each arc of $S$ has a well-defined left vertex, and that $L$ is a cut of minimal value; these sets carry the whole proof.
--
--   **Formalization Note** The left vertex is encoded as a relation rather than a function; that it is single-valued on $S$ is a separate milestone (the orientation claim). In the definition of $L$ the left vertex is quantified existentially; given the orientation claim this is equivalent to requiring the condition for the left vertex.
-- source:
--   Ford & Fulkerson, Maximal Flow Through a Network, Canad. J. Math. 8 (1956), p. 400 (definition of S), p. 401 (left vertex, left arc, L), proof of Theorem 1

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsFlow

namespace FordFulkerson56.MinCut

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-- The set `S` of the proof of Theorem 1 (p. 400): the arcs saturated in every maximal flow. -/
noncomputable def saturatedSet (N : Network V E) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ∀ f, IsMaxFlow N f → Saturated N f e)

/-- `IsLeftVertex N e v` (p. 401): `v` is the vertex of `e` that occurs first in a positive chain flow
of some maximal flow, i.e. there are a maximal flow `f` and an arrangement `(p, vs)` of a chain from
the source to the sink with `0 < f p.toFinset`, in which `e` is the `i`-th arc and `v` the `i`-th
vertex (the vertex from which the walk enters `e`). -/
def IsLeftVertex (N : Network V E) (e : E) (v : V) : Prop :=
  ∃ f, IsMaxFlow N f ∧ ∃ (p : List E) (vs : List V),
    IsChainWalk N N.source N.sink p vs ∧ 0 < f p.toFinset ∧
    ∃ i : ℕ, p[i]? = some e ∧ vs[i]? = some v

/-- The set `L` of left arcs of `S` (p. 401): the arcs `e ∈ S` with a left vertex `v` for which there
are a maximal flow `f` and a chain (possibly null) joining the source and `v` none of whose arcs is
saturated by `f`. -/
noncomputable def leftArcs (N : Network V E) : Finset E := by
  classical
  exact (saturatedSet N).filter (fun e => ∃ v, IsLeftVertex N e v ∧
    ∃ f, IsMaxFlow N f ∧ ∃ C, IsChain N N.source v C ∧ ∀ e' ∈ C, ¬ Saturated N f e')

end FordFulkerson56.MinCut


