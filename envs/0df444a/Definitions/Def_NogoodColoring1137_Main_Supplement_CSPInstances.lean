-- Prove2me | Definitions.Def_NogoodColoring1137_Main_Supplement_CSPInstances
-- name    : NogoodColoring1137_Main_Supplement_CSPInstances
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:56:47.953199+00:00
-- url     : https://prove2.me/theorems/335b624d-c713-4de5-b5b1-e47dcbb87d78
-- title:
--   Three-value CSP solutions and the constraint graph
-- statement:
--   Let $\Sigma=\{0,1,2\}$ and let $I=(L,R)$ be a binary CSP on $n$ ordered variables. Its satisfying assignments form a code
--
--   $$
--   Q_I=\{x\in\Sigma^n:\forall v,\ x(v)\in L(v),\quad
--   \forall v<w,\ (x(v),x(w))\in R_{vw}\}.
--   $$
--
--   Its simple undirected constraint graph $H_I$ has an edge $\{v,w\}$ exactly when the relation at that unordered variable pair differs from $\Sigma\times\Sigma$. Edges are computed before imposing unary lists. They do not assert that the relation is symmetric in its two values. Write $\alpha(H_I)$ for the maximum cardinality of an independent set, including the empty independent set.
--
--   This layer specializes the general binary CSP and connects its actual solution predicate to the published dependent code interface, so domain reduction can use full ambient three-value domains even when original lists are smaller.
--
--   **Formalization Note** `Color`, `Lists`, and `Code` are imported from the published base. `SolutionCode` has constant domain size three and active scope `Finset.univ`. The graph uses both orientations of each increasing pair to define symmetric adjacency. The independence number is Mathlib's `SimpleGraph.indepNum` on the finite vertex type, hence it is a bounded, attained finite maximum, and equals zero for no variables.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), Section 8.1, p. 23 (printed = PDF)

import Mathlib
import Definitions.Def_NogoodColoring1137_Main_Instances
import Definitions.Def_NogoodColoring1137_Main_Codes
import Definitions.Def_NogoodColoring1137_Main_Supplement_BinaryCSP

namespace NogoodColoring1137.Main.Supplement

/-- The general binary CSP over the paper's ambient three-value alphabet. -/
abbrev CSP (n : ℕ) := BinaryCSP n Color

/-- Original unary lists, separate from the ambient three-value domains. -/
abbrev OriginalLists {n : ℕ} (I : CSP n) : Lists n := I.unary

/-- Solutions as the published dependent code on full ambient domains, including
when the constraints admit no solution. -/
def SolutionCode {n : ℕ} (I : CSP n) :
    Code (fun _ : Fin n => 3) (Finset.univ : Finset (Fin n)) :=
  {x | I.Satisfies (fun v => x ⟨v, Finset.mem_univ v⟩)}

/-- Edges depend on the full ambient relation, before unary-list filtering.
Only the graph is symmetric; the value relation at an ordered pair need not be. -/
def ConstraintGraph {n : ℕ} (I : CSP n) : SimpleGraph (Fin n) where
  Adj v w :=
    (∃ h : v < w, I.relation ⟨(v, w), h⟩ ≠ Finset.univ) ∨
    (∃ h : w < v, I.relation ⟨(w, v), h⟩ ≠ Finset.univ)
  symm := ⟨by intro v w h; exact h.symm⟩
  loopless := ⟨by
    intro v h
    rcases h with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> exact (lt_irrefl v) hlt⟩

end NogoodColoring1137.Main.Supplement


