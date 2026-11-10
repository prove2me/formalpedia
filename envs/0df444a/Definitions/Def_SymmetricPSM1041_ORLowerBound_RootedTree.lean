-- Prove2me | Definitions.Def_SymmetricPSM1041_ORLowerBound_RootedTree
-- name    : SymmetricPSM1041_ORLowerBound_RootedTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:56:13.0062+00:00
-- url     : https://prove2.me/theorems/0b07d93d-98f5-473f-92d0-3516b73c9789
-- title:
--   Appendix A.1 — rooted trees with leaves permitted
-- statement:
--   A rooted tree on a vertex set $V$ has a root $o$ and a unique parent for each vertex other than $o$. In the parent-map representation, the total parent map fixes $o$, and every vertex reaches $o$ after finitely many parent steps:
--
--   $$\operatorname{parent}(o)=o,\qquad \forall v\in V\ \exists k\in\mathbb N:\ \operatorname{parent}^{k}(v)=o.$$
--
--   The children of $v$ are precisely the vertices $w\ne o$ with $\operatorname{parent}(w)=v$. The artificial self-parent of the root is never a child edge. Reachability excludes nonroot cycles and disconnected components, so this is the usual rooted-tree representation.
--
--   The tree may have leaves and unbounded finite depths. Finiteness of child sets and infinitude of the vertex set are separate hypotheses of König's lemma. There is no ordering of children and no requirement that a parent map be surjective.
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 26, Appendix A.1, Lemma 37

import Mathlib

namespace SymmetricPSM1041.ORLowerBound

/-- A rooted tree represented by its parent map. The root is its own parent solely
as a total-function convention; it is never counted as its own child. Every vertex
reaches the root in finitely many steps. No ordering or no-leaf condition is imposed. -/
structure RootedTree (V : Type*) where
  root : V
  parent : V → V
  parent_root : parent root = root
  reachable : ∀ v, ∃ k : ℕ, (parent^[k]) v = root

def children {V : Type*} (T : RootedTree V) (v : V) : Set V :=
  {w | w ≠ T.root ∧ T.parent w = v}

end SymmetricPSM1041.ORLowerBound


