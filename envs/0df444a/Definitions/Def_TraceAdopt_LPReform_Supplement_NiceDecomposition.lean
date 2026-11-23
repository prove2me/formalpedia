-- Prove2me | Definitions.Def_TraceAdopt_LPReform_Supplement_NiceDecomposition
-- name    : TraceAdopt_LPReform_Supplement_NiceDecomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:50:12.111131+00:00
-- url     : https://prove2.me/theorems/bd75f954-a732-4445-8f2c-cbd448c602e2
-- title:
--   Definition 5, p. 42 — equal-size nice decompositions with leaf, replace and join nodes
-- statement:
--   A **nice tree decomposition** of the auxiliary graph $G'$ is a rooted tree decomposition in which every bag has exactly $\omega'+1$ vertices. Every node has one of three forms:
--
--   1. a leaf, with no children;
--   2. a replace node with one child, whose bag loses one vertex $v$ and gains one distinct vertex $u$;
--   3. a join node with two distinct children, both with the same bag as the parent.
--
--   Thus, at a replace node $z$ with child $z_0$,
--
--   $$X'_z\setminus X'_{z_0}=\{u\},\qquad X'_{z_0}\setminus X'_z=\{v\},\qquad u\ne v.$$
--
--   The published GM5 tree-decomposition predicate supplies coverage of all auxiliary vertices and edges, and the running-intersection condition. The finite representation stores a root, a node kind, two child fields and a vertex bag for every node. Children precede parents in the numbering. Unused child fields are ignored. The integer layout stores the number of nodes, root and width, followed by these data in node order; firms have identities $0,\ldots,n-1$, and supply-chain vertices $n,\ldots,n+m-1$.
--
--   **Formalization Note** Postorder numbering is a representation choice available for every finite rooted tree. Root and leaf bags have size $\omega'+1$; they are not required to be empty. This defines the decomposition data and its encoding, without asserting a construction algorithm or supplying a decomposition as an additional input to Theorem 3.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 42, Definition 5; p. 43, Appendix D (boundary bags)

import Mathlib
import Definitions.Def_TraceAdopt_LPReform_Model

set_option autoImplicit false

namespace TraceAdopt.LPReform.Supplement

/-- The three node types in Definition 5 (PDF p. 42). A replace node introduces `u`
and forgets `v`. The conditions on these vertices belong to `IsNiceDecomposition`. -/
inductive DPNodeKind (I : Instance)
  | leaf
  | replace (u v : Fin I.n ⊕ Fin I.m)
  | join

/-- Finite data for a rooted decomposition, numbered with children before parents.
Child fields are ignored at leaves, and `child2` is ignored at replace nodes. -/
structure NiceDecomposition (I : Instance) where
  N : ℕ
  root : Fin N
  kind : Fin N → DPNodeKind I
  child1 : Fin N → Fin N
  child2 : Fin N → Fin N
  bag : Fin N → Finset (Fin I.n ⊕ Fin I.m)

def NiceDecomposition.IsChild {I : Instance} (D : NiceDecomposition I)
    (p c : Fin D.N) : Prop :=
  match D.kind p with
  | .leaf => False
  | .replace _ _ => c = D.child1 p
  | .join => c = D.child1 p ∨ c = D.child2 p

/-- The underlying undirected decomposition graph; not the auxiliary graph itself. -/
def NiceDecomposition.tree {I : Instance} (D : NiceDecomposition I) :
    SimpleGraph (Fin D.N) where
  Adj p c := p ≠ c ∧ (D.IsChild p c ∨ D.IsChild c p)
  symm := by
    constructor
    intro p c h
    exact ⟨Ne.symm h.1, h.2.symm⟩
  loopless := by
    constructor
    intro p h
    exact h.1 rfl

/-- Definition 5: a rooted tree decomposition of `G′` with *all* bags of size `ω′+1`.
Replace nodes swap one distinct vertex; joins have two distinct children with the same bag.
The published GM5 predicate supplies vertex/edge coverage and running intersection.
The postorder numbering is a representation convention, not an extra graph assumption. -/
def IsNiceDecomposition {I : Instance} (D : NiceDecomposition I) (ω' : ℕ) : Prop :=
  RobertsonSeymour1986.GM5.IsTreeDecomposition (auxGraph I) D.tree D.bag ∧
  (∀ p c, D.IsChild p c → c.val < p.val) ∧
  (∀ p, ¬ D.IsChild p D.root) ∧
  (∀ c, c ≠ D.root → ∃! p, D.IsChild p c) ∧
  (∀ z, (D.bag z).card = ω' + 1) ∧
  (∀ z, match D.kind z with
    | .leaf => True
    | .replace u v =>
        u ≠ v ∧ D.bag z \ D.bag (D.child1 z) = {u} ∧
          D.bag (D.child1 z) \ D.bag z = {v}
    | .join =>
        D.child1 z ≠ D.child2 z ∧ D.bag z = D.bag (D.child1 z) ∧
          D.bag z = D.bag (D.child2 z))

/-- Integer identities for firm and supply-chain vertices in a stored decomposition. -/
def dpVertexCode {I : Instance} : Fin I.n ⊕ Fin I.m → ℕ :=
  Sum.elim Fin.val (fun j => I.n + j.val)

def DPNodeKind.code {I : Instance} : DPNodeKind I → List ℕ
  | .leaf => [0, 0, 0]
  | .replace u v => [1, dpVertexCode u, dpVertexCode v]
  | .join => [2, 0, 0]

/-- Computational layout: number of nodes, root, width, then per node its kind,
two child fields, bag size, and the sorted vertex identities in the bag.
This records decomposition data only; it supplies no free construction oracle. -/
def niceDecompositionInts {I : Instance} (D : NiceDecomposition I) (ω' : ℕ) : List ℕ :=
  [D.N, D.root.val, ω'] ++ (List.finRange D.N).flatMap (fun z =>
    (D.kind z).code ++ [(D.child1 z).val, (D.child2 z).val, (D.bag z).card] ++
      (((D.bag z).image dpVertexCode).sort (· ≤ ·)))

end TraceAdopt.LPReform.Supplement


