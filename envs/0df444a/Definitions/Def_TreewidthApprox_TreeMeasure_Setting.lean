-- Prove2me | Definitions.Def_TreewidthApprox_TreeMeasure_Setting
-- name    : TreewidthApprox_TreeMeasure_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:02.45632+00:00
-- url     : https://prove2.me/theorems/8ad9a616-ecf6-4d59-ba54-32b13a2a12c7
-- title:
--   Lemma 4.3, p. 349 — children of a vertex in a rooted tree
-- statement:
--   Let $T$ be a finite rooted tree on the vertex set $V$, given by its root $r$ and its parent map $p$ (with the convention $p(r)=r$), as in the referenced definition of rooted trees. For vertices $v$ and $c$ we say that **$c$ is a child of $v$**, equivalently that **$v$ is the parent of $c$**, when
--   $$
--   c \neq r \quad\text{and}\quad p(c) = v .
--   $$
--   The **children** of $v$ form the finite set
--   $$
--   \mathrm{ch}(v) = \{\, c \in V : c \neq r,\ p(c) = v \,\},
--   $$
--   which is empty exactly when $v$ is a leaf. Together with the subtree size $\mathrm{size}_T(v)$ (the number of descendants of $v$, including $v$) of the referenced definition, these are the objects in which Lemma 4.3 of Bodlaender et al. is stated: its hypothesis (ii) sums the measure over the children $v_1,\dots,v_p$ of a vertex, and its hypothesis (iii) compares the measure of a vertex with that of its parent.
--
--   **Formalization Note** The condition $c \neq r$ excludes the pseudo-edge $r \to p(r) = r$ created by the total-parent-map convention, so the root is never its own child. `IsChild T v c` is the relation "$c$ is a child of $v$" and `children T v` is the set of its witnesses; the two agree by definition.
-- source:
--   Bodlaender, Drange, Dregi, Fomin, Lokshtanov and Pilipczuk, A c^k n 5-approximation algorithm for treewidth, SIAM J. Comput. 45(2) (2016), p. 349, Lemma 4.3 (ii), (iii) (children, parent)

import Mathlib
import Definitions.Def_HarelTarjan_Compressed_RootedTree

namespace TreewidthApprox.TreeMeasure

open HarelTarjan.Compressed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the rooted tree `T` (root `r`, parent map `p` with the convention `p(r) = r`), `c` is a
child of `v`, equivalently `v` is the parent of `c`: `c` is not the root and `p(c) = v`. The
condition `c ≠ r` excludes the pseudo-edge `r → p(r) = r`. -/
def IsChild (T : RootedTree V) (v c : V) : Prop :=
  c ≠ T.root ∧ T.parent c = v

/-- The set of children of `v` in the rooted tree `T` (empty when `v` is a leaf). -/
def children (T : RootedTree V) (v : V) : Finset V :=
  Finset.univ.filter (fun c => c ≠ T.root ∧ T.parent c = v)

end TreewidthApprox.TreeMeasure


