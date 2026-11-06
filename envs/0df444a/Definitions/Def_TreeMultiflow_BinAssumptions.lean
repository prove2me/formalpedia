-- Prove2me | Definitions.Def_TreeMultiflow_BinAssumptions
-- name    : TreeMultiflow_BinAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:14.099238+00:00
-- url     : https://prove2.me/theorems/4c13a21f-1790-4d07-8a5c-abdc1c280193
-- title:
--   Assumptions of Theorem 3.1: leaf-to-leaf paths with prescribed bins
-- statement:
--   Let a tree have positive integer edge capacities $u_e$, and let $P$ be a finite collection of labeled paths, path $p$ joining $a_p$ and $b_p$. At each leaf the paths ending there are partitioned into **prescribed bins**, given by a label of every path end: the bin with label $k$ at the leaf $\ell$ consists of the paths having an end at $\ell$ labeled $k$. The **assumptions of Theorem 3.1** are:
--
--   1. every path joins two distinct leaves;
--   2. (i) every bin contains at most six paths;
--   3. (ii) a leaf with incident edge $e$ has at most $u_e$ (nonempty) bins;
--   4. (iii) every internal edge $e$ is used by at most $4u_e+2$ paths.
--
--   Theorem 5.2 is stated under these assumptions.
--
--   **Formalization Note** A labeling of the ends is the same as a partition of the paths ending at each leaf into nonempty bins. Since the two endpoints of a path differ, counting ends in a bin counts paths. Condition (iii) concerns internal edges only, as printed.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Theorem 3.1, p.6 (assumptions (i)–(iii))

import Mathlib
import Definitions.Def_TreeMultiflow_load
import Definitions.Def_TreeMultiflow_IsLeaf
import Definitions.Def_TreeMultiflow_IsInternalEdge
import Definitions.Def_TreeMultiflow_pathEnd

namespace TreeMultiflow

open Classical in
/-- **The assumptions of Theorem 3.1: labeled leaf-to-leaf paths with prescribed bins.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Theorem 3.1,
p.6: "let a finite collection of labeled paths, each joining two distinct leaves, be given. At each
leaf, suppose the paths ending there are partitioned into prescribed bins. Assume that (i) every bin
contains at most six paths; (ii) a leaf with incident edge e has at most uₑ bins; (iii) every
internal edge e is used by at most 4uₑ + 2 paths."

The paths are a finite index type `P`; path `p` joins `a p` and `b p`. The end of `p` at `a p` is
`(p, false)` and the end at `b p` is `(p, true)` (see `pathEnd`). The bins are prescribed by a
label `bin ξ` for each end `ξ`: the bin with label `k` at the leaf `ℓ` consists of the paths with
an end `ξ` at `ℓ` with `bin ξ = k`. `BinAssumptions G u a b bin` is the conjunction of

1. every path joins two distinct leaves;
2. (i) every bin contains at most six path ends;
3. (ii) at a leaf `ℓ`, for its incident edge `e`, the number of distinct labels used at `ℓ`
   (the number of nonempty bins) is at most `u e`;
4. (iii) every internal edge `e` is used by at most `4 u e + 2` paths.

**Formalization Note.** A labeling of the ends is the same as a partition of the paths ending at
each leaf into (nonempty) bins; since `a p ≠ b p`, a path has at most one end at each leaf, so
counting ends in a bin is counting paths. Condition (iii) is on internal edges only, as printed;
the load of the paths is `load G a b univ`. -/
def BinAssumptions {V P κ : Type*} [Fintype P] (G : SimpleGraph V) (u : Sym2 V → ℕ)
    (a b : P → V) (bin : P × Bool → κ) : Prop :=
  (∀ p, a p ≠ b p ∧ IsLeaf G (a p) ∧ IsLeaf G (b p)) ∧
  (∀ (ℓ : V) (k : κ),
    (Finset.univ.filter fun ξ : P × Bool => pathEnd a b ξ = ℓ ∧ bin ξ = k).card ≤ 6) ∧
  (∀ ℓ : V, IsLeaf G ℓ → ∀ e ∈ G.edgeSet, ℓ ∈ e →
    ((Finset.univ.filter fun ξ : P × Bool => pathEnd a b ξ = ℓ).image bin).card ≤ u e) ∧
  (∀ e : Sym2 V, IsInternalEdge G e → load G a b Finset.univ e ≤ 4 * u e + 2)

end TreeMultiflow


