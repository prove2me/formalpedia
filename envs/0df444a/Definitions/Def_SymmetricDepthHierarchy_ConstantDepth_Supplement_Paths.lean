-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Paths
-- name    : SymmetricDepthHierarchy_ConstantDepth_Supplement_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:54:46.304917+00:00
-- url     : https://prove2.me/theorems/89dee5d3-345d-4cb8-9bac-458edf79ed1d
-- title:
--   The vertex-indexed bipartite path and root-path vertex budgets
-- statement:
--   The pattern $P_m$ has $m$ vertices, edges between consecutive vertices, and alternating sides starting on the left. Thus it has $m-1$ edges when $m\ge1$; multiplicities are one.
--
--   For a finite simple graph $G$, membership in $\mathcal T_q^K$ means that a rooted tree decomposition has bags of size at most $K$ and at most $q$ distinct vertices in the union of bags on every root-to-node path:
--   $$\left|\bigcup_{s\text{ ancestor of }t}\beta(s)\right|\le q.$$
--   For a finite tree this is equivalent to the source's root-leaf condition. These definitions use the published decomposition primitives and the independently published ordinary pathwidth predicate, without substituting a depth bound for a distinct-vertex budget.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), p. 9, 41, 43 (PDF p. 12, 44, 46), §§2.4, C.1, C.3.1; source.pdf sha256 e2d54636eb14a5004f0538279b05a710bdf6487b706704a71bea70f01e7b4c42

import Mathlib
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Pattern
import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Forestwidth
import Definitions.Def_RobersonCx_TwLE

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement


/-- The m-vertex path; the first vertex is on the left. §4 / C.1. -/
def pathPattern (m : ℕ) : Pattern where
  A := {i : Fin m // Even i.val}
  B := {i : Fin m // ¬ Even i.val}
  mult a b := if a.val.val + 1 = b.val.val ∨ b.val.val + 1 = a.val.val then 1 else 0

/-- C.3.1: a width-K decomposition whose root paths use at most q distinct vertices. -/
def inT {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (K q : ℕ) : Prop :=
  ∃ (T : Type) (_ : Fintype T) (D : TreeDecomp G T),
    (∀ t, (D.bag t).card ≤ K) ∧
    ∀ t, (Finset.univ.filter (fun v => ∃ s,
      Relation.ReflTransGen (fun a b => b ≠ D.root ∧ D.parent b = a) s t ∧
      v ∈ D.bag s)).card ≤ q

end SymmetricDepthHierarchy.ConstantDepth.Supplement


