-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Supplement_Hierarchies
-- name    : LeeCutCertificates_Certificate_Supplement_Hierarchies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:03:15.589203+00:00
-- url     : https://prove2.me/theorems/26f8bd44-eb70-4d6b-9cbb-d72eaa9c5aef
-- title:
--   Canonical hierarchies, universal promises and terminal guards
-- statement:
--   A hierarchy is a rooted terminal tree whose terminals have no children. Unary nodes and nonterminal leaves are allowed. For each node $u$, let $A_u$ be its descendant terminals. The canonical parent-edge capacity is computed from the input:
--
--   $$d_u=c_G(A_u),\qquad R_{T,G}(S)=\min_{X:\,X\cap V=S}\sum_{u\ne\mathrm{root}}d_u\,\boldsymbol{1}_{\text{labels differ}}.$$
--
--   A promise with bound $B$ requires $R_{T,G}(S^*)\le B\lambda(G)$ for every minimum-cut shore. Repeated clusters and clusters equal to the empty or full terminal set are retained. A terminal guard for a known capacitated tree is a nonnegative explicit graph $J$ satisfying $R_T(S)\le c_J(S)\le42R_T(S)$ for every terminal shore. A refinement's raw output includes a topology and learned capacities; their canonicity and new promise remain theorem conclusions.
--
--   **Formalization Note** No depth, binary-branching or initial node-count restriction is bundled into the hierarchy. Budgets retain the actual number of nonroot nodes.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §9, printed p.26 (PDF p.27), equation (27); Lemma 26, printed p.29 (PDF p.30); §10.2, printed p.31 (PDF p.32)

import Definitions.Def_LeeCutCertificates_Certificate_Supplement_TerminalTrees

set_option autoImplicit false
open Classical
open SunMinCut.Cactus

namespace LeeCutCertificates.Certificate.Supplement

/-- Section 9's general input, including unary nodes and nonterminal leaves. -/
structure Hierarchy (n : ℕ) extends TerminalTree n where
  terminal_childless : ∀ v u, u ≠ tree.root → tree.parent u ≠ terminal v

noncomputable def Hierarchy.cluster {n : ℕ} (T : Hierarchy n) (u : Fin T.nodes) :
    Finset (Fin n) := Finset.univ.filter fun v => T.tree.Ancestor u (T.terminal v)

/-- Canonical capacities are computed from the graph, not arbitrary supplied weights. -/
noncomputable def Hierarchy.canonical {n m : ℕ} (T : Hierarchy n) (G : Graph n m) :
    Fin T.nodes → ℝ := fun u => cutw G (T.cluster u)

noncomputable def Hierarchy.rep {n m : ℕ} (T : Hierarchy n) (G : Graph n m)
    (S : Finset (Fin n)) : ℝ := T.toTerminalTree.rep (T.canonical G) S

def Hierarchy.Promise {n m : ℕ} (T : Hierarchy n) (G : Graph n m) (B : ℝ) : Prop :=
  ∀ S, IsMinCut G S → T.rep G S ≤ B * lam G

/-- Offline known capacities: no canonicity or positivity is required for a guard. -/
def TerminalGuard {n : ℕ} (T : CapacitatedTree n) (J : Σ m : ℕ, Graph n m) : Prop :=
  Nonnegative J.2 ∧ ∀ S, T.toTerminalTree.rep T.capacity S ≤ cutw J.2 S ∧
    cutw J.2 S ≤ 42 * T.toTerminalTree.rep T.capacity S

/-- A refinement supplies its learned canonical capacities as explicit data. -/
structure RefinedHierarchy (n : ℕ) where
  topology : Hierarchy n
  capacity : Fin topology.nodes → ℝ

end LeeCutCertificates.Certificate.Supplement


