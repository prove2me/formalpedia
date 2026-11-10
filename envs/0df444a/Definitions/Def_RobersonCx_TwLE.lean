-- Prove2me | Definitions.Def_RobersonCx_TwLE
-- name    : RobersonCx_TwLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:57.827163+00:00
-- url     : https://prove2.me/theorems/2306639b-acd4-4abb-bc80-97c6ffb8a857
-- title:
--   Tree and path decompositions; $\mathrm{tw}(G)\le k$ and $\mathrm{pw}(G)\le k$
-- statement:
--   A **tree decomposition** of a graph $G$ is a pair $(T,(W_t)_{t\in V(T)})$ where $T$ is a tree and each bag $W_t\subseteq V(G)$, such that
--
--   1. $V(G)=\bigcup_{t}W_t$;
--   2. for every edge $xy\in E(G)$ some bag contains both $x$ and $y$;
--   3. for every $x\in V(G)$ the nodes $\{t: x\in W_t\}$ induce a connected subtree of $T$.
--
--   Its width is $\max_t|W_t|-1$; the **treewidth** $\mathrm{tw}(G)$ is the minimum width. A **path decomposition** is a tree decomposition whose tree is a path; the minimum width is the **pathwidth** $\mathrm{pw}(G)$.
--
--   The width bounds of Appendix A (Lemmas 13–18) are what force a minor model to follow the Hamilton cycles in the exclusion proof.
--
--   **Formalization Note** Both parameters are Prop-valued: `TwLE G k` means $\mathrm{tw}(G)\le k$ and `PwLE G k` means $\mathrm{pw}(G)\le k$; "$\mathrm{tw}(G)=k$" ($k\ge1$) is written `TwLE G k ∧ ¬ TwLE G (k - 1)`. Trees are finite graphs in `Type` (Mathlib's `IsTree`, which includes nonemptiness). Tree-decomposition bag sizes are measured with `Set.encard`. A path decomposition is the published `GaussianSweep.IsPathDecomposition` (a nonempty sequence of `Finset` bags covering vertices and edges, the bags containing a vertex consecutive), which is a tree decomposition over a path because a set of nodes of a path is connected iff it is an interval.
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. A.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_GaussianSweep_IsPathDecomposition

set_option autoImplicit false

namespace RobersonCx

/-- `(T, (W_t))` is a tree decomposition of `G` (Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), App. A.2, p.13 (PDF p.15)): `T` is a tree and
(i) every vertex of `G` lies in some bag; (ii) for every edge `xy` some bag contains both `x` and `y`;
(iii) for every vertex `x` the nodes whose bags contain `x` induce a connected subtree of `T`. -/
def IsTreeDecomp {V T : Type*} (G : SimpleGraph V) (TG : SimpleGraph T) (bag : T → Set V) : Prop :=
  TG.IsTree ∧ (∀ x : V, ∃ t, x ∈ bag t) ∧ (∀ x y : V, G.Adj x y → ∃ t, x ∈ bag t ∧ y ∈ bag t) ∧
    ∀ x : V, (TG.induce {t | x ∈ bag t}).Connected

/-- `TwLE G k`: `tw(G) ≤ k` (App. A.2, p.13): `G` has a tree decomposition of width at most `k`, i.e. with all
bags of size at most `k + 1`.

**Formalization Note** Treewidth is Prop-valued: "`tw(G) ≤ k`" is `TwLE G k` and "`tw(G) = k`" (`k ≥ 1`) is
`TwLE G k ∧ ¬ TwLE G (k - 1)`. The tree is a finite graph in `Type` (Mathlib's `IsTree` includes connectedness,
hence nonemptiness). Bag sizes are measured with `Set.encard`, so an infinite bag never satisfies the bound. -/
def TwLE {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (T : Type) (_ : Finite T) (TG : SimpleGraph T) (bag : T → Set V),
    IsTreeDecomp G TG bag ∧ ∀ t, (bag t).encard ≤ ((k + 1 : ℕ) : ℕ∞)

/-- `PwLE G k`: `pw(G) ≤ k` (App. A.2, p.13): `G` has a path decomposition (a tree decomposition whose tree is
a path) with all bags of size at most `k + 1`.

**Formalization Note** A path decomposition is the published `GaussianSweep.IsPathDecomposition`: a nonempty
sequence of bags `W : Fin s → Finset V` (`0 < s`) covering every vertex and every edge, in which the bags
containing a vertex are consecutive. A set of nodes of a path induces a connected subgraph iff it is an interval,
so this is the paper's tree decomposition over a path. The width bound is `(W i).card ≤ k + 1`. -/
def PwLE {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (s : ℕ) (W : Fin s → Finset V), GaussianSweep.IsPathDecomposition G s W ∧ ∀ i, (W i).card ≤ k + 1

end RobersonCx


