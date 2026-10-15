-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
-- name    : OAI_Combinatorics_ParityLifts_DecompositionCuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:08:16.090974+00:00
-- url     : https://prove2.me/theorems/2c9ac8c9-0b4d-445b-8a46-fd493d2bcfa6
-- title:
--   Rooted cut systems and reduced cut decompositions
-- statement:
--   This file axiomatizes the vertex cuts of a rooted tree decomposition, in the form used by the choice-extraction argument.
--
--   1. **Rooted cut systems.** A rooted cut system on a set $W$ consists of a finite tree on the nodes $[N]=\{0,\dots,N-1\}$ with a root $\rho$ and a parent map $\mathrm{par}$ satisfying $\mathrm{par}(i)<i$ for every $i\ne\rho$ (parents are listed before their children), together with a bag $B_i\subseteq W$ and a side $A_i\subseteq W$ for every node $i$. No validity conditions are imposed at this stage.
--   2. **Separators and reverse sides.** For a node $i$, $S_i=B_i\cap B_{\mathrm{par}(i)}$, and (for finite $W$) $\overline{A}_i=W\setminus(S_i\cup A_i)$.
--   3. **Branches at a node.** At node $i$, the branch indexed by $j\in[N]$ and its separator are
--   $$
--   \mathrm{br}_i(j)=\begin{cases}\overline{A}_i&\text{if } j=i\ne\rho,\\ A_j&\text{if } j\ne i,\ j\ne\rho,\ \mathrm{par}(j)=i,\\ \varnothing&\text{otherwise,}\end{cases}\qquad \mathrm{sep}_i(j)=\begin{cases}S_i&\text{if } j=i\ne\rho,\\ S_j&\text{if } j\ne i,\ j\ne\rho,\ \mathrm{par}(j)=i,\\ \varnothing&\text{otherwise.}\end{cases}
--   $$
--   So the branch towards the parent is indexed by $i$ itself, each child branch by the child, and all other indices give empty branches.
--   4. **Reduced cut decompositions.** For a graph $F$ on a finite set $W$ and $t\in\mathbb{N}$, a reduced cut decomposition of $F$ of width $t$ is a rooted cut system such that
--      - $|B_i|\le t$ for every node $i$, and $|S_i|<t$ for every node $i\ne\rho$;
--      - for every $i\ne\rho$: $A_i\cap S_i=\varnothing$, and every $F$-neighbour of a vertex of $A_i$ that lies outside $A_i$ belongs to $S_i$;
--      - for every node $i$, the bag $B_i$ and the branches $\mathrm{br}_i(j)$, $j\in[N]$, are pairwise disjoint and together cover $W$.
--   5. **Region map.** For a reduced cut decomposition and a node $i$, $\mathrm{reg}_i(x)=\bot$ if $x\in B_i$, and otherwise $\mathrm{reg}_i(x)$ is the index $j$ of the branch $\mathrm{br}_i(j)$ containing $x$ (unique by disjointness).
--
--   The strict bound $|S_i|<t$ is the reduced form of a tree decomposition with bags of size at most $t$; it guarantees that every separator misses at least one of the $t$ main types of the template. The axioms contain no parity or homomorphism condition. Results built on this file extract, from any reduced cut decomposition of $F$ and any weighted witness for a homomorphism $F\to T_t$ with star parity (for $t\ge1$), a balanced star at a suitable node, using the region map there as its vertex partition; reduced bag trees provide such decompositions.
--
--   **Formalization Note** `RootedCuts W` has fields `nodes`, `root`, `parent`, `parent_lt`, `bag`, `side`, with nodes in `Fin nodes`; `separator`, `reverseSide`, `branch` and `branchSeparator` are items 2 and 3. `ReducedCutDecomposition F t` extends it with `width`, `intersection`, `side_disjoint`, `boundary`, `bag_disjoint`, `branch_disjoint`, `vertex_cover`, and `ReducedCutDecomposition.region` uses a choice of covering branch, with values in an `Option` type.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/DecompositionCuts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/DecompositionCuts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section DecompositionCuts

open scoped Classical

/-- A finite rooted tree is indexed in parent-before-child order. The cuts below
are the vertex sides of its edges. Validity is recorded separately. -/
structure RootedCuts (W : Type) where
  nodes : ℕ
  root : Fin nodes
  parent : Fin nodes → Fin nodes
  parent_lt : ∀ i, i ≠ root → parent i < i
  bag : Fin nodes → Finset W
  side : Fin nodes → Finset W

variable {W : Type} [Fintype W]

noncomputable def RootedCuts.separator (D : RootedCuts W) (i : Fin D.nodes) : Finset W :=
  D.bag i ∩ D.bag (D.parent i)

noncomputable def RootedCuts.reverseSide (D : RootedCuts W) (i : Fin D.nodes) : Finset W :=
  Finset.univ \ (D.separator i ∪ D.side i)

/-- At node `i`, region `i` is the parent branch; a child is indexed by itself.
All other regions are empty. -/
noncomputable def RootedCuts.branch (D : RootedCuts W) (i j : Fin D.nodes) : Finset W :=
  if j = i then (if i = D.root then ∅ else D.reverseSide i)
  else if j ≠ D.root ∧ D.parent j = i then D.side j else ∅

noncomputable def RootedCuts.branchSeparator (D : RootedCuts W)
    (i j : Fin D.nodes) : Finset W :=
  if j = i then (if i = D.root then ∅ else D.separator i)
  else if j ≠ D.root ∧ D.parent j = i then D.separator j else ∅

/-- Standard finite tree-decomposition cuts: the incident outer sides and the
bag partition the graph, and each cut is separated by the intersection of the
incident bags. The strict intersection bound is the reduced form. No parity
or graph-homomorphism property is part of this definition. -/
structure ReducedCutDecomposition (F : SimpleGraph W) (t : ℕ) extends RootedCuts W where
  width : ∀ i, (bag i).card ≤ t
  intersection : ∀ i, i ≠ root → (toRootedCuts.separator i).card < t
  side_disjoint : ∀ i, i ≠ root → Disjoint (side i) (toRootedCuts.separator i)
  boundary : ∀ i, i ≠ root → ∀ x ∈ side i, ∀ y,
    F.Adj x y → y ∉ side i → y ∈ toRootedCuts.separator i
  bag_disjoint : ∀ i j, Disjoint (bag i) (toRootedCuts.branch i j)
  branch_disjoint : ∀ i j k, j ≠ k →
    Disjoint (toRootedCuts.branch i j) (toRootedCuts.branch i k)
  vertex_cover : ∀ i x, x ∈ bag i ∨ ∃ j, x ∈ toRootedCuts.branch i j

variable {F : SimpleGraph W} {t : ℕ}

noncomputable def ReducedCutDecomposition.region (D : ReducedCutDecomposition F t)
    (i : Fin D.nodes) (x : W) : Option (Fin D.nodes) :=
  if h : x ∈ D.bag i then none else
    some (Classical.choose ((D.vertex_cover i x).resolve_left h))

variable {a : F →g template t}

end DecompositionCuts

end ParityWL

end OAI


