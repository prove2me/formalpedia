-- Prove2me | Definitions.Def_LawlerWCT_SeriesPar_Model
-- name    : LawlerWCT_SeriesPar_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:39:05.699833+00:00
-- url     : https://prove2.me/theorems/1a953c5f-46b4-4bdb-b5eb-188bbec41a7e
-- title:
--   §3–§5, pp. 5–11 — decomposition trees, modules, initial sets, ρ, composite jobs and the series parallel algorithm
-- statement:
--   This file sets up the objects of Lawler's series parallel algorithm for the single-machine problem of minimizing $\sum_j w_jC_j$ subject to precedence constraints. A finite job set $N$, an acyclic digraph $G=(N,A)$ whose directed paths are the precedence constraints, processing times $p_j>0$ and real weights $w_j$ are given; the objective $\sum_j w_jC_j$ and optimal sequences are the published `SingleMachinePrec.Biclique.WeightedCompletion`.
--
--   **Decomposition trees (§3, pp. 5–6).** A decomposition tree is a rooted binary tree whose leaves are jobs and whose internal nodes are marked $S$ or $P$. It builds a *transitive series parallel* digraph by rules (3.1)–(3.3): a leaf $j$ is the digraph $(\{j\},\emptyset)$; an $S$-node with sons building $(N_1,A_1)$ and $(N_2,A_2)$ builds the series composition
--   $$(N_1\cup N_2,\ A_1\cup A_2\cup N_1\times N_2),$$
--   in which every job of the left son precedes every job of the right son; a $P$-node builds the parallel composition $(N_1\cup N_2, A_1\cup A_2)$. The *leaves* of a tree are listed from left to right, and the *subtrees* of a tree are the trees rooted at its nodes.
--
--   **Modules (Definition 1, p. 6).** A nonempty $M\subseteq N$ is a *module* if every job $j\in N\setminus M$ either must precede every job of $M$, or must follow every job of $M$, or is unconstrained with respect to every job of $M$.
--
--   **Initial sets and ratios (Definitions 2–3, p. 8).** $I\subseteq M$ is an *initial set* of $M$ if, for every $j\in I$, every job of $M$ that must precede $j$ lies in $I$. The ratio of a set of jobs is
--   $$\rho(I)=\frac{\sum_{j\in I}w_j}{\sum_{j\in I}p_j}.$$
--   A nonempty initial set $I^*$ of $M$ is *$\rho$-maximal* if $\rho(I^*)\ge\rho(I)$ for every nonempty initial set $I$ of $M$.
--
--   **Composite jobs (§4, p. 9; §5, pp. 9–10).** A composite job is a nonempty sequence $c$ of distinct jobs, treated as one job with weight $\sum_{j\in c}w_j$, processing time $\sum_{j\in c}p_j$ and ratio $\rho(c)$; it arises as a $\rho$-maximal initial set of itself, so every nonempty proper prefix of $c$ has ratio at most $\rho(c)$. A list of composite jobs is in *ratio order* when the ratios are nonincreasing. A set $F$ of composite jobs *represents an optimal sequence* for $M$ if its composite jobs partition $M$ and every arrangement of $F$ in nonincreasing ratio order, each composite job expanded into its sequence, is an optimal sequence for $M$.
--
--   **The algorithm (§5, pp. 9–12).** A run proceeds bottom-up on the tree. A leaf $j$ yields $\{j\}$. A $P$-node yields the union of the sets of its sons. An $S$-node with sets $M_1$ (left) and $M_2$ (right) applies the series procedure of p. 11, with a dummy of ratio $+\infty$ in $M_1$ and one of ratio $-\infty$ in $M_2$:
--
--   1. Find a minimal-ratio $i\in M_1$ and a maximal-ratio $j\in M_2$. If $\rho(i)>\rho(j)$, the result is $M_1\cup M_2$. Otherwise remove $i$ and $j$ and form the composite job $k=(i,j)$.
--   2. (2.1) Find a minimal-ratio $i\in M_1$; if $\rho(i)>\rho(k)$ go to 3.1. (2.2) Otherwise remove $i$ and set $k=(i,k)$; return to 2.1.
--   3. (3.1) Find a maximal-ratio $j\in M_2$; if $\rho(k)>\rho(j)$, the result is $M_1\cup M_2\cup\{k\}$. (3.2) Otherwise remove $j$, set $k=(k,j)$ and go to 2.1.
--
--   Ties among minimal or maximal elements may be broken in any way; a run is any execution consistent with these rules.
--
--   **Formalization Note** Jobs have a type $\iota$ with decidable equality and $N$ is a `Finset`. "Must precede" is `Relation.TransGen G` (a directed path). Modules are stated with the disjunction of (4.1)–(4.3); for an acyclic $G$ and nonempty $M$ the three conditions are mutually exclusive, so this is the page's "exactly one". Lean evaluates $0/0$ as $0$, so $\rho(\emptyset)=0$; $\rho$-maximality ranges over nonempty initial sets and requires $I^*$ nonempty. Composite jobs and the sets of the algorithm are lists of lists of jobs; each composite list has distinct jobs, and `(i, k)` is the concatenation `i ++ k`. The algorithm is the inductive relation `Run` (with `SeriesMerge` for Step 1 and `SeriesLoop` for Steps 2–3), so every tie-breaking is allowed. The tree, the module and the ratio conditions are given relative to an arbitrary arc relation `G`; the theorems tie the tree to `G`.
-- source:
--   Lawler, Sequencing jobs to minimize total weighted completion time subject to precedence constraints, IRIA-LABORIA Rapport de Recherche No. 205 (Dec. 1976), HAL hal-04716371v1, pp. 5–11, (3.1)–(3.4), Definitions 1–3, §4 p. 9 (composite jobs), §5 pp. 9–11 (representation, Steps 1–3)

import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_WeightedCompletion

namespace LawlerWCT.SeriesPar

/-- A decomposition tree (Lawler 1976, §3, pp. 5–6): a rooted binary tree whose leaves are jobs and
whose internal nodes are marked `S` (series composition, the left son preceding the right son) or
`P` (parallel composition). -/
inductive SPTree (ι : Type*) where
  | leaf (j : ι)
  | series (l r : SPTree ι)
  | parallel (l r : SPTree ι)

namespace SPTree

variable {ι : Type*}

/-- The leaves of a decomposition tree, from left to right: the node set `N₁ ∪ N₂` of the
digraph built by rules (3.1)–(3.3). -/
def leaves : SPTree ι → List ι
  | leaf j => [j]
  | series l r => l.leaves ++ r.leaves
  | parallel l r => l.leaves ++ r.leaves

/-- The arc set of the transitive series parallel digraph built by the tree (rules (3.1)–(3.3),
p. 5): no arc for a single node, `A₁ ∪ A₂ ∪ N₁ × N₂` for a series composition and `A₁ ∪ A₂` for a
parallel composition. -/
def prec : SPTree ι → ι → ι → Prop
  | leaf _, _, _ => False
  | series l r, i, j => l.prec i j ∨ r.prec i j ∨ (i ∈ l.leaves ∧ j ∈ r.leaves)
  | parallel l r, i, j => l.prec i j ∨ r.prec i j

/-- `S.IsSubtree T`: `S` is the subtree of `T` rooted at some node of `T` (`T` itself, or a
subtree of a son of an internal node). -/
inductive IsSubtree : SPTree ι → SPTree ι → Prop
  | refl (T : SPTree ι) : IsSubtree T T
  | series_left {S l r : SPTree ι} : IsSubtree S l → IsSubtree S (series l r)
  | series_right {S l r : SPTree ι} : IsSubtree S r → IsSubtree S (series l r)
  | parallel_left {S l r : SPTree ι} : IsSubtree S l → IsSubtree S (parallel l r)
  | parallel_right {S l r : SPTree ι} : IsSubtree S r → IsSubtree S (parallel l r)

end SPTree

variable {ι : Type*}

/-- Definition 1 (p. 6): a nonempty subset `M ⊆ N` is a (job) module of the digraph with arcs `G`
if every job `j ∈ N − M` must precede every job of `M` (4.1), must follow every job of `M` (4.2),
or is not constrained with respect to any job of `M` (4.3). "Must precede" is a directed path,
`Relation.TransGen G`. For an acyclic `G` and nonempty `M` the three conditions are mutually
exclusive, so the disjunction is the page's "exactly one". -/
def IsModule (G : ι → ι → Prop) (N M : Finset ι) : Prop :=
  M.Nonempty ∧ M ⊆ N ∧ ∀ j ∈ N, j ∉ M →
    (∀ m ∈ M, Relation.TransGen G j m) ∨ (∀ m ∈ M, Relation.TransGen G m j) ∨
      (∀ m ∈ M, ¬ Relation.TransGen G j m ∧ ¬ Relation.TransGen G m j)

/-- Definition 2 (p. 8): the ratio `ρ(I) = (Σ_{j∈I} w_j) / (Σ_{j∈I} p_j)` of a set of jobs.
(Lean gives `ρ(∅) = 0`; every statement about ratios of sets ranges over nonempty sets.) -/
noncomputable def rho (p w : ι → ℝ) (I : Finset ι) : ℝ :=
  (∑ j ∈ I, w j) / (∑ j ∈ I, p j)

/-- Definition 2 (p. 8): `I ⊆ M` is an initial set of `M` if, for each `j ∈ I`, every job of `M`
that must precede `j` is in `I`. -/
def IsInitialSet (G : ι → ι → Prop) (M I : Finset ι) : Prop :=
  I ⊆ M ∧ ∀ j ∈ I, ∀ i ∈ M, Relation.TransGen G i j → i ∈ I

/-- Definition 3 (p. 8): a nonempty initial set `I` of `M` is ρ-maximal if `ρ(I) ≥ ρ(I')` for
every nonempty initial set `I'` of `M`. -/
def IsRhoMaximal (G : ι → ι → Prop) (p w : ι → ℝ) (M I : Finset ι) : Prop :=
  IsInitialSet G M I ∧ I.Nonempty ∧
    ∀ I' : Finset ι, IsInitialSet G M I' → I'.Nonempty → rho p w I' ≤ rho p w I

/-- The ratio of a composite job (§4, p. 9), represented by the sequence `c` of jobs it stands
for: its weight is the sum of the weights, its processing time the sum of the processing times. -/
noncomputable def crho (p w : ι → ℝ) (c : List ι) : ℝ :=
  (c.map w).sum / (c.map p).sum

/-- A composite job (§4, p. 9): a nonempty sequence of distinct jobs that is a ρ-maximal initial set of
itself, viewed as a chain: every nonempty proper prefix has ratio at most the ratio of the whole
sequence. -/
def IsComposite (p w : ι → ℝ) (c : List ι) : Prop :=
  c ≠ [] ∧ c.Nodup ∧
    ∀ q : List ι, q <+: c → q ≠ [] → q ≠ c → crho p w q ≤ crho p w c

/-- A list of composite jobs is in nonincreasing ratio order. -/
def IsRatioOrder (p w : ι → ℝ) (L : List (List ι)) : Prop :=
  L.Pairwise (fun a b => crho p w b ≤ crho p w a)

/-- `F` represents an optimal sequence for the set of jobs `M` (§5, pp. 9–10): `F` is a set of
composite jobs that partitions `M`, and every arrangement of `F` in nonincreasing ratio order,
with each composite job expanded into the sequence it stands for, is an optimal sequence for `M`
under the precedence constraints `G`. -/
def Represents [DecidableEq ι] (G : ι → ι → Prop) (p w : ι → ℝ) (M : Finset ι)
    (F : List (List ι)) : Prop :=
  (∀ c ∈ F, IsComposite p w c) ∧ F.flatten.Nodup ∧ (∀ j, j ∈ F.flatten ↔ j ∈ M) ∧
    ∀ L : List (List ι), L.Perm F → IsRatioOrder p w L →
      SingleMachinePrec.Biclique.IsOptimalSchedule G p w M L.flatten

/-- Steps 2 and 3 of the procedure for series composition (§5, p. 11). The state is the remaining
set `A` of `M₁`, the remaining set `B` of `M₂` and the current composite job `k`;
`SeriesLoop p w A B k F` says that a run started in this state halts with the set `F`.
* Step 2.2: a minimal-ratio `i ∈ A` with `ρ(i) ≤ ρ(k)` is removed and `k := (i, k)`.
* Step 3.2: the test of 2.1 sent the run to 3.1 (every element of `A` has ratio `> ρ(k)`; with
  `A = ∅` this is the dummy of ratio `+∞`), a maximal-ratio `j ∈ B` has `ρ(k) ≤ ρ(j)`, it is
  removed and `k := (k, j)`.
* Step 3.1 halt: every element of `A` has ratio `> ρ(k)` and every element of `B` ratio `< ρ(k)`
  (with `B = ∅` the dummy of ratio `−∞`); the result is `A ∪ B ∪ {k}`.
Ties among minimal or maximal elements are broken arbitrarily. -/
inductive SeriesLoop [DecidableEq ι] (p w : ι → ℝ) :
    List (List ι) → List (List ι) → List ι → List (List ι) → Prop
  | step2_2 {A B : List (List ι)} {k i : List ι} {F : List (List ι)} :
      i ∈ A → (∀ a ∈ A, crho p w i ≤ crho p w a) → crho p w i ≤ crho p w k →
      SeriesLoop p w (A.erase i) B (i ++ k) F → SeriesLoop p w A B k F
  | step3_2 {A B : List (List ι)} {k j : List ι} {F : List (List ι)} :
      (∀ a ∈ A, crho p w k < crho p w a) → j ∈ B → (∀ b ∈ B, crho p w b ≤ crho p w j) →
      crho p w k ≤ crho p w j →
      SeriesLoop p w A (B.erase j) (k ++ j) F → SeriesLoop p w A B k F
  | halt {A B : List (List ι)} {k : List ι} :
      (∀ a ∈ A, crho p w k < crho p w a) → (∀ b ∈ B, crho p w b < crho p w k) →
      SeriesLoop p w A B k (A ++ B ++ [k])

/-- Step 1 of the procedure for series composition (§5, p. 11), applied to the sets `F₁` (for
`M₁`) and `F₂` (for `M₂`); `SeriesMerge p w F₁ F₂ F` says that a run halts with the set `F`.
* halt: a minimal-ratio element of `F₁` has ratio `>` a maximal-ratio element of `F₂` (vacuous if
  either side is empty, by the dummies of ratio `±∞`); the result is `F₁ ∪ F₂`.
* otherwise: a minimal-ratio `i ∈ F₁` and a maximal-ratio `j ∈ F₂` with `ρ(i) ≤ ρ(j)` are removed,
  the composite job `k = (i, j)` is formed and the run continues with Step 2.1. -/
inductive SeriesMerge [DecidableEq ι] (p w : ι → ℝ) :
    List (List ι) → List (List ι) → List (List ι) → Prop
  | halt {F₁ F₂ : List (List ι)} :
      (∀ i ∈ F₁, ∀ j ∈ F₂, crho p w j < crho p w i) → SeriesMerge p w F₁ F₂ (F₁ ++ F₂)
  | merge {F₁ F₂ : List (List ι)} {i j : List ι} {F : List (List ι)} :
      i ∈ F₁ → (∀ a ∈ F₁, crho p w i ≤ crho p w a) →
      j ∈ F₂ → (∀ b ∈ F₂, crho p w b ≤ crho p w j) → crho p w i ≤ crho p w j →
      SeriesLoop p w (F₁.erase i) (F₂.erase j) (i ++ j) F → SeriesMerge p w F₁ F₂ F

/-- A run of the series parallel algorithm (§5, pp. 9–12) on a decomposition tree, bottom-up:
`Run p w T F` says that the run produces the set `F` of (possibly composite) jobs for the module
of the tree `T`. A leaf `j` gives `{j}`; a `P`-node gives the union of the sets of its sons; an
`S`-node applies the series procedure (Steps 1–3) to the sets of its left and right sons. -/
inductive Run [DecidableEq ι] (p w : ι → ℝ) : SPTree ι → List (List ι) → Prop
  | leaf (j : ι) : Run p w (.leaf j) [[j]]
  | parallel {l r : SPTree ι} {F₁ F₂ : List (List ι)} :
      Run p w l F₁ → Run p w r F₂ → Run p w (.parallel l r) (F₁ ++ F₂)
  | series {l r : SPTree ι} {F₁ F₂ F : List (List ι)} :
      Run p w l F₁ → Run p w r F₂ → SeriesMerge p w F₁ F₂ F → Run p w (.series l r) F

end LawlerWCT.SeriesPar


