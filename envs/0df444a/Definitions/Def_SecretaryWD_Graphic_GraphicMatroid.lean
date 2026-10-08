-- Prove2me | Definitions.Def_SecretaryWD_Graphic_GraphicMatroid
-- name    : SecretaryWD_Graphic_GraphicMatroid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:49:07.26958+00:00
-- url     : https://prove2.me/theorems/fa61eaec-8aa2-4b7a-9c9a-8fa17e0ec7c1
-- title:
--   Graphic matroid, OPT, partition matroids, and the α-partition property (Definition 5.1)
-- statement:
--   Let $V$ be a finite vertex set. Edges are unordered pairs $\{u,w\}$ of vertices, and a graph is given by its finite edge set $E$.
--
--   **Graphic matroid.** A set $S$ of edges is *independent* (acyclic) if the graph $(V,S)$ contains no cycle. For edge values $v$, the optimum is
--   $$\mathrm{OPT}(E,v)=\max\Big\{\sum_{e\in S} v(e) : S\subseteq E,\ S \text{ acyclic}\Big\},$$
--   which exists because the empty set is acyclic. For nonnegative $v$ it is the value of a max-weight base (spanning forest).
--
--   **Partition matroids.** A *partition* of a subset $U'\subseteq E$ is a finite family $P$ of nonempty, pairwise disjoint parts, each contained in $E$; $U'$ is their union. A set $S$ is independent in the partition matroid of $P$ if every element of $S$ lies in some part and $S$ contains at most one element of each part. For nonnegative values the max-weight base of this partition matroid takes the most valuable element of every part, so its value is
--   $$\mathrm{val}(P,v)=\sum_{p\in P}\max_{e\in p} v(e).$$
--
--   **Expectation under a random partition.** For a probability mass function $\mu$ on finite families of parts, $\mathbb E_{P\sim\mu}[f(P)]=\sum_P \mu(P)\,f(P)$.
--
--   **Definition 5.1 ($\alpha$-partition property).** A random partition $\mu$ is an *$\alpha$-partition scheme* for the graphic matroid on $E$ if
--   1. every partition $P$ in the support of $\mu$ is a partition of a subset of $E$ and every set independent in its partition matroid is acyclic; and
--   2. for **every** nonnegative valuation $v$,
--   $$\mathrm{OPT}(E,v)\le \alpha\cdot \mathbb E_{P\sim\mu}\big[\mathrm{val}(P,v)\big].$$
--   The graphic matroid on $E$ *satisfies an $\alpha$-partition property* if some $\alpha$-partition scheme exists.
--
--   The law $\mu$ is chosen before the values: it may depend on the graph but not on $v$. This order of quantifiers is the content of the definition; if the partition could depend on $v$, every matroid would satisfy a $1$-partition property (take singleton parts of an optimal base).
--
--   **Formalization Note.** The paper's bound "$E(\cdot)\ge 1/\alpha\times$ value" is written multiplicatively. The independence condition must hold for every partition in the support, not on average. The maximum over a part is `Finset.sup'`, with the value $0$ on an empty part, which never occurs in a partition. Values are real numbers; nonnegativity is a hypothesis of the second condition.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 9, Section 5 (graphic and partition matroids) and Definition 5.1

import Mathlib

namespace SecretaryWD.Graphic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite edge set `S` is independent in the graphic matroid (p. 9): the graph on `V` with
edge set `S` contains no cycle. -/
def IsAcyclicSet (S : Finset (Sym2 V)) : Prop :=
  (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).IsAcyclic

theorem isAcyclicSet_empty : IsAcyclicSet (∅ : Finset (Sym2 V)) := by
  simp [IsAcyclicSet, SimpleGraph.isAcyclic_bot]

open Classical in
/-- The independent sets of the graphic matroid on the edge set `E`: the acyclic subsets of `E`. -/
noncomputable def acyclicSubsets (E : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) :=
  E.powerset.filter IsAcyclicSet

theorem empty_mem_acyclicSubsets (E : Finset (Sym2 V)) : ∅ ∈ acyclicSubsets E := by
  classical
  simp only [acyclicSubsets, Finset.mem_filter, Finset.empty_mem_powerset, true_and]
  exact isAcyclicSet_empty

/-- `OPT(G)`: the value of a max-weight independent set of the graphic matroid on `E`,
`max { ∑_{e ∈ S} v e : S ⊆ E acyclic }` (the maximum exists: `∅` is acyclic). -/
noncomputable def OPT (E : Finset (Sym2 V)) (v : Sym2 V → ℝ) : ℝ :=
  (acyclicSubsets E).sup' ⟨∅, empty_mem_acyclicSubsets E⟩ fun S => ∑ e ∈ S, v e

/-- `P` is a partition matroid on a subset `U' = ⋃ P` of the ground set `E` (p. 9): a finite
family of nonempty, pairwise disjoint parts, each contained in `E`. -/
def IsPartitionOf (E : Finset (Sym2 V)) (P : Finset (Finset (Sym2 V))) : Prop :=
  (∀ p ∈ P, p.Nonempty ∧ p ⊆ E) ∧ (P : Set (Finset (Sym2 V))).PairwiseDisjoint id

/-- `S` is independent in the partition matroid with parts `P` (p. 9): every element of `S`
lies in some part (so `S ⊆ U'`), and `S` has at most one element from each part. -/
def IsPartIndep (P : Finset (Finset (Sym2 V))) (S : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ S, ∃ p ∈ P, e ∈ p) ∧ ∀ p ∈ P, (S ∩ p).card ≤ 1

/-- The largest value in a part (`0` on an empty part, which never occurs in a partition). -/
noncomputable def partMax (p : Finset (Sym2 V)) (v : Sym2 V → ℝ) : ℝ :=
  if h : p.Nonempty then p.sup' h v else 0

/-- The value of a max-weight base of the partition matroid with parts `P`, for nonnegative
values: the sum over the parts of the largest value in the part. -/
noncomputable def partitionValue (P : Finset (Finset (Sym2 V))) (v : Sym2 V → ℝ) : ℝ :=
  ∑ p ∈ P, partMax p v

/-- The expectation of a real function `f` under a probability mass function `μ` on a finite
type: `∑_a μ(a) · f(a)`. -/
noncomputable def pmfExp {α : Type*} [Fintype α] (μ : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (μ a).toReal * f a

/-- Definition 5.1 for the graphic matroid on `E`, for a given random partition `μ`: the law `μ`
is fixed first (it may depend on `E` only), and then
* every partition `P` in the support of `μ` is a partition matroid on a subset of `E` whose
  independent sets are all independent (acyclic) in the graphic matroid, and
* for **every** nonnegative valuation `v`, `OPT(E, v) ≤ α · E_{P∼μ}[value of max-weight base of P]`
  (the paper's `E(…) ≥ 1/α × OPT`, written multiplicatively). -/
def IsPartitionScheme (E : Finset (Sym2 V)) (μ : PMF (Finset (Finset (Sym2 V)))) (α : ℝ) :
    Prop :=
  (∀ P ∈ μ.support, IsPartitionOf E P ∧ ∀ S : Finset (Sym2 V), IsPartIndep P S → IsAcyclicSet S) ∧
    ∀ v : Sym2 V → ℝ, (∀ e, 0 ≤ v e) →
      OPT E v ≤ α * pmfExp μ fun P => partitionValue P v

/-- Definition 5.1: the graphic matroid on `E` satisfies an `α`-partition property if some
random partition `μ` is an `α`-partition scheme for it. -/
def SatisfiesPartitionProperty (E : Finset (Sym2 V)) (α : ℝ) : Prop :=
  ∃ μ : PMF (Finset (Finset (Sym2 V))), IsPartitionScheme E μ α

end SecretaryWD.Graphic


