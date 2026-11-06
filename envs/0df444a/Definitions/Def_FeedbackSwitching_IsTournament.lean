-- Prove2me | Definitions.Def_FeedbackSwitching_IsTournament
-- name    : FeedbackSwitching_IsTournament
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:58.215879+00:00
-- url     : https://prove2.me/theorems/d858cbdd-831d-4d31-bf94-4af2ceddebde
-- title:
--   Tournaments, closed neighbourhoods $\overline N^+(s)$, spanning strongly observable tournaments, observed orientations
-- statement:
--   A **tournament** on $[K]$ has exactly one directed edge $i\to j$ or $j\to i$ between each pair of distinct vertices; its self-loops are specified separately.
--
--   1. The **closed combinatorial neighbourhood** of $s$ is $\overline N^+(s)=\{s\}\cup\{j:s\to j\}$; including $s$ does not assert that its raw loss is observed.
--   2. A **spanning strongly observable tournament** contained in $G$ is a tournament on all $K$ vertices together with a set of retained self-loops, both contained in $E$, that is strongly observable using only these: every vertex has a retained self-loop or receives an edge from every other vertex.
--   3. An **observed orientation** of $G$ is a tournament in which the source $s$ of every edge $s\to j$ observes both losses, $(s,s)\in E$ and $(s,j)\in E$, so that playing $s$ reveals $\Delta_t(s,j)=\ell_t(s)-\ell_t(j)$.
--   4. An orientation **computed by a pairwise rule** orients each pair $i<j$ by one fixed rule applied to the four graph entries $(i,i),(i,j),(j,i),(j,j)$.
--
--   The last notion encodes the clause "in $O(K^2)$ graph operations" of Proposition 1.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), §3.2 and Proposition 1, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_FASTournament_IsTournament
import Definitions.Def_FeedbackSwitching_FeedbackGraph

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

**Tournament** (p.14 = PDF p.16): exactly one directed edge between each pair of distinct
vertices; `A i j` is the paper's `i → j`. This is the published `FASTournament.IsTournament` of the
digraph with adjacency `A`. "We specify its self-loops separately", so a tournament carries no
loops (`¬ A i i`); retained self-loops are a separate predicate. -/
def IsTournament {K : ℕ} (A : Fin K → Fin K → Prop) : Prop :=
  FASTournament.IsTournament (⟨A⟩ : Digraph (Fin K))

/-- The closed combinatorial neighbourhood `N⁺(s) = {s} ∪ {j : s → j}` (p.15 = PDF p.17):
`closedOut A s j` means `j ∈ N⁺(s)`. Including `s` does not assert that its raw loss is
observed. -/
def closedOut {K : ℕ} (A : Fin K → Fin K → Prop) (s j : Fin K) : Prop :=
  j = s ∨ A s j

/-- A **spanning strongly observable tournament** contained in `G` (p.14): a tournament `A` on all
`K` vertices together with a set `L` of retained self-loops, both contained in `E`, that is
strongly observable using only its retained edges and self-loops: every vertex has a retained
self-loop or receives an edge of `A` from every other vertex. -/
def IsSpanningSOTournament {K : ℕ} (G : FeedbackGraph K) (A : Fin K → Fin K → Prop)
    (L : Fin K → Prop) : Prop :=
  IsTournament A ∧ (∀ i j, A i j → G i j) ∧ (∀ i, L i → G i i) ∧
    ∀ i, L i ∨ ∀ j, j ≠ i → A j i

/-- A tournament orientation of `G` such that playing `s` reveals `Δ_t(s, j) = ℓ_t(s) − ℓ_t(j)`
for every edge `s → j`, i.e. the source `s` observes both losses (Proposition 1, p.14). -/
def IsObservedOrientation {K : ℕ} (G : FeedbackGraph K) (A : Fin K → Fin K → Prop) : Prop :=
  IsTournament A ∧ ∀ s j, A s j → G s s ∧ G s j

/-- The orientation obtained by applying one rule to the four graph entries of each pair:
for `i < j`, orient `i → j` iff `rule (G i i) (G i j) (G j i) (G j j)`, and `j → i` otherwise.

**Formalization Note.** This is the encoding of "in `O(K²)` graph operations" of Proposition 1
(p.14: "Selecting the directions inspects at most a constant number of graph entries per pair"):
an orientation computed pair by pair from a fixed number of graph entries. -/
def orientByRule {K : ℕ} (rule : Prop → Prop → Prop → Prop → Prop) (G : FeedbackGraph K) :
    Fin K → Fin K → Prop :=
  fun i j => (i < j ∧ rule (G i i) (G i j) (G j i) (G j j)) ∨
    (j < i ∧ ¬ rule (G j j) (G j i) (G i j) (G i i))

end FeedbackSwitching


