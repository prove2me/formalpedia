-- Prove2me | Definitions.Def_HindsightGain_Uniform_Supplement_queries
-- name    : HindsightGain_Uniform_Supplement_queries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:51:46.59497+00:00
-- url     : https://prove2.me/theorems/d1b12b40-8485-4531-9272-c933920b79c3
-- title:
--   Adjacency-query algorithms, examined vertices and the graph estimator
-- statement:
--   In the adjacency-matrix model an algorithm asks whether a pair $\{u,v\}$ is an edge of the input graph $G$ on $[n]$. It **examines** a vertex if the vertex appears in one of its queries. A **randomized nonadaptive** algorithm draws a seed $\omega$ from a law that does not depend on $G$; the seed fixes its query set before any answer is seen, and the output is a function of the seed and of the answers to those queries. A **randomized adaptive** algorithm draws a seed that selects a finite decision tree: each internal node queries a pair and branches on the answer, and each leaf is an output; the queried pairs may depend on earlier answers. The targets are $\mathrm{mc}(G)$ and $\beta(G)$.
--
--   The estimator of Corollary 5.4 uses $q$ and $p=q/n$ and a sample $S=S_p$: if $|S|>4q$ it makes no query and outputs $0$; otherwise it queries all pairs inside $S$ and outputs $p^{-2}\mathrm{mc}(G[S])$ and $p^{-2}\beta(G[S])$.
--
--   These definitions express the upper and lower bounds of Theorem 4.
--
--   **Formalization Note** The seed lives on an arbitrary probability space, and the output is required to be measurable in the seed for each oracle, so that success probabilities are defined. Queries are unordered pairs (`Sym2`). Outputs are real numbers; an aborting run can be treated as outputting an arbitrary number, which can only increase its success probability.
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, pp.6-7, §5.4 p.26, Appendix A pp.33-35

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_graphs

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open Classical

namespace HindsightGain.Uniform.Supplement

/-- The adjacency oracle of `G`: a query `{u,v}` is answered `true` iff `uv` is an edge. -/
def answers {n : ℕ} (G : SimpleGraph (Fin n)) : Sym2 (Fin n) → Bool :=
  fun z => decide (z ∈ G.edgeSet)

/-- The vertices examined by a set of queries: those appearing in some queried pair (p.6). -/
def examined {n : ℕ} (F : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun v => ∃ z ∈ F, v ∈ z)

/-- A randomized nonadaptive adjacency-query algorithm on `n`-vertex inputs (p.6, p.34): a seed
`ω` drawn from a law on `Ω` that does not depend on the input fixes the query set before any
answer is seen, and the output is a measurable function of the seed and of the answers to those
queries only. -/
structure NonadaptiveAlg (n : ℕ) (Ω : Type) [MeasurableSpace Ω] (β : Type) [MeasurableSpace β] where
  queries : Ω → Finset (Sym2 (Fin n))
  output : Ω → (Sym2 (Fin n) → Bool) → β
  output_local : ∀ ω A A', (∀ z ∈ queries ω, A z = A' z) → output ω A = output ω A'
  measurable_output : ∀ A, Measurable (fun ω => output ω A)

/-- A deterministic adaptive adjacency-query procedure: a finite decision tree whose next query
may depend on all previous answers, ending in a real output. -/
inductive QueryTree (n : ℕ) : Type
  | leaf : ℝ → QueryTree n
  | node : Sym2 (Fin n) → (Bool → QueryTree n) → QueryTree n

/-- The output of a query tree on the oracle `A`. -/
def QueryTree.run {n : ℕ} : QueryTree n → (Sym2 (Fin n) → Bool) → ℝ
  | .leaf x, _ => x
  | .node z k, A => (k (A z)).run A

/-- The queries a query tree makes on the oracle `A`. -/
def QueryTree.queried {n : ℕ} : QueryTree n → (Sym2 (Fin n) → Bool) → Finset (Sym2 (Fin n))
  | .leaf _, _ => ∅
  | .node z k, A => insert z ((k (A z)).queried A)

/-- A randomized, possibly adaptive, adjacency-query algorithm: a seed `ω` (law independent of the
input) selects a query tree; the output is measurable in the seed for every oracle. Nonadaptive
algorithms are the special case of trees whose queries ignore the answers. -/
structure AdaptiveAlg (n : ℕ) (Ω : Type) [MeasurableSpace Ω] where
  tree : Ω → QueryTree n
  measurable_run : ∀ A, Measurable (fun ω => (tree ω).run A)

/-- The two graph parameters estimated in Theorem 4: `mc(G)` and `β(G)`. -/
inductive GraphTarget
  | maxCut
  | bipartiteness

/-- The value of a graph target. -/
def GraphTarget.eval {n : ℕ} : GraphTarget → SimpleGraph (Fin n) → ℝ
  | .maxCut, G => (HindsightGain.Uniform.Supplement.maxCut G : ℝ)
  | .bipartiteness, G => bipDist G

/-- Queries of the Corollary 5.4 estimator on the sample `S`: none if `|S| > 4q`, otherwise every
pair of distinct vertices inside `S`. -/
def estQueries {n : ℕ} (q : ℝ) (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  if 4 * q < (S.card : ℝ) then ∅
  else (Finset.univ : Finset (Sym2 (Fin n))).filter (fun z => ¬ z.IsDiag ∧ ∀ v ∈ z, v ∈ S)

/-- Max-cut output of the Corollary 5.4 estimator with `p = q/n`: `0` if `|S| > 4q`, otherwise
`p^{-2} mc(G[S])`. -/
def estMc {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℝ) (S : Finset (Fin n)) : ℝ :=
  if 4 * q < (S.card : ℝ) then 0 else ((q / n) ^ 2)⁻¹ * (maxCut (induced G S) : ℝ)

/-- Bipartiteness output of the Corollary 5.4 estimator: `0` if `|S| > 4q`, otherwise
`p^{-2} β(G[S])`. -/
def estBeta {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℝ) (S : Finset (Fin n)) : ℝ :=
  if 4 * q < (S.card : ℝ) then 0 else ((q / n) ^ 2)⁻¹ * bipDist (induced G S)

end HindsightGain.Uniform.Supplement


