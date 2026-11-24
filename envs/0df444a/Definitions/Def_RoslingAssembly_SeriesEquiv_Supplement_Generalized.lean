-- Prove2me | Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Generalized
-- name    : RoslingAssembly_SeriesEquiv_Supplement_Generalized
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:16:38.870242+00:00
-- url     : https://prove2.me/theorems/71da53a3-1118-4979-a2ad-23eaa9c53b6b
-- title:
--   Generalized Assumption, predecessor caps and inclusive local balance
-- statement:
--   Let the finite assembly tree, lead times, echelon coefficients, demand law and initial positions be those of the published model. Write $B(i)$ for all strict predecessors of item $i$, $P(i)$ for its immediate predecessors, and $M_i$ for its total lead time. Define $w_i=h_i\alpha^{-M_{s(i)}}$. The Generalized Assumption is
--   $$
--    w_i+\sum_{k\in B(i)}w_k>0\quad(1\le i\le N),\qquad
--    \sum_{i=1}^N w_i<p+H_1.
--   $$
--   The standing domain retains the finite tree and its indexing, iid nonnegative density demand with positive finite mean, $0<\alpha\le1$, physical costs $H_1=\sum_i h_i$, $p\ge0$, and a well-formed initial pipeline. The predecessor cap is $\min_{k\in P(i)}X^l_{kt}$ with empty cap $+\infty$. A shortest predecessor can be any minimizer of $l_k$, including a tie. Local balance records every sibling inequality for $0\le\mu\le M_k$, every item/shortest-predecessor equality for $0\le\mu\le M_i$, and the implied production equality.
--
--   These predicates add the signed-cost setting to the shared published model without duplicating its policy, tree or dynamics.
--
--   **Formalization Note** Items retain labels $1,\ldots,N$ and periods are $t\ge1$; the history coordinate $k$ is demand $\xi_{k+1}$. The initial well-formedness condition is the feasible past-history convention, not initial long-run balance.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4):565–579, 1989, DOI 10.1287/opre.37.4.565, pp. 566–568, §1–§2; p. 571, GA; p. 572, Lemmas 3 and 5

import Definitions.Def_RoslingAssembly_SeriesEquiv_Cost

namespace RoslingAssembly.SeriesEquiv.Supplement
open MeasureTheory

/-- All strict predecessors, using the published successor relation. -/
def allPredecessors (S : Model) (i : ℕ) : Finset ℕ :=
  (Finset.Icc 1 S.N).filter (fun k => i ∈ S.successors k)

noncomputable def weightedHolding (S : Model) (i : ℕ) : ℝ :=
  S.h i * (S.α ^ S.M (S.succ i))⁻¹

/-- Both clauses of GA; no positivity restriction on individual echelon costs. -/
def GeneralizedAssumption (S : Model) : Prop :=
  (∀ i ∈ Finset.Icc 1 S.N,
    0 < weightedHolding S i + ∑ k ∈ allPredecessors S i, weightedHolding S k) ∧
  (∑ i ∈ Finset.Icc 1 S.N, weightedHolding S i) < S.p + S.H1

/-- Installation holding costs sum over the predecessor subtree (§1). -/
def PhysicalCosts (S : Model) : Prop :=
  S.H1 = ∑ i ∈ Finset.Icc 1 S.N, S.h i ∧ 0 ≤ S.p

/-- The source domain, including the feasible initial history convention. -/
def Standing (S : Model) (x0 : InitialPositions) : Prop :=
  S.ValidTree ∧ S.ValidDemand ∧ PhysicalCosts S ∧
    0 < S.α ∧ S.α ≤ 1 ∧ S.WellFormedInitial x0

/-- An empty supplier cap is +∞, never a default real zero. -/
noncomputable def predecessorCap (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (i t : ℕ) : WithTop ℝ :=
  (S.predecessors i).inf (fun k => (S.pos x0 π ω k t (S.lead k) : WithTop ℝ))

/-- Any minimizer is allowed, including ties and zero lead times. -/
def ShortestPredecessor (S : Model) (i n : ℕ) : Prop :=
  n ∈ S.predecessors i ∧ ∀ k ∈ S.predecessors i, S.lead n ≤ S.lead k

/-- All three conclusions of Lemma 5 at one period, with inclusive endpoints. -/
def LocalBalanceAt (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (i n t : ℕ) : Prop :=
  (∀ k ∈ S.predecessors i, ∀ q ∈ S.predecessors i, k < q →
    ∀ μ ≤ S.M k, S.pos x0 π ω k t (S.M k - μ) ≤
      S.pos x0 π ω q t (S.M q - μ)) ∧
  (∀ μ ≤ S.M i, S.pos x0 π ω i t (S.M i - μ) =
    S.pos x0 π ω n t (S.M n - μ)) ∧
  decision π ω i t = S.pos x0 π ω n t (S.lead n)

end RoslingAssembly.SeriesEquiv.Supplement


