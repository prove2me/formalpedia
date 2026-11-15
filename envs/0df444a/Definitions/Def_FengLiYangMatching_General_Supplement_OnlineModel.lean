-- Prove2me | Definitions.Def_FengLiYangMatching_General_Supplement_OnlineModel
-- name    : FengLiYangMatching_General_Supplement_OnlineModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:20:19.497125+00:00
-- url     : https://prove2.me/theorems/4c218e19-c926-4abb-af57-c69d7ed3f084
-- title:
--   Matching execution, random labellings and policy values
-- statement:
--   Let the label set be $[n]=\{0,\ldots,n-1\}$. A timed policy observes each edge with its real arrival time; an order policy observes each edge without a timestamp. Both observe their complete past observations and actual decisions and may use a private uniform seed. Execution starts with the empty matching, accepts a proposed edge only when its distinct endpoints are free, and records the actual decision. A policy sees no future data and no labelling permutation. A fixed unlabelled graph may be known when the policy is chosen.
--
--   For a fixed labelled graph $G$, let $A_P(G,t,\xi)$ be the final number of accepted edges. The timed value is
--
--   $$T_G(P)=\int^- A_P(G,t,\xi)\,d(\operatorname{arrivalLaw}_G\otimes U[0,1])(t,\xi).$$
--
--   Independent uniform edge times and the sorting convention come from the published Process definition. For the order model, independently average over every vertex bijection $\pi$, every permutation $\sigma$ of the actual edges of $\pi(G)$, and the private seed:
--
--   $$W_G(P)=\frac1{n!}\sum_\pi\frac1{m!}\sum_\sigma\int^- A_P(\pi(G),\sigma,\xi)\,d\xi,\qquad V^\star(G)=\sup_P W_G(P).$$
--
--   Automorphic bijections are counted separately. An empty edge set has one empty order. Values lie in the extended nonnegative reals and are bounded by the finite number of vertices. Lower Lebesgue integrals allow arbitrary rules without a measurability assumption; for measurable policies these are ordinary expectations. This layer supplies both experiments without identifying their policy classes.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), §1.1, p. 2; §5 and §5.1, p. 17.

import Definitions.Def_FengLiYangMatching_General_Process
import Definitions.Def_FengLiYangMatching_General_Supplement_Policy

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement
noncomputable section

abbrev TimedPolicy (n : ℕ) := BinaryPolicy (Edge n × ℝ)
abbrev OrderPolicy (n : ℕ) := BinaryPolicy (Edge n)

/-- The environment enforces feasibility and records the actual decision. Its
state contains no graph, future observation or hidden labelling. -/
def policyStep {n : ℕ} {O : Type} (edgeOf : O → Edge n) (P : BinaryPolicy O)
    (seed : ℝ) (S : EdgeSet n × List (O × Bool)) (o : O) :
    EdgeSet n × List (O × Bool) := by
  classical
  let e := edgeOf o
  let accept := decide (¬ e.IsDiag ∧ free S.1 e ∧ P S.2 o seed = true)
  exact (if accept then insert e S.1 else S.1, S.2 ++ [(o, accept)])

/-- Immediate irrevocable decisions, folded on the observed prefix. -/
def policyRun {n : ℕ} {O : Type} (edgeOf : O → Edge n) (P : BinaryPolicy O)
    (seed : ℝ) (observations : List O) : EdgeSet n :=
  (observations.foldl (policyStep edgeOf P seed) (∅, [])).1

/-- Labels are chosen by the environment, never passed to a policy. -/
def relabel {n : ℕ} (G : SimpleGraph (Fin n)) (labelling : Equiv.Perm (Fin n)) :
    SimpleGraph (Fin n) := G.map labelling.toEmbedding

/-- Observed-time value; arbitrary policies are interpreted by the lower Lebesgue
integral. Thus a nonmeasurable policy is not silently assigned Bochner value zero. -/
def timedValue {n : ℕ} (G : SimpleGraph (Fin n)) (P : TimedPolicy n) : ℝ≥0∞ :=
  ∫⁻ w : Times G × ℝ,
    ((policyRun Prod.fst P w.2
      ((orderedEdges G w.1).map fun e => (e.val, w.1 e))).card : ℝ≥0∞)
    ∂((arrivalLaw G).prod seedLaw)

/-- Every permutation of the actual edges, including the unique empty order. -/
def edgeOrders {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (List (Edge n)) := by
  classical
  exact (graphEdges G).toList.permutations.toFinset

/-- Uniform independent labelling and edge order, and an independent private seed.
Automorphic labellings retain their multiplicity, as in the n! experiment. -/
def orderValue {n : ℕ} (G : SimpleGraph (Fin n)) (P : OrderPolicy n) : ℝ≥0∞ := by
  classical
  exact (∑ labelling : Equiv.Perm (Fin n),
    (∑ l ∈ edgeOrders (relabel G labelling),
      ∫⁻ seed : ℝ, ((policyRun id P seed l).card : ℝ≥0∞) ∂seedLaw) /
        ((edgeOrders (relabel G labelling)).card : ℝ≥0∞)) /
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)

/-- The order-model optimal value ranges over all randomized history policies. -/
def optimalOrderValue {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ≥0∞ :=
  ⨆ P : OrderPolicy n, orderValue G P

end
end FengLiYangMatching.General.Supplement


