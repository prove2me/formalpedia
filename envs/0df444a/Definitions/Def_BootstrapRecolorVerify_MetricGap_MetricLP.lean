-- Prove2me | Definitions.Def_BootstrapRecolorVerify_MetricGap_MetricLP
-- name    : BootstrapRecolorVerify_MetricGap_MetricLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:12.869243+00:00
-- url     : https://prove2.me/theorems/e1711d92-9842-4eb1-a946-0a217a4f8dc6
-- title:
--   Pseudometric extensions and the metric LP
-- statement:
--   Let $I=(G,w,T,d_T)$ be a finite 0-extension instance. A feasible extension is a nonnegative symmetric real function $d$ on all vertex pairs, zero on the diagonal and satisfying the triangle inequality, whose restriction to terminal pairs is $d_T$. Distinct nonterminals may have distance zero. Its objective and the relaxation value are
--
--   $$\operatorname{metricObjective}(I,d)=\sum_{e=\{u,v\}}w_e d(u,v),\qquad
--   \operatorname{MetricLP}(I)=\inf_{d\text{ feasible}}\operatorname{metricObjective}(I,d).$$
--
--   This is the shared relaxation used by the goal. On a valid finite instance with a terminal, feasibility is nonempty, the objective is nonnegative, and the infimum is attained. The generic instance's published retraction cost and optimum are reused.
--
--   **Formalization Note** Real infima on invalid or empty-terminal inputs have Lean's default convention. The goal only evaluates valid instances with at least three terminals and positive LP value.
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), §1, metric LP and pseudometric convention, p.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=2; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_ZeroExtensionGap_Instance

namespace BootstrapRecolorVerify.MetricGap

/-- Makarychev, STOC 2027 submission #1436 (October 2026), §1, p.2.
A feasible extension is a pseudometric: no separation axiom on nonterminals. -/
def IsMetricExtension {V : Type*} [Fintype V]
    (I : ZeroExtensionGap.Instance V) (d : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ d u v) ∧ (∀ u, d u u = 0) ∧
  (∀ u v, d u v = d v u) ∧
  (∀ u v z, d u z ≤ d u v + d v z) ∧
  ∀ a b : I.T, d a b = I.D a b

/-- The metric LP objective, with each undirected edge counted once (§1, p.2). -/
noncomputable def metricObjective {V : Type*} [Fintype V]
    (I : ZeroExtensionGap.Instance V) (d : V → V → ℝ) : ℝ :=
  ∑ e ∈ ZeroExtensionGap.edgeFin I.G,
    I.w e * d (ZeroExtensionGap.edgeTail e) (ZeroExtensionGap.edgeHead e)

/-- The metric LP value (§1, p.2). For a valid finite instance with a terminal,
the feasible set is nonempty (a retraction supplies an extension), the objective
is bounded below by zero, and its infimum is the LP minimum. Invalid/empty-terminal
inputs are not used by the goal; on these inputs `sInf` has Lean's default convention. -/
noncomputable def MetricLP {V : Type*} [Fintype V]
    (I : ZeroExtensionGap.Instance V) : ℝ :=
  sInf {c | ∃ d, IsMetricExtension I d ∧ c = metricObjective I d}

end BootstrapRecolorVerify.MetricGap


