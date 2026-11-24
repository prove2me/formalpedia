-- Prove2me | Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Lift
-- name    : RoslingAssembly_SeriesEquiv_Supplement_Lift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:19:15.215796+00:00
-- url     : https://prove2.me/theorems/82eb75cd-fd89-4e6a-bada-547eb892373b
-- title:
--   Full lifted reorder policy and eventual optimal continuations
-- statement:
--   Let $C$ be the surviving labels of a terminal aggregation state, $D$ its complement, and $n(i)$ the ultimate surviving representative of $i\in D$. Number the survivors in the reduced system's valid source order. For survivor $i$, let $k$ be the next survivor in this order. Given reorder levels $S_i$, the complete lifted rule is
--   $$
--   Y_{it}=\begin{cases}\min(S_i,X^{M-M_i}_{kt})&X_{it}\le S_i,\\X_{it}&X_{it}>S_i,\end{cases}
--   \quad(i\in C),\qquad
--   Y_{it}=X^{M-M_i}_{n(i),t}\quad(i\in D).
--   $$
--   The last survivor has upper cap $+\infty$, so its first branch is $S_i$. The notation $X^{M-M_i}_{kt}$ means age $M_k-M_i$ of item $k$, using original total lead times.
--
--   The reduced-level premise says that on the reduced system, from every well-formed initial pipeline there is a feasible policy that eventually follows its reorder rule and has optimal continuations. Eventual optimality of the lift means that a feasible full original policy exists and, for almost every demand path, there is a finite time after which the displayed rule on all survivors and all eliminated items holds together and every subsequent continuation is optimal from its actual remaining pipeline. Neither the transient policy nor its duration is prescribed.
--
--   These are control-problem predicates: optimality uses the original cost criterion, not agreement with a rule. No original-system optimality is assumed in the reduced-level premise.
--
--   **Formalization Note** A transient is path-dependent and finite almost surely, with no deterministic bound or failure probability. Period $k+1$ is the state after $k$ observed demands. The source's stronger conditions for optimality from period 1 (p. 573) are not imposed.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4):565–579, 1989, DOI 10.1287/opre.37.4.565, p. 572, Theorem 3(ii); p. 573, proof and first-period qualification

import Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Aggregation

namespace RoslingAssembly.SeriesEquiv.Supplement
open MeasureTheory

/-- Next label after i in the transported source order; none at the last survivor. -/
def nextSurvivor (order : List ℕ) (i : ℕ) : Option ℕ :=
  (order.drop (order.idxOf i + 1)).head?

/-- Capped two-branch rule, with the empty upper cap interpreted as +∞. -/
noncomputable def survivorDecision (S : Model) (order : List ℕ) (levels : ℕ → ℝ)
    (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ) (i t : ℕ) : ℝ :=
  if S.pos x0 π ω i t 1 ≤ levels i then
    match nextSurvivor order i with
    | none => levels i
    | some k => min (levels i) (S.pos x0 π ω k t (S.M k - S.M i))
  else S.pos x0 π ω i t 1

/-- The entire lifted policy at one time, on C and on D simultaneously. -/
def LiftedAt (S : Model) (A : AggregationState) (e : ℕ → ℕ) (levels : ℕ → ℝ)
    (x0 : InitialPositions) (π : Policy) (ω : ℕ → ℝ) (t : ℕ) : Prop :=
  (∀ i ∈ A.active,
    decision π ω i t = survivorDecision S (A.orderedLabels e) levels x0 π ω i t) ∧
  (∀ i ∈ (Finset.Icc 1 S.N) \ A.active,
    decision π ω i t = S.pos x0 π ω (A.representative i) t
      (S.M (A.representative i) - S.M i))

/-- The levels premise in Theorem 3(ii): the reduced-system reorder rule has
a feasible prefix and becomes an optimal continuation from every initial
pipeline. This predicate mentions ONLY the reduced system. -/
def EventuallyOptimalLevels (R : Model) (levels : ℕ → ℝ) : Prop :=
  ∀ z : InitialPositions, R.WellFormedInitial z →
    ∃ π : Policy, R.Feasible z π ∧
      ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => R.ν),
        ∃ T : ℕ, ∀ k ≥ T,
          (∀ i ∈ Finset.Icc 1 R.N,
            decision π ω i (k + 1) =
              survivorDecision R ((List.range R.N).map (· + 1)) levels z π ω i (k + 1)) ∧
          OptimalContinuation R z π ω k

/-- A feasible full original policy, with no prescribed transient decisions.
One almost-sure finite transient works for the whole rule and every later
optimal continuation, from the actual state reached at that time. -/
def EventuallyOptimalLift (S : Model) (A : AggregationState) (e : ℕ → ℕ) (levels : ℕ → ℝ)
    (x0 : InitialPositions) : Prop :=
  ∃ π : Policy, S.Feasible x0 π ∧
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => S.ν),
      ∃ T : ℕ, ∀ k ≥ T,
        LiftedAt S A e levels x0 π ω (k + 1) ∧ OptimalContinuation S x0 π ω k

end RoslingAssembly.SeriesEquiv.Supplement


