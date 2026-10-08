-- Prove2me | Definitions.Def_RoslingAssembly_SeriesEquiv_Dynamics
-- name    : RoslingAssembly_SeriesEquiv_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:47.687608+00:00
-- url     : https://prove2.me/theorems/00874b25-961b-4cbd-be8c-d3472bebe1f7
-- title:
--   Echelon positions, feasibility, and long-run balance
-- statement:
--   The position $X_{it}^{s}$ counts the position of item $i$ in period $t$ from orders placed at least $s$ periods earlier. For an order history and observed demand it equals the earlier decision less intervening demands. In particular $X_{it}^{0}=Y_{it}$, $X_{it}^{1}=X_{it}$, $X_{it}^{l_i}=X^l_{it}$, and $X_{it}^{L_i}=X^L_{it}$.
--
--   $$X_{it}\le Y_{it}\le X^l_{kt}\quad(k\in P(i))$$
--
--   is the feasibility condition. Long-run balance is equation (5), comparing the positions of adjacent items at each age.
--
--   **Formalization Note** Initial pipeline positions encode pre-period-1 orders. Feasibility is almost sure. The empty minimum over $k>i$ is $+\infty$ at $i=N$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, pp. 566–568, §§1–2, eqs. (3), (5)–(7)

import Definitions.Def_RoslingAssembly_SeriesEquiv_Policy
import Definitions.Def_RoslingAssembly_SeriesEquiv_Model

namespace RoslingAssembly.SeriesEquiv

/-- Positions at the start of period 1, indexed by the age `s ≥ 1` of the
earliest outstanding order. -/
abbrev InitialPositions := ℕ → ℕ → ℝ

namespace Model

/-- Echelon position of item `i` in period `t`, counting orders placed at
least `s` periods ago. At `s = 0` this is `Y_it`, and at `s = 1` it is `X_it`.
Initial histories supply the positions when `t - s ≤ 0`. -/
noncomputable def pos (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (i t s : ℕ) : ℝ :=
  if s < t then
    decision π ω i (t - s) - ∑ r ∈ Finset.Ico (t - s) t, ω (r - 1)
  else
    x0 i (s - t + 1) - ∑ r ∈ Finset.Ico 1 t, ω (r - 1)

/-- The paper's initial pipeline data are consistent with nonnegative past
orders and the assembly constraints of (3). -/
def WellFormedInitial (S : Model) (x0 : InitialPositions) : Prop :=
  (∀ i ∈ Finset.Icc 1 S.N, ∀ s ≥ 1, x0 i (s + 1) ≤ x0 i s) ∧
    (∀ i ∈ Finset.Icc 1 S.N, ∀ k ∈ S.predecessors i,
      ∀ s ≥ 1, x0 i s ≤ x0 k (s + S.lead k))

/-- Equation (5) at period `t`, along a fixed demand path. -/
def LongRunBalance (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (t : ℕ) : Prop :=
  ∀ i ∈ Finset.Ico 1 S.N, ∀ μ < S.M i,
    S.pos x0 π ω i t (S.M i - μ) ≤
      S.pos x0 π ω (i + 1) t (S.M (i + 1) - μ)

/-- Initial long-run balance is independent of the policy and demand path. -/
def InitiallyBalanced (S : Model) (x0 : InitialPositions) : Prop :=
  ∀ i ∈ Finset.Ico 1 S.N, ∀ μ < S.M i,
    x0 i (S.M i - μ) ≤ x0 (i + 1) (S.M (i + 1) - μ)

/-- The zero-total-lead-time boundary entry omitted by equation (5). -/
def ZeroLeadBoundary (S : Model) (x0 : InitialPositions) : Prop :=
  ∀ i ∈ Finset.Ico 1 S.N, S.M i = 0 →
    x0 i 1 ≤ x0 (i + 1) (S.M (i + 1) + 1)

/-- The zero-lead-time boundary entry at a later period. -/
def ZeroLeadAt (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (t : ℕ) : Prop :=
  ∀ i ∈ Finset.Ico 1 S.N, S.M i = 0 →
    S.pos x0 π ω i t 1 ≤
      S.pos x0 π ω (i + 1) t (S.M (i + 1) + 1)

/-- Constraint (3) at one period and demand path. -/
def PathFeasibleAt (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (t : ℕ) : Prop :=
  ∀ i ∈ Finset.Icc 1 S.N,
    S.pos x0 π ω i t 1 ≤ decision π ω i t ∧
      ∀ k ∈ S.predecessors i,
        decision π ω i t ≤ S.pos x0 π ω k t (S.lead k)

/-- Constraint (3) in every period along one demand path. -/
def PathFeasible (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) : Prop :=
  ∀ t ≥ 1, S.PathFeasibleAt x0 π ω t

/-- The feasible policies of Problem P: measurable and satisfying (3)
almost surely under the iid demand law. -/
def Feasible (S : Model) (x0 : InitialPositions) (π : Policy) : Prop :=
  MeasurablePolicy π ∧
    ∀ᵐ ω ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => S.ν),
      S.PathFeasible x0 π ω

/-- The paper's minimum over items `k > i`. The empty minimum at `i = N`
is `⊤`, rather than Lean's default real infimum zero. -/
noncomputable def minLater (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (i t : ℕ) : WithTop ℝ :=
  (Finset.Ioc i S.N).inf (fun k =>
    (S.pos x0 π ω k t (S.M k - S.M i) : WithTop ℝ))

/-- The two inequalities in (6), phrased as a bound on `Y_it`. -/
def NoExcessAt (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (i t : ℕ) : Prop :=
  (S.minLater x0 π ω i t ≤ (S.pos x0 π ω i t 1 : WithTop ℝ) →
    decision π ω i t = S.pos x0 π ω i t 1) ∧
  ((S.pos x0 π ω i t 1 : WithTop ℝ) ≤ S.minLater x0 π ω i t →
    (decision π ω i t : WithTop ℝ) ≤ S.minLater x0 π ω i t)

/-- The production lower bound (7). -/
def MinProductionAt (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (i t : ℕ) : Prop :=
  min (0 : WithTop ℝ) (S.minLater x0 π ω i t) ≤
    (decision π ω i t : WithTop ℝ)

/-- Corollary 1 replaces the minimum in Lemma 1 with `X^L_(i+1),t`.
At the last item the upper bound is empty, as in Lemma 1. -/
def SeriesNoExcessAt (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (i t : ℕ) : Prop :=
  i < S.N →
  (S.pos x0 π ω i t 1 ≥ S.pos x0 π ω (i + 1) t (S.L (i + 1)) →
      decision π ω i t = S.pos x0 π ω i t 1) ∧
  (S.pos x0 π ω i t 1 ≤ S.pos x0 π ω (i + 1) t (S.L (i + 1)) →
      decision π ω i t ≤ S.pos x0 π ω (i + 1) t (S.L (i + 1)))

end Model
end RoslingAssembly.SeriesEquiv


