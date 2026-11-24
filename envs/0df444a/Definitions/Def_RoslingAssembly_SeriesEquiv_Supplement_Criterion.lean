-- Prove2me | Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Criterion
-- name    : RoslingAssembly_SeriesEquiv_Supplement_Criterion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:17:18.287121+00:00
-- url     : https://prove2.me/theorems/d931ad29-2084-4d16-82c8-b5368ed52556
-- title:
--   Discounted and normalized limiting average objectives; conditional continuation
-- statement:
--   For a measurable policy $\pi$, let $J_\beta(\pi)$ be the published expected discounted objective (2) without its fixed constant, evaluated with discount $\beta$ and all physical costs and the demand law fixed. A signed expectation is defined when its positive and negative parts are not both infinite. For $0<\alpha<1$, use this unchanged discounted objective. At $\alpha=1$, a value $c\in\overline{\mathbb R}$ is an average cost precisely when the discounted signed expectations are defined for all sufficiently large $\beta<1$ and
--   $$
--    \lim_{\beta\uparrow1}\frac{1-\beta}{\beta}\left(J_\beta(\pi)
--    -\frac{\sum_{i=1}^N h_i\lambda(l_i+1)\beta^{l_i}}{1-\beta}\right)=c.
--   $$
--   A policy is optimal when it is feasible, has a defined criterion value, and that value is no greater than that of every feasible policy with a defined criterion. Values may be infinite. No default is assigned to a nonexistent average limit or to an undefined signed expectation. The existence of a minimizing policy and of its criterion value remains part of the theorem conclusions.
--
--   After a history of $k$ demands, the restarted initial position at age $s$ is $X^s_{i,k+1}$. The continuation concatenates that fixed history with fresh iid future demands. Optimal continuation means minimization of this same control problem from the actual remaining pipeline.
--
--   This interface distinguishes eventual optimal continuation from global discounted optimality at period 1.
--
--   **Formalization Note** The fixed constant cancels in discounted comparisons but is included before taking the average limit. The time index of a continuation is reset to period 1. The expectation and the average limit are relations on their natural domains; undefined quantities are not filled with Lean junk values.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4):565–579, 1989, DOI 10.1287/opre.37.4.565, p. 567, Problem P (2)–(4); pp. 572–573, eventual optimality

import Definitions.Def_RoslingAssembly_SeriesEquiv_Supplement_Generalized

namespace RoslingAssembly.SeriesEquiv.Supplement
open MeasureTheory Filter Topology

noncomputable def positiveTotal (S : Model) (π : Policy) : ENNReal :=
  ∫⁻ ω, ∑' k, ENNReal.ofReal (S.α ^ k * S.periodCost π ω (k + 1))
    ∂(Measure.infinitePi fun _ : ℕ => S.ν)

noncomputable def negativeTotal (S : Model) (π : Policy) : ENNReal :=
  ∫⁻ ω, ∑' k, ENNReal.ofReal (-(S.α ^ k * S.periodCost π ω (k + 1)))
    ∂(Measure.infinitePi fun _ : ℕ => S.ν)

/-- A signed expectation exists unless both its parts are infinite. -/
def DefinedDiscounted (S : Model) (π : Policy) : Prop :=
  positiveTotal S π ≠ ⊤ ∨ negativeTotal S π ≠ ⊤

/-- Vary only the discount, keeping the primitive physical costs and law fixed. -/
def atDiscount (S : Model) (β : ℝ) : Model := { S with α := β }

/-- The policy-independent constant (4), on 0<β<1. -/
noncomputable def fixedConstant (S : Model) (β : ℝ) : ℝ :=
  -(∑ i ∈ Finset.Icc 1 S.N,
    S.h i * (∫ x : ℝ, x ∂S.ν) * (S.lead i + 1) * β ^ S.lead i) / (1 - β)

/-- Normalized (2), INCLUDING (4), before taking the average-cost limit. -/
noncomputable def normalizedCost (S : Model) (π : Policy) (β : ℝ) : EReal :=
  (((1 - β) / β : ℝ) : EReal) *
    ((atDiscount S β).cost π + (fixedConstant S β : EReal))

/-- This relation asserts existence of the source's extended-valued limit;
no value is assigned to a policy for which the limit fails to exist. -/
def HasAverageCost (S : Model) (π : Policy) (c : EReal) : Prop :=
  (∀ᶠ β : ℝ in 𝓝[<] 1, DefinedDiscounted (atDiscount S β) π) ∧
    Tendsto (normalizedCost S π) (𝓝[<] 1) (𝓝 c)

/-- Discounted comparisons use the unchanged published objective, whose fixed
constant cancels. At α=1 the constant must be retained in the limiting recipe. -/
def HasCriterion (S : Model) (π : Policy) (c : EReal) : Prop :=
  if S.α = 1 then HasAverageCost S π c
  else DefinedDiscounted S π ∧ c = S.cost π

/-- Minimize the source criterion among all feasible policies for which it is
defined. Existence of a minimizing policy AND of its criterion is a conclusion
of the lemma items, never a premise. Infinite defined values are allowed. -/
def CriterionOptimal (S : Model) (x0 : InitialPositions) (π : Policy) : Prop :=
  S.Feasible x0 π ∧ ∃ c : EReal, HasCriterion S π c ∧
    ∀ σ : Policy, S.Feasible x0 σ → ∀ d : EReal, HasCriterion S σ d → c ≤ d

/-- Pipeline at the beginning of period k+1, after the first k demands. -/
noncomputable def restart (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (k : ℕ) : InitialPositions :=
  fun i s => S.pos x0 π ω i (k + 1) s

/-- Conditional policy after a finite, already observed demand history. -/
def continuation (π : Policy) {k : ℕ} (past : Fin k → ℝ) : Policy :=
  fun r future i => π (k + r) (Fin.append past future) i

/-- Optimality of the actual continuation, from the actual remaining pipeline. -/
def OptimalContinuation (S : Model) (x0 : InitialPositions) (π : Policy)
    (ω : ℕ → ℝ) (k : ℕ) : Prop :=
  CriterionOptimal S (restart S x0 π ω k)
    (continuation π (fun j : Fin k => ω j.val))

end RoslingAssembly.SeriesEquiv.Supplement


