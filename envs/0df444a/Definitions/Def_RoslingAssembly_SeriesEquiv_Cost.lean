-- Prove2me | Definitions.Def_RoslingAssembly_SeriesEquiv_Cost
-- name    : RoslingAssembly_SeriesEquiv_Cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:06.581836+00:00
-- url     : https://prove2.me/theorems/066aa29a-0700-4535-b32e-40c5ac270a27
-- title:
--   Expected discounted cost and optimality for Problem P
-- statement:
--   The cost of a policy is the expected discounted sum of Rosling’s period costs: discounted echelon holding charges plus the expected shortage under demand over $l_1+1$ periods. A policy is optimal when it is feasible and its cost does not exceed the cost of any feasible policy from the same initial pipeline.
--
--   $$C(\pi)=\mathbb E\sum_{t=1}^{\infty}\alpha^{t-1}\left[\sum_{i=1}^{N}\alpha^{l_i}h_iY_{it}+\alpha^{l_1}(p+H_1)\mathbb E(D_{l_1+1}-Y_{1t})^+\right].$$
--
--   This defines Problem P for the original tree and, without a special case, for the equivalent series tree.
--
--   **Formalization Note** Lean uses `EReal` and separate positive and negative expectations. The constant in (2) is independent of policy and is omitted.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 567, Problem P, eqs. (2)–(4)

import Definitions.Def_RoslingAssembly_SeriesEquiv_Dynamics

namespace RoslingAssembly.SeriesEquiv
namespace Model

/-- The law of demand over `lead 1 + 1` periods, the paper's convolution
with density `φ_1^(l+1)`. -/
noncomputable def leadDemandLaw (S : Model) : MeasureTheory.Measure ℝ :=
  (MeasureTheory.Measure.pi (fun _ : Fin (S.lead 1 + 1) => S.ν)).map
    (fun z => ∑ j, z j)

/-- The one-period summand in the objective (2), excluding its fixed constant. -/
noncomputable def periodCost (S : Model) (π : Policy) (ω : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  (∑ i ∈ Finset.Icc 1 S.N,
    S.α ^ S.lead i * S.h i * decision π ω i t) +
  S.α ^ S.lead 1 * (S.p + S.H1) *
    ∫ x, max (x - decision π ω 1 t) 0 ∂S.leadDemandLaw

/-- The expected discounted objective (2), without its policy-independent
constant. The positive and negative expectations are taken separately so the
value lies in the extended reals. -/
noncomputable def cost (S : Model) (π : Policy) : EReal :=
  ((∫⁻ ω, ∑' k,
      ENNReal.ofReal (S.α ^ k * S.periodCost π ω (k + 1))
      ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => S.ν) : ENNReal) : EReal) -
  ((∫⁻ ω, ∑' k,
      ENNReal.ofReal (-(S.α ^ k * S.periodCost π ω (k + 1)))
      ∂(MeasureTheory.Measure.infinitePi fun _ : ℕ => S.ν) : ENNReal) : EReal)

/-- Optimality for Problem P from a fixed initial pipeline: feasibility and
least expected discounted cost among all feasible policies. -/
def Optimal (S : Model) (x0 : InitialPositions) (π : Policy) : Prop :=
  S.Feasible x0 π ∧
    ∀ σ : Policy, S.Feasible x0 σ → S.cost π ≤ S.cost σ

end Model
end RoslingAssembly.SeriesEquiv


