-- Prove2me | Definitions.Def_RiskBargaining_SYM
-- name    : RiskBargaining_SYM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:30:31.599436+00:00
-- url     : https://prove2.me/theorems/d820dc56-94d0-4936-9f0b-820852d03e94
-- title:
--   Axiom 2 (SYM): symmetry
-- statement:
--   A rule $F$ satisfies **SYM** if, for every admissible instance with $u^*=F(R,M,\mathcal A)$: if $\mathcal A_i(R_i)=\mathcal A_j(R_j)$ for all $i,j\in N$, and if for every permutation $\sigma$ of $N$
--   $$
--   (u_1,\dots,u_n)\in\mathcal U(R,M,\mathcal A)\ \Rightarrow\ (u_{\sigma(1)},\dots,u_{\sigma(n)})\in\mathcal U(R,M,\mathcal A),
--   $$
--   then $u^*_i=u^*_j$ for all $i,j\in N$.
--
--   Both hypotheses of the paper are kept, so the axiom is conditional. It is the fairness requirement of the characterization.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Axiom 2, p.8

import Mathlib
import Definitions.Def_RiskBargaining_Rule
import Definitions.Def_RiskBargaining_Instance_U
import Definitions.Def_RiskBargaining_Instance_Admissible

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **Axiom 2 (SYM).**
Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Axiom 2, p.8: if `𝒜_i(R_i) = 𝒜_j(R_j)` for all `i, j`, and if for every permutation `σ` the set
`𝒰(R, M, 𝒜)` is invariant under `u ↦ (u_σ(1), …, u_σ(n))`, then `u*_i = u*_j` for all `i, j`.

**Formalization Note.** Both hypotheses of the page are kept. -/
def SYM (F : Rule μ p X) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (I : Instance μ p X ι),
    I.Admissible → (∀ i j, I.v i = I.v j) →
      (∀ σ : Equiv.Perm ι, ∀ u ∈ I.U, (fun i => u (σ i)) ∈ I.U) → ∀ i j, F ι I i = F ι I j

end RiskBargaining


