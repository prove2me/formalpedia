-- Prove2me | Definitions.Def_AuditAdapt_Supplement_banditAdaptivityCost
-- name    : AuditAdapt_Supplement_banditAdaptivityCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:35:19.766714+00:00
-- url     : https://prove2.me/theorems/4870bcb6-2de7-4bbc-9293-132cc0a3f9e3
-- title:
--   Contextual bandit: $\bar p$, mean costs $c(x)$, adaptivity cost $\Delta(\pi)$ and $\bar\chi^2(\pi)$
-- statement:
--   In the contextual-bandit setting of §5.1, contexts $x\sim\mathcal D$ live on a measurable space $\mathcal X$, the policy $\pi(\cdot\mid x)$ is a distribution on the finite action set $\mathcal A$, and given $x$ a cost vector $\ell\in[0,1]^{\mathcal A}$ is drawn from a conditional law $K(x)$ with mean $c(x)=\mathbb E[\ell\mid x]$. Define
--
--   1. the **average action distribution** $\bar p(a)=\mathbb E_{x\sim\mathcal D}\,\pi(a\mid x)$;
--   2. the **per-round adaptivity cost**
--   $$
--   \Delta(\pi)=\mathbb E_x\langle c(x),\pi(\cdot\mid x)\rangle-\langle\mathbb E_x c(x),\bar p\rangle=\operatorname{tr}\operatorname{Cov}\big(c(x),\pi(\cdot\mid x)\big);
--   $$
--   3. the **average $\chi^2$** $\bar\chi^2(\pi)=\mathbb E_x\big[\chi^2(\bar p\,\|\,\pi(\cdot\mid x))\big]\in[0,\infty]$.
--
--   $\Delta(\pi)$ is the quantity an auditor estimates from logs; $\bar\chi^2(\pi)$ is the complexity parameter of Theorems 5.3 and 5.4.
--
--   **Formalization Note** The policy is a Markov kernel `πk : Kernel X A` with $\pi(a\mid x)$ = `(πk x {a}).toReal`, and the cost law a Markov kernel `K : Kernel X (A → ℝ)`. The expectations over $x$ are Bochner integrals of bounded measurable functions (costs in $[0,1]$ are assumed in every statement); $\bar\chi^2$ is a lower Lebesgue integral in `ℝ≥0∞`.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), §5.1 "Setting", p.5 (PDF p.5)

import Mathlib
import Definitions.Def_AuditAdapt_Supplement_chiSq

namespace AuditAdapt.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! Contextual-bandit instance quantities of §5.1 (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), §5.1 "Setting", p.5).

"Contexts x_t ∼ D are i.i.d. on a measurable space X; given x_t, a cost vector ℓ_t ∈ [0, 1]^A is drawn
from a conditional law with mean c(x_t); the policy draws a_t ∼ π(· | x_t), independently of ℓ_t given
x_t. [...] p̄ = E_x π(· | x). The target is the per-round adaptivity cost
Δ(π) = E_x⟨c(x), π(· | x)⟩ − ⟨E_x c(x), p̄⟩ [...]. Let χ̄²(π) = E_x[χ²(p̄ ∥ π(· | x))] ∈ [0, ∞]."

The policy is a Markov kernel `πk : Kernel X A` and the cost law a Markov kernel
`K : Kernel X (A → ℝ)` (the law of the cost vector given the context). -/

/-- `π(a | x)`, the probability the policy's kernel gives to action `a` in context `x`. -/
noncomputable def policyProb {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (πk : Kernel X A) (x : X) (a : A) : ℝ :=
  (πk x {a}).toReal

/-- The average action distribution `p̄(a) = E_{x∼D} π(a | x)` (§5.1, p.5). -/
noncomputable def avgAction {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (D : Measure X) (πk : Kernel X A) (a : A) : ℝ :=
  ∫ x, policyProb πk x a ∂D

/-- The mean cost `c(x)(a) = E[ℓ(a) | x]` of action `a` in context `x` (§5.1, p.5). -/
noncomputable def meanCost {X A : Type*} [MeasurableSpace X]
    (K : Kernel X (A → ℝ)) (x : X) (a : A) : ℝ :=
  ∫ ℓ, ℓ a ∂(K x)

/-- The per-round adaptivity cost `Δ(π) = E_x⟨c(x), π(· | x)⟩ − ⟨E_x c(x), p̄⟩` (§5.1, p.5).

**Formalization Note** The integrands are bounded measurable functions of `x` whenever the costs lie
in `[0,1]^A` (as every statement of the mission assumes) and `D` is a probability measure, so the
Bochner integrals are the genuine expectations. -/
noncomputable def banditAdaptivityCost {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [Fintype A]
    (D : Measure X) (πk : Kernel X A) (K : Kernel X (A → ℝ)) : ℝ :=
  (∫ x, ∑ a, meanCost K x a * policyProb πk x a ∂D) -
    ∑ a, (∫ x, meanCost K x a ∂D) * avgAction D πk a

/-- `χ̄²(π) = E_x[χ²(p̄ ∥ π(· | x))] ∈ [0, ∞]` (§5.1, p.5), a lower Lebesgue integral in `ℝ≥0∞`. -/
noncomputable def chiBar {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] [Fintype A]
    (D : Measure X) (πk : Kernel X A) : ℝ≥0∞ :=
  ∫⁻ x, chiSq (avgAction D πk) (policyProb πk x) ∂D

end AuditAdapt.Supplement


