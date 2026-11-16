-- Prove2me | Definitions.Def_AuditAdapt_Supplement_banditRoundLaw
-- name    : AuditAdapt_Supplement_banditRoundLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:35:56.133199+00:00
-- url     : https://prove2.me/theorems/c2f056b1-49c8-4d9b-bbb4-fa1b54ef8ebb
-- title:
--   Contextual bandit: law of a round, the logged record and the IPW sample $Y_t$
-- statement:
--   One round of the contextual bandit of §5.1 is a triple $(x_t,\ell_t,a_t)$: $x_t\sim\mathcal D$, and given $x_t$ the cost vector $\ell_t\sim K(x_t)$ and the action $a_t\sim\pi(\cdot\mid x_t)$ are drawn independently. Rounds are i.i.d. The auditor observes the **log**
--
--   $$
--   \big\{(x_t,\ \pi(\cdot\mid x_t),\ a_t,\ \ell_t(a_t))\big\}_{t=1}^T
--   $$
--
--   (bandit feedback with logged propensities) and knows $\bar p$. The **inverse-propensity sample** of Theorem 5.3 is
--
--   $$
--   w_t=\frac{\bar p(a_t)}{\pi(a_t\mid x_t)},\qquad Y_t=\ell_t(a_t)\,(1-w_t).
--   $$
--
--   **Formalization Note** The round law is $\mathcal D\otimes_m(K\times_k\pi)$, i.e. $x\sim\mathcal D$ followed by the product kernel $x\mapsto K(x)\otimes\pi(\cdot\mid x)$ (conditional independence of $\ell_t$ and $a_t$ given $x_t$); $T$ rounds have the product law. If $\pi(a_t\mid x_t)=0$ Lean gives $w_t=0$; such rounds have probability $0$.
-- source:
--   Aldridge, Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing Adaptive Policies, STOC 2027 submission (held version, sha256 3f6ad545b0454d8de6836d32bb81359da5022bbc373510a7c75452ab66ec9fc2), §5.1 "Setting" and Theorem 5.3, p.5 (PDF p.5)

import Mathlib
import Definitions.Def_AuditAdapt_Supplement_chiSq
import Definitions.Def_AuditAdapt_Supplement_banditAdaptivityCost

namespace AuditAdapt.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The law of one round `(x_t, ℓ_t, a_t)` of the contextual bandit (Aldridge, *Regret-based Characterization, Information Limits, and the Sample Complexity of Auditing
Adaptive Policies*, STOC 2027 submission (held version, sha256 3f6ad545…), §5.1 "Setting", p.5):
`x ∼ D`; given `x`, the cost vector `ℓ ∼ K(x)` and the action `a ∼ π(· | x)` are drawn
independently. Rounds are i.i.d., so `T` rounds have law `Measure.pi (fun _ : Fin T => banditRoundLaw D πk K)`.

**Formalization Note** `D ⊗ₘ (K ×ₖ πk)`: the composition-product of `D` with the product kernel
`x ↦ K(x) ⊗ π(· | x)`, which is conditional independence of `ℓ_t` and `a_t` given `x_t`. A round is a
triple `(x, ℓ, a) : X × (A → ℝ) × A`. -/
noncomputable def banditRoundLaw {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (D : Measure X) (πk : Kernel X A) (K : Kernel X (A → ℝ)) : Measure (X × (A → ℝ) × A) :=
  D ⊗ₘ (K ×ₖ πk)

/-- The logged record of one round, `(x_t, π(· | x_t), a_t, ℓ_t(a_t))` (§5.1, p.5: "The auditor observes
the log {(x_t, π(· | x_t), a_t, ℓ_t(a_t))}_{t=1}^T (bandit feedback with logged propensities)"). -/
noncomputable def banditLog {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (πk : Kernel X A) (r : X × (A → ℝ) × A) : X × (A → ℝ) × A × ℝ :=
  (r.1, fun a => policyProb πk r.1 a, r.2.2, r.2.1 r.2.2)

/-- The inverse-propensity sample of Theorem 5.3 (p.5): `w_t = p̄(a_t)/π(a_t | x_t)` and
`Y_t = ℓ_t(a_t)(1 − w_t)`, computed from one round `(x_t, ℓ_t, a_t)` (it uses only the logged record and
the known `p̄`).

**Formalization Note** If `π(a_t | x_t) = 0` Lean's division gives `w_t = 0`; such a round has
probability `0`. -/
noncomputable def ipwSample {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (D : Measure X) (πk : Kernel X A) (r : X × (A → ℝ) × A) : ℝ :=
  r.2.1 r.2.2 * (1 - avgAction D πk r.2.2 / policyProb πk r.1 r.2.2)

end AuditAdapt.Supplement


