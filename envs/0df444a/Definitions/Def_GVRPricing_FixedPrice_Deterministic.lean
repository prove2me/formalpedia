-- Prove2me | Definitions.Def_GVRPricing_FixedPrice_Deterministic
-- name    : GVRPricing_FixedPrice_Deterministic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T11:38:48.257159+00:00
-- url     : https://prove2.me/theorems/b9dfb46b-541a-4aba-a1aa-c42ecba369b6
-- title:
--   §3.1.1 — the deterministic problem (11): J^D(x,t), and the augmented deterministic value J^D(x,t,μ) of (16)
-- statement:
--   This file defines the deterministic counterpart of the pricing problem, Gallego and van Ryzin (1994), §3.1.1 and eq. (16).
--
--   A **rate path** on $[0,t]$ is a measurable, integrable function $\lambda(\cdot)$ with $\lambda(s)\in\Lambda$ for all $0\le s\le t$. With a continuous stock $x$, the **deterministic problem** is
--   $$J^D(x,t)=\sup_{\{\lambda(s)\}}\int_0^t r(\lambda(s))\,ds\quad\text{subject to}\quad\int_0^t\lambda(s)\,ds\le x,\qquad\lambda(s)\in\Lambda.\qquad(11)$$
--   For a multiplier $\mu\ge0$, the **augmented deterministic value** drops the stock constraint and prices it at $\mu$:
--   $$J^D(x,t,\mu)=\sup_{\lambda(s)\in\Lambda}\int_0^t\big(r(\lambda(s))-\mu\lambda(s)\big)\,ds+x\mu.\qquad(16)$$
--
--   $J^D(n,t)$ is the upper bound of Theorem 2 and the benchmark of Theorem 3; $J^D(n,t,\mu)$ is its Lagrangian dual function.
--
--   **Formalization Note** The paper writes $\max$; the definitions take the supremum, and that it is attained is part of Proposition 2. Both are real suprema. For $x\ge0$, $t\ge0$ and $\mu\ge0$ the sets are nonempty (the null path $\lambda\equiv0$) and bounded above by $t r^*$, so the supremum is the true one and not a default value. Rate paths are required to be integrable on $[0,t]$, so that every integral above is a genuine integral.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1006 (PDF 8), §3.1.1, eq. (11); p. 1007 (PDF 9), eq. (16)

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model

open MeasureTheory Set

namespace GVRPricing.FixedPrice

/-- A **rate path** on `[0, t]`: a measurable, interval-integrable `ℓ : ℝ → ℝ` with
`ℓ(s) ∈ Λ` for every `s ∈ [0, t]` (the deterministic problem (11), §3.1.1, p. 1006). -/
def IsRatePath (M : Model) (t : ℝ) (ℓ : ℝ → ℝ) : Prop :=
  Measurable ℓ ∧ (∀ s ∈ Icc 0 t, ℓ s ∈ M.Λ) ∧ IntervalIntegrable ℓ volume 0 t

/-- A rate path feasible for (11) with stock `x`: in addition `∫_0^t ℓ(s) ds ≤ x`. -/
def IsFeasiblePath (M : Model) (x t : ℝ) (ℓ : ℝ → ℝ) : Prop :=
  IsRatePath M t ℓ ∧ ∫ s in (0 : ℝ)..t, ℓ s ≤ x

/-- `J^D(x, t)`, eq. (11): the optimal value of the deterministic problem
`sup {∫_0^t r(ℓ(s)) ds : ℓ feasible for stock x}`. For `x ≥ 0` and `t ≥ 0` the set is nonempty
(`ℓ ≡ 0`) and bounded above by `t r*`, so this real supremum is the true one. -/
noncomputable def detValue (M : Model) (x t : ℝ) : ℝ :=
  sSup ((fun ℓ : ℝ → ℝ => ∫ s in (0 : ℝ)..t, M.r (ℓ s)) '' {ℓ | IsFeasiblePath M x t ℓ})

/-- `J^D(x, t, μ)`, eq. (16): the augmented deterministic value
`sup_{ℓ(s) ∈ Λ} ∫_0^t (r(ℓ(s)) − μ ℓ(s)) ds + x μ`, the supremum over all rate paths **without**
the stock constraint. For `t ≥ 0`, `μ ≥ 0` the set is nonempty and bounded above by `t r*`. -/
noncomputable def detAugValue (M : Model) (x t μ : ℝ) : ℝ :=
  sSup ((fun ℓ : ℝ → ℝ => ∫ s in (0 : ℝ)..t, (M.r (ℓ s) - μ * ℓ s)) '' {ℓ | IsRatePath M t ℓ})
    + x * μ

end GVRPricing.FixedPrice


