-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_IsFeasiblePolicy
-- name    : KallMayerSLP_Multistage_IsFeasiblePolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:15:17.281888+00:00
-- url     : https://prove2.me/theorems/39a938f9-d430-4ca4-8f40-02efc640ce00
-- title:
--   Feasible policy of (3.10)
-- statement:
--   A **feasible policy** of problem (3.10) is a family of decision functions $x_t(\zeta_t)$, $t=1,\dots,T$, such that
--
--   1. each $x_t$ is a measurable function of the state $\zeta_t$ (nonanticipativity, $\mathcal F_t=\sigma(\zeta_t)$);
--   2. each $x_t(\zeta_t)$ is square-integrable;
--   3. $\sum_{\tau=1}^tA_{t\tau}x_\tau(\zeta_\tau)=b_t(\zeta_t)$ almost surely;
--   4. $x_t(\zeta_t)\ge0$ almost surely.
--
--   The square-integrability is the book's standing requirement on decisions for the general problem (p.249), which also makes the objective well defined.
--
--   **Formalization Note** Stage $t=1$ is covered by the same formulas: the state space of stage 1 is a point, so $x_1$ is a deterministic vector.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.10), p.261 (PDF 270); requirements on decisions p.249 (PDF 258)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_MSLP
import Definitions.Def_KallMayerSLP_Multistage_zeta

namespace KallMayerSLP.Multistage

open MeasureTheory
open scoped Matrix

/-- A **feasible policy** of problem (3.10) (Kall & Mayer, *Stochastic Linear Programming* (2005),
Chapter 3, (3.10), p.261, PDF 270, with the requirements on decisions of p.249, PDF 258): a family
of decision functions `x_t(ζ_t)`, `t = 1, …, T`, that are

* measurable functions of the state `ζ_t`, which is nonanticipativity (`ℱ_t = σ(ζ_t)`, p.249);
* square-integrable ("we have required the square-integrability of the decisions `x_t(·)`", p.249);
* a.s. solutions of `Σ_{τ=1}^t A_{tτ} x_τ(ζ_τ) = b_t(ζ_t)`, with `x_t(ζ_t) ≥ 0` a.s.

**Formalization Note.** Stage `t = 1` is included in the same formula: `Hist D.r 1` is a single
point, so `x_1` is a deterministic vector and the conditions at `t = 1` read `A_11 x_1 = b_1`,
`x_1 ≥ 0`. Coordinates at `t = 0` or `t > T` carry no condition and are ignored by the objective. -/
structure IsFeasiblePolicy (D : MSLP) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ∀ t, Ω → Fin (D.r t) → ℝ) (x : ∀ t, Hist D.r t → Fin (D.n t) → ℝ) : Prop where
  measurable : ∀ t, 1 ≤ t → t ≤ D.T → Measurable (x t)
  memLp : ∀ t, 1 ≤ t → t ≤ D.T → MemLp (fun ω => x t (zeta ξ t ω)) 2 P
  constraint : ∀ t, 1 ≤ t → t ≤ D.T → ∀ᵐ ω ∂P,
    ∑ τ ∈ Finset.Icc 1 t, D.A t τ *ᵥ x τ (zeta ξ τ ω) = D.b t (zeta ξ t ω)
  nonneg : ∀ t, 1 ≤ t → t ≤ D.T → ∀ᵐ ω ∂P, 0 ≤ x t (zeta ξ t ω)

end KallMayerSLP.Multistage


