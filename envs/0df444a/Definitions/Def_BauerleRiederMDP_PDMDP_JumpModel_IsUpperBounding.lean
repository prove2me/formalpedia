-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_IsUpperBounding
-- name    : BauerleRiederMDP_PDMDP_JumpModel_IsUpperBounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:45.713354+00:00
-- url     : https://prove2.me/theorems/c8ddd74d-efca-4a00-83a4-872f88a04b18
-- title:
--   Definition 8.2.4: upper bounding function
-- statement:
--   A measurable $b:E\to\mathbb R_+$ is an **upper bounding function** if there are $c_r,c_Q,c_\varphi\in\mathbb R_+$ such that
--
--   1. $r^+(x,u)\le c_rb(x)$ for all $(x,u)\in E\times U$;
--   2. $\int b(z)\,Q(dz|x,u)\le c_Qb(x)$ for all $(x,u)\in E\times U$;
--   3. $\lambda\int_0^\infty e^{-(\lambda+\beta)t}b(\varphi^\alpha_t(x))\,dt\le c_\varphi b(x)$ for all $x\in E$, $\alpha\in\mathcal R$.
--
--   Then $b$ is also an upper bounding function of the embedded model, with $\alpha_b\le c_Qc_\varphi$.
--
--   **Formalization Note** The integrals of $b\ge0$ are Lebesgue integrals in `ℝ≥0∞`, so the bounds carry finiteness.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 8.2.4, p.251

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.PDMDP

/-- Definition 8.2.4 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.251, PDF 262): a measurable `b : E → ℝ₊` is an **upper bounding
function** if there are `c_r, c_Q, c_φ ∈ ℝ₊` with
(i) `r⁺(x,u) ≤ c_r b(x)` for all `(x,u)`;
(ii) `∫ b(z) Q(dz|x,u) ≤ c_Q b(x)` for all `(x,u)`;
(iii) `λ ∫_0^∞ e^{-(λ+β)t} b(φ^α_t(x)) dt ≤ c_φ b(x)` for all `x ∈ E`, `α ∈ R`.

**Formalization Note** The integrals of the nonnegative function `b` are Lebesgue integrals in
`ℝ≥0∞`, so the bounds carry their finiteness. -/
def JumpModel.IsUpperBounding {E U : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSpace U] (M : JumpModel E U) (b : E → ℝ) : Prop :=
  Measurable b ∧ (∀ x, 0 ≤ b x) ∧ ∃ cr cQ cφ : ℝ, 0 ≤ cr ∧ 0 ≤ cQ ∧ 0 ≤ cφ ∧
    (∀ x u, max (M.r (x, u)) 0 ≤ cr * b x) ∧
    (∀ x u, ∫⁻ z, ENNReal.ofReal (b z) ∂(M.Q (x, u)) ≤ ENNReal.ofReal (cQ * b x)) ∧
    ∀ x (α : RelaxedControl U),
      ENNReal.ofReal M.lam * ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(M.lam + M.β) * t) * b (M.flow α x t)) ≤
      ENNReal.ofReal (cφ * b x)

end BauerleRiederMDP.PDMDP


