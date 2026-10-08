-- Prove2me | Definitions.Def_CVPricing_CertEquiv_EventA
-- name    : CVPricing_CertEquiv_EventA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T10:12:55.191214+00:00
-- url     : https://prove2.me/theorems/a5be3c51-bfac-473d-8113-a6b8203267bd
-- title:
--   Appendix, proof of Proposition 1, p. 780 — the event $A$, the constant $a$ and $C_t$
-- statement:
--   These are the objects of the proof of Proposition 1. For sequences $(x_i)_{i \ge 1}$ write $\bar x_t = t^{-1}\sum_{i=1}^t x_i$ for the sample mean. For a price sequence $(p_i)$ and a noise sequence $(e_i)$ put
--
--   $$C_t = \sum_{i=1}^t (p_i - \bar p_t)\, e_i, \qquad V_t = \sum_{i=1}^t (p_i - \bar p_t)^2 ,$$
--
--   and, for initial prices $p_1, p_2$,
--
--   $$a = \frac{(p_h - p_1)^2 + (p_h - p_2)^2}{p_h}.$$
--
--   For $\delta > 0$ the event $A = A_\delta$ is the set of noise paths $(e_i)_{i\ge1}$ satisfying all three of
--
--   1. $(p_2 - 2p_h)e_1 + (2p_h - p_1)e_2 \ \ge\ -a_1^{(0)}(p_2 - p_1)\,2p_h$;
--   2. $(p_1 - p_h)e_1 + (p_2 - p_h)e_2 \ \ge\ (-2p_h a_1^{(0)} - a_0^{(0)} + \delta)\,a + (2p_h - p_1 - p_2)\,\delta$;
--   3. $|\bar e_t| \le \delta$ for all $t \ge 3$.
--
--   On $A$ the certainty equivalent price stays at $p_h$ from period 3 on; this is the event whose positive probability proves Proposition 1.
--
--   **Formalization Note** Two printing slips in the paper's definition of $A$ are corrected. Line 2 is printed ending in $+(2p_h - p_1 - p_2)$; the factor $\delta$ is restored as in (12) and in the final display of the proof (p. 781), which is the condition the induction uses. Line 3 is printed "$\delta|\bar e_t| \le \delta$" and is read $|\bar e_t| \le \delta$, as the proof uses it. $V_t$ and $\bar x_t$ are the referenced `infoMetricOf` and `avgPriceOf` (applied to any sequence, prices or noise). $A$ is a predicate on a single noise path; its probability is taken in the theorems.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 780 (PDF 12), Appendix, proof of Proposition 1, the event A, the constant a, Eq. (12), and C_t, V_t; p. 781 (PDF 13), last display of the proof

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_Model
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares

namespace CVPricing.CertEquiv

open KeskinZeevi.SufficientConditions

/-- `C_t = Σ_{i=1}^t (p_i − p̄_t) e_i` (Appendix, proof of Proposition 1, p. 780), where
`p̄_t = avgPriceOf p t` is the sample mean of `p_1, …, p_t`. Together with
`V_t = infoMetricOf p t = Σ_{i=1}^t (p_i − p̄_t)²` it gives the least squares slope error `C_t / V_t`. -/
noncomputable def crossSum (p e : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 t, (p i - avgPriceOf p t) * e i

/-- The constant `a = ((p_h − p₁)² + (p_h − p₂)²) p_h⁻¹` of the proof of Proposition 1 (p. 780). -/
noncomputable def aConst (M : Model) (p₁ p₂ : ℝ) : ℝ :=
  ((M.ph - p₁) ^ 2 + (M.ph - p₂) ^ 2) / M.ph

/-- The event `A` of the proof of Proposition 1 (p. 780), as a predicate on a noise path `e`
(`e i` is the paper's `e_i`, `i ≥ 1`; `ē_t = avgPriceOf e t` is the sample mean of `e_1, …, e_t`):
1. `(p₂ − 2p_h) e₁ + (2p_h − p₁) e₂ ≥ −a₁ (p₂ − p₁) 2p_h`;
2. `(p₁ − p_h) e₁ + (p₂ − p_h) e₂ ≥ (−2p_h a₁ − a₀ + δ) a + (2p_h − p₁ − p₂) δ`;
3. `|ē_t| ≤ δ` for all `t ≥ 3`.
Line 2 carries the factor `δ` on its last term, as in (12) and in the last display of the proof
(p. 781); the printed definition of `A` omits it. Line 3 is printed `δ|ē_t| ≤ δ`, read as `|ē_t| ≤ δ`
as the proof uses it. -/
def EventA (M : Model) (p₁ p₂ δ : ℝ) (e : ℕ → ℝ) : Prop :=
  -M.a₁ * (p₂ - p₁) * (2 * M.ph) ≤ (p₂ - 2 * M.ph) * e 1 + (2 * M.ph - p₁) * e 2 ∧
  (-2 * M.ph * M.a₁ - M.a₀ + δ) * aConst M p₁ p₂ + (2 * M.ph - p₁ - p₂) * δ ≤
    (p₁ - M.ph) * e 1 + (p₂ - M.ph) * e 2 ∧
  ∀ t : ℕ, 3 ≤ t → |avgPriceOf e t| ≤ δ

end CVPricing.CertEquiv


