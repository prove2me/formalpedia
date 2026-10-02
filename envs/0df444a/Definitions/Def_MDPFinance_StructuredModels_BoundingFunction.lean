-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
-- name    : MDPFinance_StructuredModels_BoundingFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:34:40.10136+00:00
-- url     : https://prove2.me/theorems/14e953c3-acbb-400b-8e83-d429b526b14e
-- title:
--   Upper bounding functions and the regularity class $\mathbb{I\!B}_b^+$ (restated)
-- statement:
--   A measurable $b : E \to \mathbb{R}_{\geq 0}$ is an **upper bounding function** for $M$ if
--   there are constants $c_r, c_g, \alpha_b \geq 0$ with $r_n^+(x,a) \leq c_r\,b(x)$, $g_N^+(x)
--   \leq c_g\,b(x)$, and $\int b(x')\,Q_n(dx' \mid x,a) \leq \alpha_b\,b(x)$ for every admissible
--   $(x,a)$ and $n$. $\mathbb{I\!B}_b^+$ is the set of measurable $v : E \to [-\infty,\infty)$
--   with $v^+ \leq c\,b$ for some $c \geq 0$.
--
--   **Formalization Note.** Restated from `MDPFinance.Semicontinuous.IsUpperBoundingFunction`/
--   `IBbPlus` (chunk `02b`).
--
--   **Formalization Note (moderation).** Condition (iii) uses the Lebesgue integral of the
--   nonnegative $b$, so that it asserts $\int b\,dQ_n(\cdot\mid x,a) < \infty$ as well as the
--   bound; a Bochner integral of a non-integrable $b$ would be $0$ and satisfy the bound vacuously.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 28-29, Definition 2.4.1

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- An upper bounding function for the Markov Decision Model (Bäuerle–Rieder, Definition 2.4.1,
p. 28, PDF 43): a measurable `b : E → ℝ_+` for which there exist `c_r, c_g, α_b ∈ ℝ_+` with
`r_n^+(x,a) ≤ c_r b(x)` for `(x,a) ∈ D_n`, `g_N^+(x) ≤ c_g b(x)` for `x ∈ E`, and
`∫ b(x') Q_n(dx'|x,a) ≤ α_b b(x)` for `(x,a) ∈ D_n`, for every `n = 0, …, N-1`. Restated from
`MDPFinance.Semicontinuous.IsUpperBoundingFunction` (chunk `02b`). -/
structure IsUpperBoundingFunction (M : MarkovDecisionModel E A N) (b : E → ℝ)
    (cr cg αb : ℝ) : Prop where
  hb_meas : Measurable b
  hb_nonneg : ∀ x, 0 ≤ b x
  hcr : 0 ≤ cr
  hcg : 0 ≤ cg
  hαb : 0 ≤ αb
  hr : ∀ n < N, ∀ xa ∈ M.D n, max (M.r n xa) 0 ≤ cr * b xa.1
  hg : ∀ x, max (M.g x) 0 ≤ cg * b x
  hQ : ∀ n < N, ∀ xa ∈ M.D n,
    ∫⁻ x', ENNReal.ofReal (b x') ∂(M.Q n xa) ≤ ENNReal.ofReal (αb * b xa.1)

/-- `IB_b^+ := {v ∈ IM(E) | v^+(x) ≤ c b(x)` for all `x`, for some `c ∈ ℝ_+}` (Bäuerle–Rieder,
p. 29, PDF 44), the standing regularity class for value functions throughout §2.4. Restated from
`MDPFinance.Semicontinuous.IBbPlus` (chunk `02b`). -/
def IBbPlus (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, (v x ⊔ 0) ≤ (c * b x : ℝ)}

end MDPFinance.StructuredModels


