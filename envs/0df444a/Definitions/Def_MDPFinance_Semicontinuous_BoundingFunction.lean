-- Prove2me | Definitions.Def_MDPFinance_Semicontinuous_BoundingFunction
-- name    : MDPFinance_Semicontinuous_BoundingFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:24:08.876985+00:00
-- url     : https://prove2.me/theorems/b3e247a5-0d11-415b-8477-a9f923aa716f
-- title:
--   Upper bounding function, and the classes $IB_b$, $IB_b^+$
-- statement:
--   A measurable function $b : E \to \mathbb{R}_+$ is an **upper bounding function** for the
--   Markov Decision Model (Definition 2.4.1) if there exist $c_r, c_g, \alpha_b \in \mathbb{R}_+$
--   with, for every $n = 0,\dots,N-1$:
--   $$
--   r_n^+(x,a) \le c_r\, b(x) \ \ ((x,a)\in D_n), \qquad
--   g_N^+(x) \le c_g\, b(x) \ \ (x \in E), \qquad
--   \int b(x')\, Q_n(dx' \mid x,a) \le \alpha_b\, b(x) \ \ ((x,a) \in D_n).
--   $$
--   Writing $\|v\|_b := \sup_{x} |v(x)|/b(x)$ for the weighted supremum norm ($0/0 := 0$), the book
--   defines $\mathrm{IB}_b := \{v \in \mathrm{IM}(E) : \|v\|_b < \infty\}$ and $\mathrm{IB}_b^+ :=
--   \{v \in \mathrm{IM}(E) : \|v^+\|_b < \infty\}$ — equivalently (the book gives both forms),
--   $\mathrm{IB}_b = \{v : |v(x)| \le c\, b(x)\ \forall x,\text{ for some } c \ge 0\}$ and likewise
--   for $\mathrm{IB}_b^+$ with $v^+$. $\mathrm{IB}_b^+$ is the regularity class every value function
--   in this mission is shown to belong to.
--
--   **Formalization Note.** $\mathrm{IB}_b$, $\mathrm{IB}_b^+$ are formalized directly via the
--   book's own bound-by-a-constant characterization, sidestepping `EReal` division and its
--   `0/0 := 0` convention in the norm $\|\cdot\|_b$ for no loss of content (the book itself proves
--   the two forms equivalent).
--
--   **Formalization Note (moderation).** Condition (iii) uses the Lebesgue integral of the
--   nonnegative $b$, so that it asserts $\int b\,dQ_n(\cdot\mid x,a) < \infty$ as well as the
--   bound; a Bochner integral of a non-integrable $b$ would be $0$ and satisfy the bound vacuously.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 28-29, Definition 2.4.1

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Semicontinuous

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- An upper bounding function for the Markov Decision Model (Bäuerle–Rieder, Definition 2.4.1,
p. 28, PDF 43): a measurable `b : E → ℝ_+` for which there exist `c_r, c_g, α_b ∈ ℝ_+` with
`r_n^+(x,a) ≤ c_r b(x)` for `(x,a) ∈ D_n`, `g_N^+(x) ≤ c_g b(x)` for `x ∈ E`, and
`∫ b(x') Q_n(dx'|x,a) ≤ α_b b(x)` for `(x,a) ∈ D_n`, for every `n = 0, …, N-1`. Positive parts
`r_n^+`, `g_N^+` are written `max (·) 0`; the integral of the nonnegative `b` is the Lebesgue integral
`∫⁻`, so that (iii) also asserts its finiteness (a Bochner integral of a non-integrable `b` would be
`0`). -/
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

/-- `IB_b := {v ∈ IM(E) | |v(x)| ≤ c b(x)` for all `x`, for some `c ∈ ℝ_+}` (Bäuerle–Rieder,
p. 28, PDF 43), the second, equivalent form of the definition the book itself gives for the set
of functions of finite weighted supremum norm `‖·‖_b` — used directly rather than the norm
itself, which would need `EReal` division and its `0/0 := 0` convention for no further benefit
(see `MODERATION_NOTES.md`). -/
def IBb (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, max (v x) (-(v x)) ≤ (c * b x : ℝ)}

/-- `IB_b^+ := {v ∈ IM(E) | v^+(x) ≤ c b(x)` for all `x`, for some `c ∈ ℝ_+}` (Bäuerle–Rieder,
p. 29, PDF 44), the standing regularity class for value functions throughout §2.4.1-2.4.3. -/
def IBbPlus (b : E → ℝ) : Set (E → EReal) :=
  {v | Measurable v ∧ (∀ x, v x ≠ ⊤) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ x, (v x ⊔ 0) ≤ (c * b x : ℝ)}

end MDPFinance.Semicontinuous


