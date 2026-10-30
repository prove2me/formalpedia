-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
-- name    : StochasticProg_RecourseKKT_expectedRecourse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:44:11.92134+00:00
-- url     : https://prove2.me/theorems/9e81f3eb-9d81-4c11-9eab-621c36c64ce1
-- title:
--   Expected recourse function $\mathcal Q(x)=\mathrm E_\xi Q(x,\xi)$
-- statement:
--   Let $P$ be a probability measure on $\Omega$. The **expected recourse function** is
--
--   $$
--   \mathcal Q(x) = \mathrm E_\xi\, Q(x, \xi(\omega)),
--   $$
--
--   made complete by the book's convention $+\infty + (-\infty) = +\infty$: writing $Q^+$ and $Q^-$ for the positive and negative parts of $\omega \mapsto Q(x,\xi(\omega))$,
--
--   $$
--   \mathcal Q(x) = \begin{cases} +\infty & \text{if } \mathrm E\, Q^+ = +\infty,\\ \mathrm E\, Q^+ - \mathrm E\, Q^- \in [-\infty, +\infty) & \text{otherwise.}\end{cases}
--   $$
--
--   Outcomes of probability zero contribute nothing ("defining $0 \cdot \infty = 0$", p. 110). A first-stage decision that leads to an infeasible second stage with positive probability therefore has $\mathcal Q(x) = +\infty$.
--
--   **Formalization Note** Both parts are lower Lebesgue integrals with values in $[0, \infty]$, so no integrability assumption is hidden. Lean's `EReal` has $\top - \top = \bot$, the opposite convention, so the subtraction is only performed when $\mathrm E\, Q^+ < \infty$.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, eq. (1.3), printed p. 104 (PDF p. 129), and §3.1c, printed pp. 109–110 (PDF pp. 134–135)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_secondStageValue
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **The expected recourse function `𝒬(x) = E_ξ Q(x, ξ)` — (1.3), with the p. 109 convention.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, eq. (1.3), printed p. 104 (PDF p. 129), and §3.1c, printed pp. 109–110
(PDF pp. 134–135): "𝒬(x) = E_ξ Q(x, ξ)". "Typically, the definition is made complete by adopting the
convention +∞ + (−∞) = +∞." Realizations of probability zero are ignored ("defining 0 · ∞ = 0",
p. 110).

Write `Q⁺` and `Q⁻` for the positive and negative parts of `ω ↦ Q(x, ξ(ω))`. Then `𝒬(x) = +∞` if
`E Q⁺ = +∞` (whatever `E Q⁻` is), and `𝒬(x) = E Q⁺ − E Q⁻ ∈ [−∞, +∞)` otherwise.

**Formalization Note.** The two parts are integrated with the lower Lebesgue integral `∫⁻`
(values in `[0, ∞]`), so no integrability hypothesis is hidden and a null set contributes nothing.
The `if` implements `+∞ + (−∞) = +∞`: Mathlib's `EReal` has `⊤ - ⊤ = ⊥`, the opposite convention,
so the subtraction is only performed when `E Q⁺ < ∞`. Measurability of `ω ↦ Q(x, ξ(ω))` is not
assumed (it holds, the LP value being a Borel function of the data; `∫⁻` is defined in any case). -/
noncomputable def expectedRecourse {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2) (x : Fin n1 → ℝ) : EReal :=
  let pos : ENNReal := ∫⁻ ω, (secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x).toENNReal ∂P
  let neg : ENNReal := ∫⁻ ω, (-(secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x)).toENNReal ∂P
  if pos = ⊤ then ⊤ else (pos : EReal) - (neg : EReal)

end StochasticProg.RecourseKKT


