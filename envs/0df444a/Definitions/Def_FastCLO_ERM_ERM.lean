-- Prove2me | Definitions.Def_FastCLO_ERM_ERM
-- name    : FastCLO_ERM_ERM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:19:59.485933+00:00
-- url     : https://prove2.me/theorems/da96045b-ab53-40ef-a698-936ed6424975
-- title:
--   Empirical risk minimization (5) over a policy class, the normalized excess cost d(π, π′) and the disagreement probability d_Δ(π, π′)
-- statement:
--   Let $\Pi$ be a class of policies and $\mathcal D = ((X_1, Y_1), \dots, (X_n, Y_n))$ a data set.
--
--   1. A policy $\pi$ is an **empirical risk minimizer** over $\Pi$ on $\mathcal D$ if $\pi \in \Pi$ and
--   $$\frac1n \sum_{i=1}^n Y_i^\top \pi(X_i) \le \frac1n \sum_{i=1}^n Y_i^\top \pi'(X_i) \qquad \text{for all } \pi' \in \Pi.$$
--   An ERM method $\hat\pi^{\mathrm{ERM}}_\Pi$ returns such a minimizer for every data set.
--   2. For policies $\pi, \pi'$, the normalized excess cost is
--   $$d(\pi, \pi') = \frac1B\, \mathbb E_X\bigl[f^*(X)^\top(\pi'(X) - \pi(X))\bigr].$$
--   3. The disagreement probability is $d_\Delta(\pi, \pi') = \mathbb P_X(\pi(X) \ne \pi'(X))$.
--
--   The regret of a data-driven policy is $B\,\mathbb E_{\mathcal D}[d(\pi^*, \hat\pi)]$, and the analysis of ERM compares $d$ with $d_\Delta$.
--
--   **Formalization Note** The factor $1/n$ does not change the minimizers and is omitted. The paper breaks ties by a fixed ordering of $\mathcal Z^\angle$; here every selection from the empirical argmin counts as ERM, which makes upper bounds stronger. In Lean $d$ is named `dExcess` to avoid Mathlib's metric `dist`.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Eq. (5), p. 3; A.4.1, p. 22

import Mathlib
import Definitions.Def_FastCLO_ERM_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FastCLO.ERM

variable {p d : ℕ}

/-- Empirical risk minimization (5) (arXiv:2011.03030v3, p. 3): `π` belongs to the policy class `H`
and minimizes the empirical cost `(1/n) Σ_i Y_iᵀ π(X_i)` over `H` on the data
`D = ((X_1, Y_1), …, (X_n, Y_n))`.

Formalization Note: the factor `1/n` does not change the minimizers and is dropped. An ERM
algorithm is any data-driven policy whose value at every `D` is such a minimizer; the paper's
consistent tie-breaking is not encoded, so every selection from the argmin is allowed. -/
def IsERM {n : ℕ} (H : Set (Vec p → Vec d)) (D : Fin n → Vec p × Vec d)
    (π : Vec p → Vec d) : Prop :=
  π ∈ H ∧ ∀ π' ∈ H, ∑ i, ⟪(D i).2, π (D i).1⟫_ℝ ≤ ∑ i, ⟪(D i).2, π' (D i).1⟫_ℝ

/-- The normalized excess cost `d(π, π') = (1/B) E_X[f*(X)ᵀ(π'(X) − π(X))]`
(arXiv:2011.03030v3, A.4.1, p. 22).

Formalization Note: the page calls this `d`; it is named `dExcess` to avoid a clash with the metric
`dist` of Mathlib. -/
noncomputable def dExcess (P : Polytope d) (I : Instance p d) (π π' : Vec p → Vec d) : ℝ :=
  (1 / P.B) * ∫ x, ⟪I.fstar x, π' x - π x⟫_ℝ ∂I.μ

/-- The disagreement probability `d_Δ(π, π') = P_X(π(X) ≠ π'(X))` (arXiv:2011.03030v3, A.4.1,
p. 22), as a real number. -/
noncomputable def dDelta (I : Instance p d) (π π' : Vec p → Vec d) : ℝ :=
  (I.μ {x | π x ≠ π' x}).toReal

end FastCLO.ERM


