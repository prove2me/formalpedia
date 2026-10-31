-- Prove2me | Definitions.Def_NonlinearPriority_delta
-- name    : NonlinearPriority_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:42.75403+00:00
-- url     : https://prove2.me/theorems/895456ef-fb53-4668-bf76-b7acbe4ca471
-- title:
--   The marginal-cost index $\delta^{\gamma_1,\gamma_2}_i$, (3), and $\delta^\gamma_i=\delta^{\gamma,\bar\pi_k}_i$
-- statement:
--   For policies $\gamma_1,\gamma_2$ and a type $i$,
--   $$\delta^{\gamma_1,\gamma_2}_i\equiv\frac{\mathbb E[C_i(W^{\gamma_1}_i)]-\mathbb E[C_i(W^{\gamma_2}_i)]}{\mathbb E[W^{\gamma_1}_i]-\mathbb E[W^{\gamma_2}_i]},\tag{3}$$
--   where $W^\gamma_i$ has the steady-state law $w(\gamma,i)$. The abbreviation $\delta^\gamma_i\equiv\delta^{\gamma,\bar\pi_k}_i$ compares a policy with the pooled policy $\bar\pi_k$.
--
--   $\delta^{\gamma_1,\gamma_2}_i$ is the change in expected cost of type $i$ per unit change in its mean waiting time between the two policies; Proposition 2 compares policies through $\delta\mu$.
--
--   **Formalization Note** Real division: the value is $0$ if the two means coincide. Where the paper uses (3), the means differ by Lemma A.1(c).
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, (3), Proposition 2, p.5 (PDF 6)

import Mathlib
import Definitions.Def_NonlinearPriority_piBar

open MeasureTheory

namespace NonlinearPriority

variable {K : ℕ}

/-- **The marginal-cost index `δ^{γ1,γ2}_i`, (3)** (Proposition 2, p. 5, PDF 6). Ouyang, Argon and
Ziya, Management Science (2021), doi:10.1287/mnsc.2020.3952:

`δ^{γ1,γ2}_i ≡ (E[Ci(W^{γ1}_i)] − E[Ci(W^{γ2}_i)]) / (E[W^{γ1}_i] − E[W^{γ2}_i])`.

`w γ i` is the steady-state waiting-time law of type `i` under the policy `γ`, so
`E[g(W^γ_i)] = ∫ g d(w γ i)`.

**Formalization Note.** Real division: the value is `0` if the two means coincide; for the
policies and types where the paper uses (3) the means differ (Lemma A.1(c)). -/
noncomputable def delta (C : Fin K → ℝ → ℝ) (w : (Fin K → ℕ) → Fin K → ProbabilityMeasure ℝ)
    (g1 g2 : Fin K → ℕ) (i : Fin K) : ℝ :=
  ((∫ x, C i x ∂(w g1 i : Measure ℝ)) - ∫ x, C i x ∂(w g2 i : Measure ℝ)) /
    ((∫ x, x ∂(w g1 i : Measure ℝ)) - ∫ x, x ∂(w g2 i : Measure ℝ))

/-- `δ^γ_i ≡ δ^{γ, π̄_k}_i` (p. 5, PDF 6). -/
noncomputable def deltaBar (C : Fin K → ℝ → ℝ) (w : (Fin K → ℕ) → Fin K → ProbabilityMeasure ℝ)
    (k : ℕ) (γ : Fin K → ℕ) (i : Fin K) : ℝ :=
  delta C w γ (piBar k) i

end NonlinearPriority


