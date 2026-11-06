-- Prove2me | Definitions.Def_IAFTRL_regretDist
-- name    : IAFTRL_regretDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:53.218049+00:00
-- url     : https://prove2.me/theorems/19109dea-a71c-4d45-b1de-b50a8492a752
-- title:
--   Regret against a comparator distribution
-- statement:
--   For a distribution $u$ on $\mathcal A$, identified with its mean action $\sum_au_a\,a$, the regret over $T$ rounds is
--   $$
--   \mathrm{Reg}_T(u)=\mathbb E\Big[\sum_{t=1}^T\Big(A_t-\sum_au_a\,a\Big)^\top\theta_t\Big].
--   $$
--   For a point mass it is the regret against a fixed action. Lemma D.18 decomposes it.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Lemma D.18, p.91; Section 1.1, p.5

import Mathlib
import Definitions.Def_IAFTRL_Run

namespace IAFTRL

open Matrix MeasureTheory

/-- **Regret against a fixed comparator distribution.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma D.18, p.91: "For a fixed
comparator distribution `u ∈ 𝒫(𝒜)`, the actual corrupted regret satisfies (D.167)", with
`Reg_T(u) = E[Σ_{t=1}^T (A_t − u)^⊤θ_t]` (p.5) and `u` identified with its mean action `Σ_a u_a a`.

`regretDist P arms T R u = ∫ Σ_{t<T} (a_{A_t} − Σ_a u_a a)^⊤θ_t dP`. -/
noncomputable def regretDist {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (arms : Fin K → Fin d → ℝ) (T : ℕ) (R : Run d K Ω) (u : Fin K → ℝ) : ℝ :=
  ∫ ω, ∑ t ∈ Finset.range T, (arms (R.A t ω) - ∑ a, u a • arms a) ⬝ᵥ R.θs t ω ∂P

end IAFTRL


