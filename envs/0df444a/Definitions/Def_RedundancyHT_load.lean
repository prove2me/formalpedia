-- Prove2me | Definitions.Def_RedundancyHT_load
-- name    : RedundancyHT_load
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:47.098584+00:00
-- url     : https://prove2.me/theorems/44d97dd1-e685-4586-8779-cce87b55daa8
-- title:
--   The load $\lambda/\mu$ corresponding to a normalized arrival rate
-- statement:
--   For the normalized arrival rate $\lambda=\lambda_{\mathrm{tot}}/N$ the load is $\lambda/\mu$. Since the nominal rates of the model equal $\mu_{\mathrm{tot}}p_S$, a clock of type $S$ running at the load times its nominal rate runs at
--   $$\frac{\lambda}{\mu}\,\mu_{\mathrm{tot}}\,p_S=N\lambda p_S,$$
--   which is the arrival rate of type-$S$ jobs in the paper.
--
--   **Formalization Note** The load is unrelated to the capacity ratio $\rho_{\mathcal T}$ of Definition 1.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.1, p.4

import Definitions.Def_RedundancyHT_muBar

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The load `λ/µ`.** The published chains take the load `ρ = λ/µ`, and their class-`i` clock runs
at rate `ρ * nominal i`. With `nominal i = µ_tot p_i` this is the paper's `N λ p_i`
(arXiv:2005.14566v5, §2.1, p.4). The load is not the capacity ratio `ρ_𝒯` of Definition 1. -/
def load {n m : ℕ} (D : Model n m) (lam : ℝ) : ℝ :=
  lam / muBar D

end RedundancyHT


