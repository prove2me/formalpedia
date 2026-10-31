-- Prove2me | Definitions.Def_KallMayerSLP_CondExp_cvar
-- name    : KallMayerSLP_CondExp_cvar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:05.277087+00:00
-- url     : https://prove2.me/theorems/c488aa85-182b-4c29-8b3c-55ef838c32c5
-- title:
--   Conditional Value at Risk $\nu_c(\vartheta,\alpha)$
-- statement:
--   For an integrable random variable $\vartheta$ and $0<\alpha<1$, the **Conditional Value at Risk** is
--   $$
--   \rho^\alpha_{\mathrm{CVaR}}(\vartheta)=\nu_c(\vartheta,\alpha)=\min_z\Big[z+\frac{1}{1-\alpha}\,\mathbb E[(\vartheta-z)^+]\Big].
--   $$
--
--   **Formalization Note** The minimum is written as the infimum of the range of the objective. Attainment is part of the theorem `nu_le_cvar`, so the infimum is not a default value.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.32), p.161

import Mathlib
import Definitions.Def_KallMayerSLP_CondExp_cvarObjective

open MeasureTheory

namespace KallMayerSLP.CondExp

/-- Conditional Value at Risk `ρ^α_CVaR(ϑ) := ν_c(ϑ, α) := min_z [z + (1 / (1 - α)) 𝔼[(ϑ - z)⁺]]`.
Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, eq. (4.32), p.161 (PDF 171).

**Formalization Note** The book's `min` is `sInf` of the range of the objective. For integrable `ϑ`
and `0 < α < 1` the range is nonempty and bounded below and the minimum is attained: this is part of
`KallMayerSLP.CondExp.nu_le_cvar`, so the `sInf` is never a junk value. -/
noncomputable def cvar {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (ϑ : Ω → ℝ) (α : ℝ) : ℝ :=
  sInf (Set.range (cvarObjective μ ϑ α))

end KallMayerSLP.CondExp


