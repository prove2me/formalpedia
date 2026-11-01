-- Prove2me | Definitions.Def_ParetoIneff_Mech_PoS
-- name    : ParetoIneff_Mech_PoS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:23.826654+00:00
-- url     : https://prove2.me/theorems/2f425fbf-f197-4c85-8f93-43beee06657d
-- title:
--   Price of Stability
-- statement:
--   The **Price of Stability** of a mechanism $\mathcal M$ on $n$ machines compares the best equilibrium with the optimum, in the worst case over all instances:
--   $$
--   \mathrm{PoS}(\mathcal M)=\sup_{m\in\mathbb N,\ t\in\mathbb R_{\ge0}^{n\times m}}\frac{\inf_{s\in\mathcal Q_t^{\mathcal M}}C^{\mathcal M}(s\mid t)}{\mathrm{OPT}(t)}.
--   $$
--
--   **Formalization Note** As for the Price of Anarchy, the value lies in $[0,\infty]$ with $c/0=\infty$ for $c\ne0$ and $0/0=0$. An infimum over an empty equilibrium set is $\infty$, which the standing assumption of existence rules out.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib
import Definitions.Def_ParetoIneff_Mech_Q
import Definitions.Def_ParetoIneff_Mech_C
import Definitions.Def_ParetoIneff_OPT

open NNReal ENNReal

namespace ParetoIneff

/-- The **Price of Stability** of `ℳ`, arXiv:1809.03454v7, p.5:
`PoS(ℳ) = sup_{m ∈ ℕ, t ∈ ℝ≥0^{n×m}} (inf_{s ∈ 𝒬_t} C(s|t)) / OPT(t)`.

**Formalization Note** As for `Mech.PoA`, in `ℝ≥0∞` with `c / 0 = ⊤` for `c ≠ 0` and `0 / 0 = 0`.
The infimum over an empty set of equilibria is `⊤`; under the standing assumption
`Mech.HasEquilibria` it never occurs. -/
noncomputable def Mech.PoS {n : ℕ} (M : Mech n) : ℝ≥0∞ :=
  ⨆ (m : ℕ) (t : Fin n → Fin m → ℝ≥0),
    (⨅ s ∈ M.Q m t, ENNReal.ofReal (M.C m s t)) / ENNReal.ofReal (OPT t)

end ParetoIneff


