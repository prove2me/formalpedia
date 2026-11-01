-- Prove2me | Definitions.Def_ParetoIneff_Mech_PoA
-- name    : ParetoIneff_Mech_PoA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:17.810094+00:00
-- url     : https://prove2.me/theorems/65ade77b-1f05-4af8-b572-60a1eaec284f
-- title:
--   Price of Anarchy
-- statement:
--   The **Price of Anarchy** of a mechanism $\mathcal M$ on $n$ machines compares the worst equilibrium with the optimum, in the worst case over all instances:
--   $$
--   \mathrm{PoA}(\mathcal M)=\sup_{m\in\mathbb N,\ t\in\mathbb R_{\ge0}^{n\times m}}\frac{\sup_{s\in\mathcal Q_t^{\mathcal M}}C^{\mathcal M}(s\mid t)}{\mathrm{OPT}(t)}.
--   $$
--
--   **Formalization Note** The value lies in $[0,\infty]$, so an unbounded family gives $\infty$. The paper does not define the ratio at $\mathrm{OPT}(t)=0$; here $c/0=\infty$ for $c\ne0$ and $0/0=0$. A supremum over an empty equilibrium set is $0$.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib
import Definitions.Def_ParetoIneff_Mech_Q
import Definitions.Def_ParetoIneff_Mech_C
import Definitions.Def_ParetoIneff_OPT

open NNReal ENNReal

namespace ParetoIneff

/-- The **Price of Anarchy** of `ℳ`, arXiv:1809.03454v7, p.5:
`PoA(ℳ) = sup_{m ∈ ℕ, t ∈ ℝ≥0^{n×m}} (sup_{s ∈ 𝒬_t} C(s|t)) / OPT(t)`.

**Formalization Note** The value lies in `ℝ≥0∞`, so the supremum of an unbounded family is `⊤`
rather than a junk value; `C` and `OPT` are nonnegative for `n ≥ 1`, so `ENNReal.ofReal` loses
nothing. The paper does not define the ratio when `OPT(t) = 0`; here `c / 0 = ⊤` for `c ≠ 0` (an
unbounded ratio, as in the proof of Theorem 5, p.11) and `0 / 0 = 0` (an instance with zero optimal
and zero equilibrium makespan costs nothing). The inner supremum over an empty set of equilibria
is `0`. -/
noncomputable def Mech.PoA {n : ℕ} (M : Mech n) : ℝ≥0∞ :=
  ⨆ (m : ℕ) (t : Fin n → Fin m → ℝ≥0),
    (⨆ s ∈ M.Q m t, ENNReal.ofReal (M.C m s t)) / ENNReal.ofReal (OPT t)

end ParetoIneff


