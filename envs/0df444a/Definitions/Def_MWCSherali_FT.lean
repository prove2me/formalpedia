-- Prove2me | Definitions.Def_MWCSherali_FT
-- name    : MWCSherali_FT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:12.307945+00:00
-- url     : https://prove2.me/theorems/92b7d88d-d7b0-45da-b42a-74bd2d9bd2f7
-- title:
--   The tube flows $F^{T_{ab}}_{a,i}$
-- statement:
--   In the tube $T_{ab}$ with $\{i,j\}=[4]\setminus\{a,b\}$,
--
--   $$dB_i=dF^{T_{ab}}_{a,i}=dF^{T_{ab}}_{b,i}=\frac{C\beta\,t_i}{(t_i+t_j)^2}\,dt,\qquad dB_j=dF^{T_{ab}}_{a,j}=dF^{T_{ab}}_{b,j}=\frac{C\beta\,t_j}{(t_i+t_j)^2}\,dt;$$
--
--   commodities $a$ and $b$ share these flows, and all other measures vanish in the tube.
--
--   **Formalization Note** Defined for every direction $i$, used only for $i\notin\{a,b\}$. On the null set $t_i+t_j=0$ Lean's $x/0=0$ sets the density to $0$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4.3, p.35

import Mathlib
import Definitions.Def_MWCSherali_volD4
import Definitions.Def_MWCSherali_Treg

namespace MWCSherali

open MeasureTheory

/-- **The tube flows `F^{T_{ab}}_{a,i}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4.3, p.35: in the tube `T_{ab}`, with
`{i, j} = [4] ∖ {a, b}`, "`dB_i = dF^{T_{ab}}_{a,i} = dF^{T_{ab}}_{b,i} = Cβ t_i/(t_i + t_j)² dt`,
`dB_j = dF^{T_{ab}}_{a,j} = dF^{T_{ab}}_{b,j} = Cβ t_j/(t_i + t_j)² dt`. All other measures are set
to `0`."

`FT α β C a b i` is `dt` (`volD4`) restricted to `T_{ab}` with density `Cβ t_i/(t_i + t_j)²`; it is
used only for `i ∉ {a, b}`, where it is the flow of commodities `a` and `b` in direction `i` and
the tube capacity `B^{T_{ab}}_i`.

**Formalization Note.** `t_i + t_j` is the sum over the complement of `{a, b}`, so
`FT α β C a b i = FT α β C b a i`. On the null set `t_i + t_j = 0` (the simplex edge `E_{ab}`)
Lean's `x / 0 = 0` sets the density to `0`, which changes nothing. The density enters through
`ENNReal.ofReal`. -/
noncomputable def FT (α β C : ℝ) (a b i : Fin 4) : Measure (Fin 4 → ℝ) :=
  (volD4.restrict (Treg α β a b)).withDensity fun t =>
    ENNReal.ofReal (C * β * t i / (∑ l ∈ ({a, b} : Finset (Fin 4))ᶜ, t l) ^ 2)

end MWCSherali


