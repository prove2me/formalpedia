-- Prove2me | Definitions.Def_MWCSherali_muT
-- name    : MWCSherali_muT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:45.459527+00:00
-- url     : https://prove2.me/theorems/87909287-4b2c-46a6-b8a7-02722d9468e0
-- title:
--   The corner-to-tube measure $\mu^T_{ab}$
-- statement:
--   $$d\mu^T_{ab}=\frac{C\beta}{t_i+t_j}\,dt_i\,dt_j\quad\text{on }K_a\cap T_{ab},\qquad \{i,j\}=[4]\setminus\{a,b\},\tag{10}$$
--
--   the measure on the cross section $\{t_a=\alpha\}$ of the tube $T_{ab}$, inversely proportional to the distance from the simplex edge.
--
--   **Formalization Note** The density blows up at the simplex edge but is integrable; at the single null point $t_i+t_j=0$ of the slice, Lean's $x/0=0$ sets the density to $0$, which changes nothing.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (10), p.33

import Mathlib
import Definitions.Def_MWCSherali_planeMeasure
import Definitions.Def_MWCSherali_Treg

namespace MWCSherali

open MeasureTheory

/-- **The corner-to-tube measure `μ^T_{ab}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), (10), p.33:
"`dμ^T_{ab} = Cβ/(t_i + t_j) dt_i dt_j` on `K_a ∩ T_{ab}`, `i ≠ j ∈ [4] ∖ {a, b}`".

It is the area measure of the slice `{t_a = α}` restricted to `T_{ab}`, with density
`Cβ/(t_i + t_j)`, `{i, j} = [4] ∖ {a, b}`.

**Formalization Note.** `t_i + t_j` is the sum over the complement of `{a, b}`. The density
blows up at the simplex edge `t_i + t_j = 0` but is integrable there; at that single point of the
slice Lean's `x / 0 = 0` gives the density `0`, which is harmless because the point is null.
The density enters through `ENNReal.ofReal` (it is nonnegative for `C, β > 0`). -/
noncomputable def muT (α β C : ℝ) (a b : Fin 4) : Measure (Fin 4 → ℝ) :=
  ((planeMeasure a α).restrict (Treg α β a b)).withDensity fun t =>
    ENNReal.ofReal (C * β / ∑ l ∈ ({a, b} : Finset (Fin 4))ᶜ, t l)

end MWCSherali


