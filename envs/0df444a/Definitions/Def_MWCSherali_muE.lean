-- Prove2me | Definitions.Def_MWCSherali_muE
-- name    : MWCSherali_muE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:53.455957+00:00
-- url     : https://prove2.me/theorems/7075f8d5-e8d2-4234-bc05-1feb76821cab
-- title:
--   The corner-to-edge atom $\mu^E_{ab}$
-- statement:
--   $$\mu^E_{ab}=C\beta(2\alpha-1)\,\delta_{y_{ab}(\alpha)},\tag{11}$$
--
--   a point mass at the point of the simplex edge $E_{ab}$ where it leaves the corner $K_a$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (11), p.33

import Mathlib
import Definitions.Def_MWCSherali_yab

namespace MWCSherali

open MeasureTheory

/-- **The corner-to-edge atom `μ^E_{ab}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), (11), p.33:
"`μ^E_{ab} = Cβ(2α − 1) δ_{y_{ab}(α)}`", where `δ_x` is the unit point mass at `x`.

**Formalization Note.** The mass enters through `ENNReal.ofReal` (it is positive for
`C, β > 0`, `α > 1/2`). -/
noncomputable def muE (α β C : ℝ) (a b : Fin 4) : Measure (Fin 4 → ℝ) :=
  ENNReal.ofReal (C * β * (2 * α - 1)) • Measure.dirac (yab a b α)

end MWCSherali


