-- Prove2me | Definitions.Def_MWCSherali_muZ
-- name    : MWCSherali_muZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:16.328612+00:00
-- url     : https://prove2.me/theorems/5288426c-546d-42d3-9293-7d9fbc7a43d8
-- title:
--   The corner-to-centre measure $\mu^Z_a$
-- statement:
--   $$d\mu^Z_a=C\,dt_i\,dt_j\quad\text{on }K_a\cap Z,\qquad i\neq j\in[4]\setminus\{a\},\tag{9}$$
--
--   the uniform measure (with density $C$) on the cross section of $Z$ at $t_a=\alpha$, through which commodity $a$ passes from the corner $K_a$ into the central region.
--
--   **Formalization Note** Points of $Z$ with $t_a=\alpha$ are exactly the cross section $K_a\cap Z\cap\{t_a=\alpha\}$; $C$ enters as a nonnegative extended real.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (9), p.33

import Mathlib
import Definitions.Def_MWCSherali_planeMeasure
import Definitions.Def_MWCSherali_Zreg

namespace MWCSherali

open MeasureTheory

/-- **The corner-to-centre measure `μ^Z_a`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), (9), p.33:
"`dμ^Z_a = C dt_i dt_j` on `K_a ∩ Z`, `i ≠ j ∈ [4] ∖ {a}`".

It is `C` times the area measure of the slice `{t_a = α}`, restricted to `Z`; points of
`Z` with `t_a = α` are exactly the points of the cross section `K_a ∩ Z` (p.33).

**Formalization Note.** `C` enters through `ENNReal.ofReal C` (the paper has `C > 0`). -/
noncomputable def muZ (α β C : ℝ) (a : Fin 4) : Measure (Fin 4 → ℝ) :=
  ENNReal.ofReal C • (planeMeasure a α).restrict (Zreg α β)

end MWCSherali


