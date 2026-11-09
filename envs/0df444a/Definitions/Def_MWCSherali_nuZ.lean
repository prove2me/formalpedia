-- Prove2me | Definitions.Def_MWCSherali_nuZ
-- name    : MWCSherali_nuZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:12.720383+00:00
-- url     : https://prove2.me/theorems/55f02456-a51a-4570-a623-4854b3ddd283
-- title:
--   The exit measures $\nu_a$
-- statement:
--   $$d\nu_a=C\,dt_i\,dt_j\quad\text{on }Z\cap\Gamma_a,\qquad i\neq j\in[4]\setminus\{a\},$$
--
--   the uniform measure (density $C$) on the sink hexagon of $Z$ opposite $e_a$, through which commodity $a$ exits.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.7, p.40

import Mathlib
import Definitions.Def_MWCSherali_planeMeasure
import Definitions.Def_MWCSherali_Zreg

namespace MWCSherali

open MeasureTheory

/-- **The exit measures `ν_a`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.7, p.40: "`dν_a` is defined on
`Z ∩ Γ_a` via `dν_a = C dt_i dt_j`, `i ≠ j ∈ [4] ∖ {a}`".

It is `C` times the area measure of the slice `{t_a = 0}`, restricted to `Z`.

**Formalization Note.** `C` enters through `ENNReal.ofReal C`. -/
noncomputable def nuZ (α β C : ℝ) (a : Fin 4) : Measure (Fin 4 → ℝ) :=
  ENNReal.ofReal C • (planeMeasure a 0).restrict (Zreg α β)

end MWCSherali


