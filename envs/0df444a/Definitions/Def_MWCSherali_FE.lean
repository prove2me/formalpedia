-- Prove2me | Definitions.Def_MWCSherali_FE
-- name    : MWCSherali_FE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:19.219107+00:00
-- url     : https://prove2.me/theorems/9bcd9b7a-b293-4755-8169-b04c194efeb2
-- title:
--   The simplex-edge flow $F^{E_{ab}}_{a,b}$
-- statement:
--   On the simplex edge $E_{ab}$ commodity $a$ flows in direction $b$ with
--
--   $$dB^{E_{ab}}_b=dF^{E_{ab}}_{a,b}=C\beta(w-1+\alpha)\,dw,$$
--
--   supported on $\{y_{ab}(w)\mid 1-\alpha\le w\le\alpha\}$; the factor $w-1+\alpha$ reflects the constant rate at which the edge flow sheds into the tube $T_{ab}$.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4.2, p.34

import Mathlib
import Definitions.Def_MWCSherali_yab

namespace MWCSherali

open MeasureTheory

/-- **The simplex-edge flow `F^{E_{ab}}_{a,b}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4.2, p.34: "On the simplex edge
`E_{ab}`, we have the simplex-edge flow `F^{E_{ab}}_{a,b}` supported on
`{y_{ab}(w) | 1 − α ≤ w ≤ α}`, defined by `dB^{E_{ab}}_b = dF^{E_{ab}}_{a,b} = Cβ(w − 1 + α) dw`."

It is the image under `w ↦ y_{ab}(w)` of the measure `Cβ(w − 1 + α) dw` on `[1 − α, α]`: the
flow of commodity `a` in direction `b` on the edge `E_{ab}`, and also the capacity
`B^{E_{ab}}_b` in direction `b`.

**Formalization Note.** The density enters through `ENNReal.ofReal`; it is nonnegative on
`[1 − α, α]` when `C, β > 0`. -/
noncomputable def FE (α β C : ℝ) (a b : Fin 4) : Measure (Fin 4 → ℝ) :=
  Measure.map (yab a b)
    ((volume.restrict (Set.Icc (1 - α) α)).withDensity fun w =>
      ENNReal.ofReal (C * β * (w - 1 + α)))

end MWCSherali


