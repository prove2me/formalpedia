-- Prove2me | Definitions.Def_MWCSherali_yab
-- name    : MWCSherali_yab
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:09.884083+00:00
-- url     : https://prove2.me/theorems/1de45914-6944-403b-a0b6-262cebf28a45
-- title:
--   The simplex edge $E_{ab}$, parametrized
-- statement:
--   For terminals $a,b$,
--
--   $$y_{ab}(w)=we_a+(1-w)e_b,\qquad 0\le w\le1,$$
--
--   parametrizes the simplex edge $E_{ab}$ from $e_b$ ($w=0$) to $e_a$ ($w=1$).
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.31

import Mathlib

namespace MWCSherali

/-- **The simplex edge `E_{ab}` parametrized.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4, p.31:
"`y_{ab}(w) = w e_a + (1 − w) e_b`, `0 ≤ w ≤ 1`".

**Formalization Note.** `e_a = Pi.single a 1`; indices are 0-based. -/
def yab (a b : Fin 4) (w : ℝ) : Fin 4 → ℝ :=
  w • Pi.single a 1 + (1 - w) • Pi.single b 1

end MWCSherali


