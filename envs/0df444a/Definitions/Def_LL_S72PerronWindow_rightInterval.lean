-- Prove2me | Definitions.Def_LL_S72PerronWindow_rightInterval
-- name    : LL_S72PerronWindow_rightInterval
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-25T13:03:06.221302+00:00
-- url     : https://prove2.me/theorems/c2c7c232-13cf-52e2-901b-3b79d1094847
-- title:
--   The window $J=(\lfloor x^{11/20+\varepsilon}\rfloor,\lfloor 2x^{11/20+\varepsilon}\rfloor]$
-- statement:
--   For real $\varepsilon,x$, the finite set of natural numbers $m$ with $\lfloor Y\rfloor_+<m\le\lfloor 2Y\rfloor_+$, where $Y=x^{11/20+\varepsilon}$ is Mathlib's real power and $\lfloor\cdot\rfloor_+$ the natural number floor.

import Mathlib

namespace LL_S72PerronWindow

noncomputable section

open Classical Complex

noncomputable def rightInterval (ε x : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊

end

end LL_S72PerronWindow


