-- Prove2me | Definitions.Def_SecondBestBT_Supplement_baseState
-- name    : SecondBestBT_Supplement_baseState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:35:58.839047+00:00
-- url     : https://prove2.me/theorems/96a84cd2-37f4-4757-a493-69c6447db591
-- title:
--   Base clear state $\omega_0$
-- statement:
--   The **base clear state** is
--   $$
--   \omega_0:=\Big(\frac{\beta}{1+\alpha};\ r_0\Big)=\Big(\frac{\beta}{1+\alpha};\ 0\Big),
--   $$
--   the state reached by Algorithm 1 at buyer value $b=1$: the clear-state condition $H(1;x)=0$ forces $x(0,1)=\beta/(1+\alpha)$, and $r_0=F_S(-1)/f_S(0)=0$. Every canonical execution of the state-transition procedure ALG2 starts from it.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 5.1, "Base Clear State", p.17

import Mathlib

open scoped ENNReal

namespace SecondBestBT.Supplement

/-- The **base clear state** `ω0 := (β / (1 + α) ; r_0)` with `r_0 = 0` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 5.1,
"Base Clear State", p.17): the state reached at `b = 1`, one ratio entry, the value `0`. -/
noncomputable def baseState (α β : ℝ) : ℝ × List ℝ≥0∞ :=
  (β / (1 + α), [0])

end SecondBestBT.Supplement


