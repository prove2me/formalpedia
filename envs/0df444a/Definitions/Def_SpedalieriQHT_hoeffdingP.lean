-- Prove2me | Definitions.Def_SpedalieriQHT_hoeffdingP
-- name    : SpedalieriQHT_hoeffdingP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:50.362622+00:00
-- url     : https://prove2.me/theorems/e68fbc3a-136e-4c6d-a201-1d27d9ac5bfc
-- title:
--   The Hoeffding function $P(r,s)=\frac{-rs-\ln C_s}{1-s}$
-- statement:
--   For bounded operators $\rho_0,\rho_1$ and real numbers $r,s$,
--   $$
--   P(r,s)=\frac{-r s-\ln C_s}{1-s}\in[-\infty,+\infty],
--   $$
--   where $C_s$ is the s-overlap and $\ln 0=-\infty$, so that $P(r,s)=+\infty$ when $C_s=0$ and $s<1$.
--
--   The quantum Hoeffding bound (15) is the supremum of $P(r,s)$ over $0\le s<1$.
--
--   **Formalization Note** Values in `EReal`. The term $-rs$ is a finite real, so no $\infty-\infty$ occurs; the division is by the real $1-s$, positive on the range of (15).
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. II B, Eq. (15), p.3

import Mathlib
import Definitions.Def_HayashiHoeffding_elog
import Definitions.Def_SpedalieriQHT_sOverlap

open HayashiHoeffding (elog)

namespace SpedalieriQHT

/-- The Hoeffding function `P(r, s) = (−r s − ln C_s)/(1 − s)`.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. II B, Eq. (15), p.3:
"P(r, s) := (−r s − ln C_s)/(1 − s)", with `C_s` the s-overlap (16).

**Formalization Note.** Values in `EReal`, with `ln` the published extended logarithm `HayashiHoeffding.elog`
(`ln 0 = −∞`), so `P(r, s) = +∞` when `C_s = 0`. The term `−r s` is a finite real, so no
`⊤ − ⊤` arises. The division is by the real `1 − s`, positive on the range `0 ≤ s < 1` of (15). -/
noncomputable def hoeffdingP {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ0 ρ1 : H →L[ℂ] H) (r s : ℝ) : EReal :=
  (((-(r * s) : ℝ) : EReal) - elog (sOverlap ρ0 ρ1 s)) / ((1 - s : ℝ) : EReal)

end SpedalieriQHT


