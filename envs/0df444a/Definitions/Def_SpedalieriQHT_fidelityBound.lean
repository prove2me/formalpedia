-- Prove2me | Definitions.Def_SpedalieriQHT_fidelityBound
-- name    : SpedalieriQHT_fidelityBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:16.226604+00:00
-- url     : https://prove2.me/theorems/0ac3767b-edc5-4f71-ae49-5c875f930980
-- title:
--   Fidelity bound $H_F(r)=\sup_{0\le s<1}\frac{-rs-\ln F}{1-s}$
-- statement:
--   For real numbers $F$ and $r$, the **fidelity bound** is
--   $$
--   H_F(r)=\sup_{0\le s<1}\frac{-r s-\ln F}{1-s}\in[-\infty,+\infty],
--   $$
--   with $\ln 0=-\infty$. It is the quantum Hoeffding bound with the s-overlap $C_s$ replaced by the constant $F$; the paper uses it with $F$ the fidelity of the two states.
--
--   **Formalization Note** This is the supremum (18), not the closed form (19), which is the theorem `SpedalieriQHT.eq_19`. Values in `EReal`.
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. III, Eq. (18), p.3

import Mathlib
import Definitions.Def_HayashiHoeffding_elog

open HayashiHoeffding (elog)

namespace SpedalieriQHT

/-- The fidelity bound `H_F(r) = sup_{0 ≤ s < 1} (−r s − ln F)/(1 − s)`.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. III, Eq. (18), p.3:
"H_F(r) := sup_{0≤s<1} (−r s − ln F)/(1 − s)".

**Formalization Note.** This is the supremum of (18), not its closed form (19), which is a
theorem (`SpedalieriQHT.eq_19`). Values in `EReal`; `ln F` is the published extended logarithm `HayashiHoeffding.elog F`,
so `F = 0` gives `+∞` termwise. The parameter `F` is any real number; the theorems apply it to
a fidelity. -/
noncomputable def fidelityBound (F r : ℝ) : EReal :=
  ⨆ s ∈ Set.Ico (0 : ℝ) 1, (((-(r * s) : ℝ) : EReal) - elog F) / ((1 - s : ℝ) : EReal)

end SpedalieriQHT


