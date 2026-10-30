-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIV_shared_riemannXiUpper
-- name    : RamanujanLostNotebook_PartIV_shared_riemannXiUpper
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-06T15:08:54.634012+00:00
-- url     : https://prove2.me/theorems/eeaca314-4f7f-41aa-8484-410026ad5e28
-- title:
--   Ramanujan's Lost Notebook Part IV, shared: riemannXiUpper
-- statement:
--   Riemann's `Ξ`-function, `Ξ(t) = ξ(1/2 + i t)`: equation (3.4.30), p. 108, and
--   equation (13.3.1) of the book.  `riemannXi` is the entire function `ξ` with no exceptional
--   points, so this is the classical `Ξ(t)` for every complex `t`; for real `t` its values are
--   real, and `Ξ` is even.  Reference value: `Ξ(0) = ξ(1/2) = 0.4971207781…`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part IV, Springer 2013.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_shared_riemannXi

namespace RamanujanLostNotebook.PartIV

/-- Riemann's `Ξ`-function, `Ξ(t) = ξ(1/2 + i t)`: equation (3.4.30), p. 108, and
equation (13.3.1) of the book.  `riemannXi` is the entire function `ξ` with no exceptional
points, so this is the classical `Ξ(t)` for every complex `t`; for real `t` its values are
real, and `Ξ` is even.  Reference value: `Ξ(0) = ξ(1/2) = 0.4971207781…`. -/
noncomputable def riemannXiUpper (t : ℂ) : ℂ :=
  riemannXi (1 / 2 + Complex.I * t)

end RamanujanLostNotebook.PartIV


