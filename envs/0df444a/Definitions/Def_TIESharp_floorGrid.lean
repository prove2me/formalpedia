-- Prove2me | Definitions.Def_TIESharp_floorGrid
-- name    : TIESharp_floorGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:58.074766+00:00
-- url     : https://prove2.me/theorems/96ae71d5-0c9f-47f7-a68a-48369f9606ab
-- title:
--   Flooring a profile to the $h$-grid, $G_h(t)$
-- statement:
--   For a mesh $h>0$ write $\lfloor s\rfloor_h=h\lfloor s/h\rfloor$ and
--   $$G_h(t)=(\lfloor t_{ij}\rfloor_h)_{i,j}.$$
--   On nonnegative profiles $G_h$ floors every report coordinate to the nonnegative $h$-grid. The grid approximations of a family are $y^m\circ G_h$, $q^m\circ G_h$ and $V^m_i\circ G_h$; they are Borel measurable step functions even if the family is not measurable.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §4.2.1, p.17

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- **Flooring a profile to the `h`-grid** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, §4.2.1, p.17): `⌊s⌋_h = h ⌊s / h⌋` and `G_h(t) = (⌊t_ij⌋_h)_{i,j}`.
On nonnegative profiles and `h > 0` the result lies in the nonnegative `h`-grid. -/
noncomputable def floorGrid {n m : ℕ} (h : ℝ) (t : Fin n → Fin m → ℝ) : Fin n → Fin m → ℝ :=
  fun i j => h * (⌊t i j / h⌋ : ℝ)

end TIESharp


