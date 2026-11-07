-- Prove2me | Definitions.Def_MaxEntOCRS_smallC
-- name    : MaxEntOCRS_smallC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:21.440887+00:00
-- url     : https://prove2.me/theorems/c39b49f3-d16e-4272-9104-8e1ace2ce278
-- title:
--   The constant $c = \alpha/\beta$
-- statement:
--   The constant $c = \alpha/\beta$, where $\alpha = (\sqrt3-1)/2$ and $\beta = 1-\alpha$; it equals $1/\sqrt3$, so $c^2 = 1/3$. It bounds the aggregated activities between a pair vertex and its neighbours in Eq. (3).
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4 (opening display)

import Mathlib
import Definitions.Def_MaxEntOCRS_alpha
import Definitions.Def_MaxEntOCRS_beta

namespace MaxEntOCRS

/-- The constant `c = α/β` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4, opening display; equal to `1/√3`). It bounds the
aggregated activities in Eq. (3), p.7. -/
noncomputable def smallC : ℝ := alpha / beta

end MaxEntOCRS


