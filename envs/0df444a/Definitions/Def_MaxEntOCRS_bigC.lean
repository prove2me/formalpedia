-- Prove2me | Definitions.Def_MaxEntOCRS_bigC
-- name    : MaxEntOCRS_bigC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:12.675727+00:00
-- url     : https://prove2.me/theorems/b104d144-4f58-4de8-be79-2b6bc83626e3
-- title:
--   The constant $C = 1/\alpha$
-- statement:
--   The constant $C = 1/\alpha$, where $\alpha = (\sqrt3-1)/2$; it equals $1 + \sqrt3$. Theorem 2 is equivalent to the local bound $K \le C$ for the localization quantity $K$ of Section 3.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4 (opening display)

import Mathlib
import Definitions.Def_MaxEntOCRS_alpha

namespace MaxEntOCRS

/-- The constant `C = 1/α` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4, opening display; equal to `1 + √3`). Theorem 2 is
equivalent to `K ≤ C` (§3, p.5). -/
noncomputable def bigC : ℝ := 1 / alpha

end MaxEntOCRS


