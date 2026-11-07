-- Prove2me | Definitions.Def_MaxEntOCRS_beta
-- name    : MaxEntOCRS_beta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:11.336743+00:00
-- url     : https://prove2.me/theorems/1b552934-d79b-46cc-8e8c-1a8606a8911b
-- title:
--   The constant $\beta = 1 - \alpha$
-- statement:
--   The constant $\beta = 1 - \alpha$, where $\alpha = (\sqrt3-1)/2$; it equals $\sqrt3\,\alpha$. Under the occupancy hypothesis of Theorem 2, every vertex is uncovered with probability at least $\beta$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4 (opening display)

import Mathlib
import Definitions.Def_MaxEntOCRS_alpha

namespace MaxEntOCRS

/-- The constant `β = 1 − α` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4, opening display; equal to `√3 α`). -/
noncomputable def beta : ℝ := 1 - alpha

end MaxEntOCRS


