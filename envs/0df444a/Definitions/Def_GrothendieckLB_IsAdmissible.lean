-- Prove2me | Definitions.Def_GrothendieckLB_IsAdmissible
-- name    : GrothendieckLB_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:13.282269+00:00
-- url     : https://prove2.me/theorems/492ca3f6-b2ae-4d4b-a6c6-299abbc466ef
-- title:
--   Admissible majorant value (Definition 9.1)
-- statement:
--   Let $H$ be odd and analytic near the origin with $H'(0)>0$, and write its local inverse branch as $H^{-1}(z)=\sum_{j\ge0}a_{2j+1}z^{2j+1}$. A number $\gamma>0$ is **admissible** for $H$ if the series converges absolutely at $\gamma$ and
--   $$
--   \sum_{j\ge0}|a_{2j+1}|\,\gamma^{2j+1}\le1 .
--   $$
--   Admissible values are the parameters of the inverse-majorant bound $K_G\le\pi/(2\gamma)$.
--
--   **Formalization Note** The conditions on $H$ are part of the predicate, because the page defines admissibility only for such $H$. The coefficients $a_n$ are the Taylor coefficients of the analytic inverse germ (`IsLocalInverseBranch`); the existential selects that unique germ.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 9.1, p.40

import Mathlib
import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_IsLocalInverseBranch
open Topology

namespace GrothendieckLB

/-- Definition 9.1 (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 9.1, p.40): `H` is odd and analytic near the origin with
`H′(0) > 0`, and `γ > 0` is admissible for `H`: with `H⁻¹(z) = ∑_{j≥0} a_{2j+1} z^{2j+1}`, the series
`∑_{j≥0} |a_{2j+1}| γ^{2j+1}` converges and is at most `1`.

**Formalization Note** The conditions on `H` are part of the predicate, because the page defines
admissibility only for such `H`. The existential over `G` selects the unique germ of the inverse
branch (see `IsLocalInverseBranch`). -/
def IsAdmissible (H : ℝ → ℝ) (γ : ℝ) : Prop :=
  (∀ᶠ t in 𝓝 (0 : ℝ), H (-t) = -H t) ∧ AnalyticAt ℝ H 0 ∧ 0 < deriv H 0 ∧ 0 < γ ∧
    ∃ G : ℝ → ℝ, IsLocalInverseBranch H G ∧
      Summable (fun j : ℕ => |taylorCoeff (2 * j + 1) G| * γ ^ (2 * j + 1)) ∧
      ∑' j : ℕ, |taylorCoeff (2 * j + 1) G| * γ ^ (2 * j + 1) ≤ 1

end GrothendieckLB


