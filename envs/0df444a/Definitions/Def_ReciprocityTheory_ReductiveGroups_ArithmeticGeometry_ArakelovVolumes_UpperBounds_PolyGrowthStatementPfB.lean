-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PolyGrowthStatementPfB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PolyGrowthStatementPfB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:53:45.941751+00:00
-- url     : https://prove2.me/theorems/7aa48ea7-638f-45c9-904e-f3523f27e46d
-- title:
--   Poly Growth Statement Pf B
-- statement:
--   Definitions and structural lemmas for Poly Growth Statement Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PolyGrowthStatementPfB.lean

import Mathlib
import Definitions.Def_Lemmata_CofiniteContinuousBounds_LeOfCofinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PG
open MvPolynomial
variable {D : ℕ}
noncomputable def lineHom (a w : Fin D → ℂ) : MvPolynomial (Fin D) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval fun i => Polynomial.C (a i) + Polynomial.C (w i) * Polynomial.X
end ReciprocityTheory.ChartRestriction.G.AR.Up.PG


