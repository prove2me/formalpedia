-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PolyGrowthStatementPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PolyGrowthStatementPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:45.75306+00:00
-- url     : https://prove2.me/theorems/cdc03298-7fe2-4ec2-8d21-02f3650e6b0e
-- title:
--   Poly Growth Statement Pf
-- statement:
--   Definitions and structural lemmas for Poly Growth Statement Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PolyGrowthStatementPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PolyGrowthStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
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
noncomputable def liftHom (a : Fin D → ℂ) :
    MvPolynomial (Fin D) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (Fin D) ℂ) :=
  aeval fun i => Polynomial.C (C (a i)) + Polynomial.C (X i - C (a i)) * Polynomial.X
end ReciprocityTheory.ChartRestriction.G.AR.Up.PG
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
end ReciprocityTheory.ChartRestriction.G.AR.Up


