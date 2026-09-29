-- Prove2me | solution 1 for AlgebraicCurve.kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/45f4a6c1-2df6-5ff2-993a-433bd2064ed0

import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
    {v : Place K F} [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : f ∈ v.toValuationSubring) (hω : ω = f • v.dCoord)
    {g : F} (hg : g ∈ v.toValuationSubring) :
    kaehlerResidueTerm ω (diagonalHom K F g) v = 0 := by
  unfold kaehlerResidueTerm
  rw [diagonalHom_apply, v.differentialCoeff_unique hω, v.localResidue_of_mem (mul_mem hg hf), map_zero]

end S_AlgebraicCurve_kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord
end P2MW
export P2MW.S_AlgebraicCurve_kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord (solution)
