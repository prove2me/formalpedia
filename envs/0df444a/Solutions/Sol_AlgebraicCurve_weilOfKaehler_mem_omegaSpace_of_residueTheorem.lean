-- Prove2me | solution 1 for AlgebraicCurve.weilOfKaehler_mem_omegaSpace_of_residueTheorem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c81f4ce0-82fe-58be-9d3d-fef56b3b6bee

import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]] [HasPrincipalDivisors K F]
    (hRT : ResidueTheorem K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    weilOfKaehler K F hω ∈ omegaSpace (canonicalDivisorOf hω) :=
  by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
  rw [map_add, weilOfKaehler_vanish_adeleBdd_canonical hω (Submodule.mem_comap.mp hβ)]
  obtain ⟨f, hf⟩ := Submodule.mem_comap.mp hγ
  have hγ' : γ = ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ := Subtype.ext hf.symm
  rw [hγ', hRT hω f, add_zero]

end S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem
end P2MW
export P2MW.S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem (solution)
