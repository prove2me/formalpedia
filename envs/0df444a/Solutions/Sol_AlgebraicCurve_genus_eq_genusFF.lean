-- Prove2me | solution 1 for AlgebraicCurve.genus_eq_genusFF
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/854eb426-e870-5e37-b092-36e34e7cc43c

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Theorems.Thm_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_genus_eq_genusFF

open AlgebraicCurve KaehlerDifferential

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F) (hWDA : AlgebraicCurve.WeilDualityAdelic K F)
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    AlgebraicCurve.genus K F = AlgebraicCurve.genusFF K F := by
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have h1 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (ell (canonicalDivisorOf hω - 0) : ℤ) := hWDA hω 0
  rw [sub_zero] at h1
  have h2 : (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) :=
    ell_canonicalDivisor_eq_genus_of_riemannRoch hRR hC hω
  have h3 : indexOfSpecialty (0 : Divisor K F) = Module.finrank K (H1 (0 : Divisor K F)) :=
    indexOfSpecialty_eq_finrank_H1 0
  have h4 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (genusFF K F : ℤ) := by
    rw [genusFF, ← h3]
  have : (genus K F : ℤ) = (genusFF K F : ℤ) := by
    rw [← h4, h1, h2]
  exact_mod_cast this

end S_AlgebraicCurve_genus_eq_genusFF
end P2MW
export P2MW.S_AlgebraicCurve_genus_eq_genusFF (solution)
