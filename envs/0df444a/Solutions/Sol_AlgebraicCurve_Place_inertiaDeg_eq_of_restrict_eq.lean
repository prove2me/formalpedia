-- Prove2me | solution 1 for AlgebraicCurve.Place.inertiaDeg_eq_of_restrict_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b56f5bef-a420-5ab3-9a1c-8a4dd8a8dd24

import Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.FieldTheory.Galois.Basic
import Theorems.Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
import Theorems.Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false
noncomputable section
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.AlgebraicCurve IsDedekindDomain"
open scoped Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "SemilinearAut.IntertwinesAlong Place SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.ofAlgAut_smul Place.exists_algEquiv_smul_eq_of_restrict_eq SemilinearAut.inertiaDeg_smul"
p2m_open "AlgebraicCurve"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrict inertiaDeg exists_algEquiv_smul_eq_of_restrict_eq"
p2m_open "AlgebraicCurve.Place"

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

private theorem intertwinesAlong_one_ofAlgAut (σ : M ≃ₐ[F'] M) :
    SemilinearAut.IntertwinesAlong (algebraMap F' M) (1 : SemilinearAut K F')
      (SemilinearAut.ofAlgAut (σ.restrictScalars K)) := by
  intro x
  rw [one_smul, SemilinearAut.ofAlgAut_smul]
  exact σ.commutes x

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq.AlgebraicCurve.Place in
theorem solution {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    W'.inertiaDeg F' = W.inertiaDeg F' := by
  obtain ⟨σ, rfl⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq W W' h
  exact SemilinearAut.inertiaDeg_smul (intertwinesAlong_one_ofAlgAut σ) W

end

end S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq
end P2MW
export P2MW.S_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq (solution)
