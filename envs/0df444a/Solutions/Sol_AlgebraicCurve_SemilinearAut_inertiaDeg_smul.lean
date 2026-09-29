-- Prove2me | solution 1 for AlgebraicCurve.SemilinearAut.inertiaDeg_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/db6d5cc5-36ba-5be1-9c60-6833cc578381

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_inertiaDeg_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

private def restrictSmulValuationSubringEquiv {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g')
    (w : Place K F') :
    (w.restrict F).toValuationSubring ≃+* ((g' • w).restrict F).toValuationSubring where
  toFun x := ⟨g • (x : F), by
    show algebraMap F F' (g • (x : F)) ∈ (g' • w).toValuationSubring
    rw [← hgg' (x : F), smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g' _ _ x.2⟩
  invFun y := ⟨g⁻¹ • (y : F), by
    show algebraMap F F' (g⁻¹ • (y : F)) ∈ w.toValuationSubring
    rw [← hgg'.inv (y : F)]
    have hy : algebraMap F F' (y : F) ∈ (g' • w).toValuationSubring := y.2
    rw [smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hy
    exact hy⟩
  left_inv x := by ext; exact inv_smul_smul g (x : F)
  right_inv y := by ext; exact smul_inv_smul g (y : F)
  map_mul' x y := by ext; exact smul_mul' g (x : F) (y : F)
  map_add' x y := by ext; exact smul_add g (x : F) (y : F)

@[scoped simp]
private theorem coe_restrictSmulValuationSubringEquiv_apply {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F')
    (x : (w.restrict F).toValuationSubring) :
    ((restrictSmulValuationSubringEquiv hgg' w x :
      ((g' • w).restrict F).toValuationSubring) : F) = g • (x : F) :=
  rfl

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') : (g' • w).inertiaDeg F = w.inertiaDeg F := by
  refine (Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (restrictSmulValuationSubringEquiv hgg' w))
    (smulResidueRingEquiv g' w) ?_).symm
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  show (Place.restrictResidueMap F (g' • w))
        (IsLocalRing.ResidueField.map _ (IsLocalRing.residue _ a))
      = (smulResidueRingEquiv g' w) ((Place.restrictResidueMap F w) (IsLocalRing.residue _ a))
  rw [IsLocalRing.ResidueField.map_residue, Place.restrictResidueMap_residue,
    Place.restrictResidueMap_residue, smulResidueRingEquiv,
    IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  refine congrArg _ (Subtype.ext ?_)
  show algebraMap F F' (g • (a : F)) = g' • (algebraMap F F' (a : F))
  exact (hgg' (a : F)).symm

end

end S_AlgebraicCurve_SemilinearAut_inertiaDeg_smul
end P2MW
export P2MW.S_AlgebraicCurve_SemilinearAut_inertiaDeg_smul (solution)
