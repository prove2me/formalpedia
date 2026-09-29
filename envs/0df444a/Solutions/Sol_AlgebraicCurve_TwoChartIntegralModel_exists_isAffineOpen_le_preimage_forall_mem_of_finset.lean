-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_le_preimage_forall_mem_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/4548361c-8ece-51c3-a8b0-33fb7b58a9eb

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_forall_mem_of_finset
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_le_preimage_forall_mem_of_finset
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

universe u

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (U : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens)
    (V : (Spec (CommRingCat.of R)).affineOpens) (S : Finset ↥U)
    (hS : ∀ x ∈ S, (U.ι ≫ toBase R F j).base x ∈ (V : (Spec (CommRingCat.of R)).Opens)) :
    ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧
      W ≤ (U.ι ≫ toBase R F j) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧ ∀ x ∈ S, x ∈ W := by
  exact AlgebraicGeometry.exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
    (AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_forall_mem_of_finset R F j) U
    ((toBase R F j) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens)) S hS

#print axioms solution

end S_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_le_preimage_forall_mem_of_finset
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_le_preimage_forall_mem_of_finset (solution)
