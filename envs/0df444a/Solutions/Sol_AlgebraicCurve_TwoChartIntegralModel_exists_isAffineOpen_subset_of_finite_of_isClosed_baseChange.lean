-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/60c2029e-4bb7-5de3-90c3-9bd2d60cd9b6

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_forall_mem_of_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem solution
    {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    {A : Type u} [CommRing A] [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)] (φ : R →+* A)
    (T : Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))))
    (hT : T.Finite) (hTcl : ∀ t ∈ T, IsClosed ({t} : Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))))) :
    ∃ U : (pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))).Opens,
      IsAffineOpen U ∧ T ⊆ (U : Set ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ)))) := by
  classical
  let π := pullback.fst (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom φ))
  haveI : IsAffineHom π := MorphismProperty.pullback_fst _ _ inferInstance
  obtain ⟨W, hW, hWS⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_isAffineOpen_forall_mem_of_finset R F j
    (hT.toFinset.image π.base)
  refine ⟨π ⁻¹ᵁ W, hW.preimage π, fun t ht => ?_⟩
  show π.base t ∈ W
  exact hWS _ (Finset.mem_image_of_mem _ (hT.mem_toFinset.mpr ht))

end S_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_isAffineOpen_subset_of_finite_of_isClosed_baseChange (solution)
