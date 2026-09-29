-- Prove2me | solution 1 for AlgebraicCurve.exists_isAffineOpen_sup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2eb8bb60-4074-59f1-be63-6620cf503ad0

import Mathlib
import Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (haff : ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :
    ∃ U V : C.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen (U ⊓ V) ∧ U ⊔ V = ⊤ := by
  classical

  haveI : C.IsSeparated := ⟨by
    rw [show terminal.from C = c ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩

  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨U, hU, hxU⟩ := haff {x}
  have hUne : (U : Set C).Nonempty := ⟨x, hxU x (Finset.mem_singleton_self x)⟩

  have hfin : ((U : Set C)ᶜ).Finite := AlgebraicCurve.finite_compl_of_isOpen c U hUne
  obtain ⟨V, hV, hFV⟩ := haff hfin.toFinset
  refine ⟨U, V, hU, hV, hU.inf hV, ?_⟩
  refine top_le_iff.mp fun y _ => ?_
  by_cases hy : y ∈ U
  · exact Or.inl hy
  · exact Or.inr (hFV y (hfin.mem_toFinset.mpr hy))

end S_AlgebraicCurve_exists_isAffineOpen_sup_eq_top
end P2MW
export P2MW.S_AlgebraicCurve_exists_isAffineOpen_sup_eq_top (solution)
