-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8711bacc-1da4-50e1-ba9d-601d98c3ec03

import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_unit_of_isIntegral_of_ih
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsProper π]
    (F : OModulePresheaf π) (hc : F.IsCoherent) (hq : F.IsQuasicoherent) (K : V.OrderedAffineCover) :
    F.CechFinite K := by
  refine AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral π K ?_ ⊤ F hc hq ?_
  · intro Z₀ _ hint ih0
    haveI := hint
    haveI : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π) := inferInstance
    exact (AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff
        (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι (OModulePresheaf.unit _) K).mpr
      (AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih
        ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π) (K.preimage _)
        fun F' hc' hq' Y' hY' hs' =>
          AlgebraicGeometry.OModulePresheaf.cechFinite_preimage_of_ih π K ih0 F' hc' hq' Y' hY' hs')
  ·

    intro U hU
    have hUbot : (U : V.Opens) = ⊥ :=
      le_bot_iff.mp fun x hx => (Set.ext_iff.mp hU x).mp ⟨hx, trivial⟩
    haveI : Subsingleton Γ(V, U.1) := hUbot ▸ (inferInstance : Subsingleton Γ(V, (⊥ : V.Opens)))
    exact Module.subsingleton Γ(V, U.1) _

end S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper (solution)
