-- Prove2me | solution 1 for AlgebraicGeometry.SymmetricFiniteFrame.exists_bounded_double
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:22:42.430644+00:00
-- url     : https://prove2.me/submissions/268c1f37-e95b-4929-ac59-fd3a39457ac4

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_pullback_pointLogHeight_eq
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensorPow_pointLogHeight_eq_nsmul_and_isFinite
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_abs_pointLogHeight_sub_le_of_iso_of_isFinite

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.SymmetricFiniteFrame

private theorem point_comp_double {K : Type} [Field K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f)
    (x : Scheme.KPoint f) :
    x.1 ≫ G.schemeNsmul 2 = (G.mul (𝟙 _) x x).1 := by
  have hid : GoodReductionJacobian.schemeHomOverComp x.1 x.2
      (RelativeGroupLaw.idPoint : SchemeHomOver f f) = x := by
    apply Subtype.ext
    exact Category.comp_id _
  have hn := G.nsmul_natural f (𝟙 _) x.1 x.2 2
    (RelativeGroupLaw.idPoint : SchemeHomOver f f)
  rw [hid] at hn
  have hv := congrArg Subtype.val hn
  simpa only [GoodReductionJacobian.schemeHomOverComp, RelativeGroupLaw.schemeNsmul,
    RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_zero, G.one_mul] using hv

/-- A finite symmetric frame has a uniformly bounded doubling defect. -/
theorem _root_.solution {K : Type} [Field K] [NumberField K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} {G : RelativeGroupLaw K f} (F : SymmetricFiniteFrame K f G) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ x : Scheme.KPoint f, |F.height (G.mul (𝟙 _) x x) - 4 * F.height x| ≤ C₂  := by
  classical
  obtain ⟨Nq, Q, hQ, hq⟩ :=
    F.presentation.exists_tensorPow_pointLogHeight_eq_nsmul_and_isFinite
      F.presentation_finite 4 (by norm_num)
  have hpb := F.presentation.exists_pullback_pointLogHeight_eq (G.schemeNsmul 2)
  obtain ⟨P₀, _, _, hp⟩ := hpb
  let P : ((Scheme.Modules.pullback (G.schemeNsmul 2)).obj F.line).ProjPresentation f F.N :=
    { P₀ with toProj_π := P₀.toProj_π.trans (G.schemeNsmul_over 2) }
  obtain ⟨C, hC, hbound⟩ :=
    Q.exists_abs_pointLogHeight_sub_le_of_iso_of_isFinite P
      F.doubleIso.some.symm hQ
  refine ⟨C, hC, ?_⟩
  intro x
  have hd : P.pointLogHeight x = F.height (G.mul (𝟙 _) x x) := by
    have hx : x.1 ≫ (G.schemeNsmul 2 ≫ f) = 𝟙 _ := by
      rw [G.schemeNsmul_over]
      exact x.2
    change P₀.pointLogHeight ⟨x.1, hx⟩ = _
    rw [hp]
    apply congrArg F.height
    apply Subtype.ext
    exact point_comp_double G x
  have hb := hbound x
  rw [hq, hd] at hb
  simpa only [height, Nat.cast_ofNat, abs_sub_comm] using hb

end AlgebraicGeometry.SymmetricFiniteFrame
