-- Prove2me | solution 1 for AlgebraicGeometry.isAffine_of_isClosedImmersion_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/073cb8dc-920b-59e8-9de8-4cd38938cc52

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_le_isNilpotent_mem_ideal_of_le_nilradical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective quasiSeparatedSpace_of_quasiSeparated Scheme.Hom.le_ker_comp Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal Scheme.Hom IsAffine.of_isIso QuasiCompact IsAffine Scheme.Hom.support_ker Scheme Scheme.exists_isAffine_of_isLimit QuasiCompact.compactSpace_of_compactSpace Scheme.IdealSheafData.zero_eq_bot Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.vanishingIdeal_top IsClosedImmersion Scheme.IdealSheafData.ideal_mono IsClosedImmersion.of_comp_isClosedImmersion IsClosedImmersion.lift Scheme.IdealSheafData.inclusion_comp Scheme.IdealSheafData.add_eq_sup IsClosedImmersion.lift_fac Scheme.IdealSheafData.inclusion_id Scheme.IdealSheafData.inclusion_subschemeι Scheme.IdealSheafData.inclusion IsAffineHom Scheme.IdealSheafData isAffine_of_isClosedImmersion_of_isNilpotent_ker Scheme.IdealSheafData.exists_le_isNilpotent_mem_ideal_of_le_nilradical"
p2m_open "AlgebraicGeometry"

namespace ThickAffMain

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData CategoryTheory.Limits"

variable {X : Scheme.{u}} (I : X.IdealSheafData)

def NilpIdeal : Type u := {J : X.IdealSheafData // J ≤ I ∧ IsNilpotent J}

namespace NilpIdeal

variable {I}

scoped instance : SemilatticeSup (NilpIdeal I) :=
  Subtype.semilatticeSup fun J K hJ hK =>
    ⟨sup_le hJ.1 hK.1, by
      rw [← Scheme.IdealSheafData.add_eq_sup]
      exact Commute.isNilpotent_add (Commute.all _ _) hJ.2 hK.2⟩

scoped instance : OrderBot (NilpIdeal I) where
  bot := ⟨⊥, bot_le, by rw [← Scheme.IdealSheafData.zero_eq_bot]; exact IsNilpotent.zero⟩
  bot_le J := (bot_le : (⊥ : X.IdealSheafData) ≤ J.1)

scoped instance : Nonempty (NilpIdeal I) := ⟨⊥⟩

theorem coe_le_coe {J K : NilpIdeal I} : J.1 ≤ K.1 ↔ J ≤ K := Iff.rfl

variable (I)

@[reducible] noncomputable def diagram : (NilpIdeal I)ᵒᵖ ⥤ Scheme.{u} where
  obj J := J.unop.1.subscheme
  map {J K} f := Scheme.IdealSheafData.inclusion (show K.unop.1 ≤ J.unop.1 from f.unop.le)
  map_id _ := Scheme.IdealSheafData.inclusion_id _
  map_comp _ _ := (Scheme.IdealSheafData.inclusion_comp _ _).symm

@[scoped simp] theorem diagram_obj (J : (NilpIdeal I)ᵒᵖ) : (diagram I).obj J = J.unop.1.subscheme := rfl

@[scoped simp] theorem diagram_map {J K : (NilpIdeal I)ᵒᵖ} (f : J ⟶ K) :
    (diagram I).map f = Scheme.IdealSheafData.inclusion (show K.unop.1 ≤ J.unop.1 from f.unop.le) :=
  rfl

@[reducible] noncomputable def cone : Cone (diagram I) where
  pt := I.subscheme
  π :=
  { app J := Scheme.IdealSheafData.inclusion J.unop.2.1
    naturality J K f := by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
        Scheme.IdealSheafData.inclusion_comp] }

@[scoped simp] theorem cone_pt : (cone I).pt = I.subscheme := rfl

@[scoped simp] theorem cone_π_app (J : (NilpIdeal I)ᵒᵖ) :
    (cone I).π.app J = Scheme.IdealSheafData.inclusion J.unop.2.1 := rfl

variable {I}

theorem cone_app_comp_subschemeι (s : Cone (diagram I)) (J : NilpIdeal I) :
    @CategoryStruct.comp Scheme _ s.pt J.1.subscheme X (s.π.app (op J)) J.1.subschemeι =
      @CategoryStruct.comp Scheme _ s.pt (⊥ : NilpIdeal I).1.subscheme X (s.π.app (op ⊥))
        (⊥ : NilpIdeal I).1.subschemeι := by
  have w := s.w ((homOfLE (bot_le : (⊥ : NilpIdeal I) ≤ J)).op)
  dsimp only [Functor.const_obj_obj, diagram, Opposite.unop_op] at w
  rw [← Scheme.IdealSheafData.inclusion_subschemeι (bot_le : (⊥ : NilpIdeal I).1 ≤ J.1),
    ← Category.assoc]
  exact congrArg (fun φ => φ ≫ (⊥ : NilpIdeal I).1.subschemeι) w

variable (I)

noncomputable def isLimitCone (hI : I ≤ ⨆ J : NilpIdeal I, J.1) : IsLimit (cone I) where
  lift s := IsClosedImmersion.lift I.subschemeι
    (@CategoryStruct.comp Scheme _ s.pt (⊥ : NilpIdeal I).1.subscheme X (s.π.app (op ⊥))
      (⊥ : NilpIdeal I).1.subschemeι) (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    refine hI.trans (iSup_le fun J => ?_)
    rw [← cone_app_comp_subschemeι s J]
    conv_lhs => rw [← J.1.ker_subschemeι]
    exact Scheme.Hom.le_ker_comp _ _)
  fac s J := by
    rw [← cancel_mono J.unop.1.subschemeι]
    dsimp only [Functor.const_obj_obj, cone, diagram, Opposite.unop_op]
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, IsClosedImmersion.lift_fac]
    exact (cone_app_comp_subschemeι s J.unop).symm
  uniq s m hm := by
    rw [← cancel_mono I.subschemeι, IsClosedImmersion.lift_fac,
      ← Scheme.IdealSheafData.inclusion_subschemeι (⊥ : NilpIdeal I).2.1, ← Category.assoc]
    have := hm (op ⊥)
    dsimp only [Functor.const_obj_obj, cone, diagram, Opposite.unop_op] at this ⊢
    rw [this]

scoped instance isAffineHom_diagram_map {J K : (NilpIdeal I)ᵒᵖ} (f : J ⟶ K) : IsAffineHom ((diagram I).map f) := by
  have : IsClosedImmersion (Scheme.IdealSheafData.inclusion (show K.unop.1 ≤ J.unop.1 from f.unop.le) ≫
      K.unop.1.subschemeι) := by
    rw [Scheme.IdealSheafData.inclusion_subschemeι]; infer_instance
  have := IsClosedImmersion.of_comp_isClosedImmersion
    (Scheme.IdealSheafData.inclusion (show K.unop.1 ≤ J.unop.1 from f.unop.le)) K.unop.1.subschemeι
  dsimp only [diagram]
  infer_instance

scoped instance compactSpace_diagram_obj [CompactSpace X] (J : (NilpIdeal I)ᵒᵖ) :
    CompactSpace ((diagram I).obj J) :=
  QuasiCompact.compactSpace_of_compactSpace J.unop.1.subschemeι

scoped instance quasiSeparatedSpace_diagram_obj [QuasiSeparatedSpace X] (J : (NilpIdeal I)ᵒᵖ) :
    QuasiSeparatedSpace ((diagram I).obj J) :=
  quasiSeparatedSpace_of_quasiSeparated J.unop.1.subschemeι

end NilpIdeal
p2m_reactivate "P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective.AlgebraicGeometry.ThickAffMain.NilpIdeal"

open NilpIdeal in
theorem isAffine_of_isClosedImmersion_of_surjective {X₀ X : Scheme.{u}} (i : X₀ ⟶ X)
    [IsClosedImmersion i] [Surjective i] [IsAffine X₀] : IsAffine X := by

  let e : X₀ ≃ₜ X := i.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective i.surjective
  haveI : CompactSpace X := e.compactSpace
  haveI : QuasiSeparatedSpace X := (quasiSeparatedSpace_congr e).mp inferInstance

  set I := i.ker with hIdef
  have hInil : I ≤ X.nilradical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_top,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, hIdef, top_le_iff]
    ext1
    rw [Scheme.Hom.support_ker, i.surjective.range_eq, closure_univ]
    rfl

  have hI : I ≤ ⨆ J : NilpIdeal I, J.1 := by
    intro U s hs
    obtain ⟨J, hJI, hJ, hsJ⟩ :=
      AlgebraicGeometry.Scheme.IdealSheafData.exists_le_isNilpotent_mem_ideal_of_le_nilradical I hInil U s hs
    have : (⟨J, hJI, hJ⟩ : NilpIdeal I).1.ideal U ≤ (⨆ J : NilpIdeal I, J.1).ideal U :=
      Scheme.IdealSheafData.ideal_mono (le_iSup (fun J : NilpIdeal I => J.1) ⟨J, hJI, hJ⟩) U
    exact this hsJ

  haveI : IsAffine (cone I).pt := by
    change IsAffine i.image
    exact IsAffine.of_isIso (inv i.toImage)
  obtain ⟨J, hJ⟩ := Scheme.exists_isAffine_of_isLimit (diagram I) (cone I) (isLimitCone I hI)
  change IsAffine J.unop.1.subscheme at hJ
  exact AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isNilpotent_ker J.unop.1.subschemeι
    (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact J.unop.2.2)

end ThickAffMain
p2m_reactivate "P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective.AlgebraicGeometry.ThickAffMain.NilpIdeal P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective.AlgebraicGeometry.ThickAffMain"

end AlgebraicGeometry
p2m_reactivate "P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective.AlgebraicGeometry.ThickAffMain.NilpIdeal P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective.AlgebraicGeometry.ThickAffMain P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective.AlgebraicGeometry"

theorem solution
    {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] [Surjective i] [IsAffine X₀] :
    IsAffine X :=
  AlgebraicGeometry.ThickAffMain.isAffine_of_isClosedImmersion_of_surjective i

end S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_surjective (solution)
