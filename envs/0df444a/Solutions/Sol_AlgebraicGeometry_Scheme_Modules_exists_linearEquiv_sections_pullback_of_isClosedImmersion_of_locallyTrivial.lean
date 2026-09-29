-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5ffd82eb-5c74-5c0b-a084-5fb67d02b754

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom IsAffineOpen.opensRange_fromSpec Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf moduleSpecΓFunctor IsAffineOpen.SpecMap_appLE_fromSpec IsAffineOpen.fromSpec_preimage_self Spec Spec.map Scheme IsAffineOpen.fromSpec_app_self IsOpenImmersion IsClosedImmersion Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE tilde IsAffineHom Scheme.Modules.map_smul Scheme.Hom.appLE Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.pushforwardSpecCompΓIso Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom mk Γ Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.comp_app Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.app_eq_appLE Modules.map_smul restrict Hom.appLE Modules.pullbackComp ΓSpecIso Modules.pushforwardSpecCompΓIso Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app pushforwardComp_hom_app_app Hom pushforward_map_app Hom.id_app Hom.app restrictAdjunction fromTildeΓ pullbackCongr pullbackPushforwardAdjunction restrict conjugateEquiv_pullbackComp_inv map_smul pullbackComp pushforwardSpecCompΓIso isIso_fromTildeGamma_of_locallyTrivial isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace SectionsCI
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules"

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U)

abbrev iU : Spec Γ(X, U) ⟶ X := hU.fromSpec

abbrev j : Spec Γ(Y, i ⁻¹ᵁ U) ⟶ Y := (hU.preimage i).fromSpec

theorem j_i' : j i U hU ≫ i = Spec.map (i.app U) ≫ iU U hU := by
  rw [Scheme.Hom.app_eq_appLE]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec i hU (hU.preimage i) le_rfl).symm

theorem j_i : j i U hU ≫ i = Spec.map (i.app U) ≫ iU U hU :=
  (Classical.choice (⟨⟨j_i' i U hU⟩⟩ : Nonempty (PLift (j i U hU ≫ i = Spec.map (i.app U) ≫ iU U hU)))).down

theorem le_opensRange_j : i ⁻¹ᵁ U ≤ (j i U hU).opensRange := by
  rw [IsAffineOpen.opensRange_fromSpec]

theorem top_le_preimage_j : (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ≤ (j i U hU) ⁻¹ᵁ (i ⁻¹ᵁ U) := by
  rw [IsAffineOpen.fromSpec_preimage_self]

theorem top_le_preimage_iU : (⊤ : (Spec Γ(X, U)).Opens) ≤ (iU U hU) ⁻¹ᵁ U := by
  rw [IsAffineOpen.fromSpec_preimage_self]

end AlgebraicGeometry.Scheme.Modules.SectionsCI

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom IsAffineOpen.opensRange_fromSpec Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf moduleSpecΓFunctor IsAffineOpen.SpecMap_appLE_fromSpec IsAffineOpen.fromSpec_preimage_self Spec Spec.map Scheme IsAffineOpen.fromSpec_app_self IsOpenImmersion IsClosedImmersion Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE tilde IsAffineHom Scheme.Modules.map_smul Scheme.Hom.appLE Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.pushforwardSpecCompΓIso Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom mk Γ Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.comp_app Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.app_eq_appLE Modules.map_smul restrict Hom.appLE Modules.pullbackComp ΓSpecIso Modules.pushforwardSpecCompΓIso Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app pushforwardComp_hom_app_app Hom pushforward_map_app Hom.id_app Hom.app restrictAdjunction fromTildeΓ pullbackCongr pullbackPushforwardAdjunction restrict conjugateEquiv_pullbackComp_inv map_smul pullbackComp pushforwardSpecCompΓIso isIso_fromTildeGamma_of_locallyTrivial isIso_baseChange_sections_of_isIso_fromTildeGamma"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace UnitCalculus

variable {X Y Z : Scheme.{u}}

theorem unit_app_comp (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    ((pullbackPushforwardAdjunction (g ≫ f)).unit.app M).app U ≫
        ((pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      ((pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((pullbackPushforwardAdjunction g).unit.app ((Scheme.Modules.pullback f).obj M)).app (f ⁻¹ᵁ U) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction g))
    (pullbackPushforwardAdjunction (g ≫ f)) (pullbackComp g f).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun t => Hom.app t U) h
  simp only [Hom.comp_app, Adjunction.comp_unit_app, pushforward_map_app, pushforwardComp_hom_app_app,
    Functor.comp_obj] at h'
  erw [Category.comp_id] at h'
  exact h'.symm

theorem unit_app_congr_res {p₁ p₂ : Z ⟶ X} (h : p₁ = p₂) (M : X.Modules) (U : X.Opens) (W : Z.Opens)
    (hW₁ : W ≤ p₁ ⁻¹ᵁ U) (hW₂ : W ≤ p₂ ⁻¹ᵁ U) :
    ((pullbackPushforwardAdjunction p₁).unit.app M).app U ≫ ((pullbackCongr h).hom.app M).app (p₁ ⁻¹ᵁ U) ≫
        ((Scheme.Modules.pullback p₂).obj M).presheaf.map (homOfLE hW₁).op =
      ((pullbackPushforwardAdjunction p₂).unit.app M).app U ≫
        ((Scheme.Modules.pullback p₂).obj M).presheaf.map (homOfLE hW₂).op := by
  subst h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Hom.id_app]
  erw [Category.id_comp]

theorem bijective_unit_app_of_isOpenImmersion (j : Y ⟶ X) [IsOpenImmersion j] (N : X.Modules)
    (V : X.Opens) (hV : V ≤ j.opensRange) :
    Function.Bijective (((pullbackPushforwardAdjunction j).unit.app N).app V) := by
  have hfac := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j) (pullbackPushforwardAdjunction j) N
  have hfac' := congrArg (fun t => Hom.app t V) hfac.symm

  have heq : j ''ᵁ j ⁻¹ᵁ V = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have h2 : (homOfLE (j.image_preimage_le V)).op = eqToHom (congrArg op heq.symm) := Subsingleton.elim _ _
  have hiso1 : IsIso (N.presheaf.map (homOfLE (j.image_preimage_le V)).op) := by
    rw [h2]
    exact ⟨N.presheaf.map (eqToHom (congrArg op heq)), by simp [eqToHom_map], by simp [eqToHom_map]⟩
  have hiso2 : IsIso ((((restrictAdjunction j).leftAdjointUniq (pullbackPushforwardAdjunction j)).hom.app N).app
      (j ⁻¹ᵁ V)) := inferInstance
  have hiso := @IsIso.comp_isIso _ _ _ _ _ _ _ hiso1 hiso2
  rw [← ConcreteCategory.isIso_iff_bijective]

  revert hiso
  refine fun hiso => ?_
  convert hiso using 2 <;>
    first | rfl | (apply heq_of_eq; rw [hfac']; rfl) | (apply heq_of_eq; erw [hfac']; rfl) | simp only [Functor.id_obj]

end UnitCalculus

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom IsAffineOpen.opensRange_fromSpec Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf moduleSpecΓFunctor IsAffineOpen.SpecMap_appLE_fromSpec IsAffineOpen.fromSpec_preimage_self Spec Spec.map Scheme IsAffineOpen.fromSpec_app_self IsOpenImmersion IsClosedImmersion Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE tilde IsAffineHom Scheme.Modules.map_smul Scheme.Hom.appLE Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.pushforwardSpecCompΓIso Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom mk Γ Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.comp_app Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.app_eq_appLE Modules.map_smul restrict Hom.appLE Modules.pullbackComp ΓSpecIso Modules.pushforwardSpecCompΓIso Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app pushforwardComp_hom_app_app Hom pushforward_map_app Hom.id_app Hom.app restrictAdjunction fromTildeΓ pullbackCongr pullbackPushforwardAdjunction restrict conjugateEquiv_pullbackComp_inv map_smul pullbackComp pushforwardSpecCompΓIso isIso_fromTildeGamma_of_locallyTrivial isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace SectionsCI
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules"

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)

abbrev M' : (Spec Γ(X, U)).Modules := (Scheme.Modules.pullback (iU U hU)).obj M

abbrev MY : Y.Modules := (Scheme.Modules.pullback i).obj M

def η : Γ(M, U) ⟶ Γ(MY i M, i ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction i).unit.app M).app U

def ρ : Γ(M, U) ⟶ Γ(M' U hU M, ⊤) :=
  ((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U ≫
    (M' U hU M).presheaf.map (homOfLE (top_le_preimage_iU U hU)).op

def θ : Γ(MY i M, i ⁻¹ᵁ U) ⟶
    Γ((Scheme.Modules.pullback (j i U hU)).obj (MY i M), ⊤) :=
  ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U) ≫
    ((Scheme.Modules.pullback (j i U hU)).obj (MY i M)).presheaf.map (homOfLE (top_le_preimage_j i U hU)).op

theorem isIso_presheaf_map_top_le {Y : Scheme.{u}} (N : Y.Modules) (V : Y.Opens) (h : (⊤ : Y.Opens) ≤ V) :
    IsIso (N.presheaf.map (homOfLE h).op) := by
  have hV : V = ⊤ := top_le_iff.mp h
  subst hV
  rw [Subsingleton.elim (homOfLE h) (𝟙 _), op_id, N.presheaf.map_id]
  infer_instance

theorem bijective_ρ : Function.Bijective (ρ U hU M) := by
  unfold ρ
  rw [← ConcreteCategory.isIso_iff_bijective]
  have h1 : IsIso (((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact UnitCalculus.bijective_unit_app_of_isOpenImmersion (iU U hU) M U (by rw [IsAffineOpen.opensRange_fromSpec])
  have h2 := isIso_presheaf_map_top_le (M' U hU M) _ (top_le_preimage_iU U hU)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

theorem bijective_θ : Function.Bijective (θ i U hU M) := by
  unfold θ
  rw [← ConcreteCategory.isIso_iff_bijective]
  have h1 : IsIso (((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact UnitCalculus.bijective_unit_app_of_isOpenImmersion (j i U hU) (MY i M) _ (le_opensRange_j i U hU)
  have h2 := isIso_presheaf_map_top_le ((Scheme.Modules.pullback (j i U hU)).obj (MY i M)) _
    (top_le_preimage_j i U hU)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

def σ : (Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M) ≅
    (Scheme.Modules.pullback (j i U hU)).obj (MY i M) :=
  (pullbackComp (Spec.map (i.app U)) (iU U hU)).app M ≪≫
    (pullbackCongr (j_i i U hU).symm).app M ≪≫
    ((pullbackComp (j i U hU) i).app M).symm

def ηφ : Γ(M' U hU M, ⊤) ⟶ Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), ⊤) :=
  ((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)).app ⊤

theorem app_res {Y : Scheme.{u}} {N₁ N₂ : Y.Modules} (ψ : N₁ ⟶ N₂) {V W : Y.Opens} (h : W ≤ V) (x : Γ(N₁, V)) :
    ψ.app W (N₁.presheaf.map (homOfLE h).op x) = N₂.presheaf.map (homOfLE h).op (ψ.app V x) := by
  have := ψ.mapPresheaf.naturality (homOfLE h).op
  exact ConcreteCategory.congr_hom this x

theorem hom_inv_app_apply {Y : Scheme.{u}} {N₁ N₂ : Y.Modules} (e : N₁ ≅ N₂) (V : Y.Opens) (x : Γ(N₂, V)) :
    e.hom.app V (e.inv.app V x) = x := by
  have h : (e.inv ≫ e.hom).app V = 𝟙 _ := by rw [e.inv_hom_id]; rfl
  have := ConcreteCategory.congr_hom h x
  exact this

theorem σ_hom_app (V : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens)
    (x : Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), V)) :
    (σ i U hU M).hom.app V x =
      ((pullbackComp (j i U hU) i).inv.app M).app V
        (((pullbackCongr (j_i i U hU).symm).hom.app M).app V
          (((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app V x)) := by
  rfl

theorem le1 : (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ≤ (Spec.map (i.app U)) ⁻¹ᵁ ((iU U hU) ⁻¹ᵁ U) :=
  fun _ _ => top_le_preimage_iU U hU (Set.mem_univ _)

theorem chase (m : Γ(M, U)) :
    ((σ i U hU M).hom.app ⊤) (ηφ i U hU M (ρ U hU M m)) = θ i U hU M (η i U M m) := by
  have le3 := top_le_preimage_j i U hU

  have e1 : ηφ i U hU M (ρ U hU M m)
      = ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M)).presheaf.map (homOfLE (le1 i U hU)).op
          (((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)).app ((iU U hU) ⁻¹ᵁ U)
            (((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m)) :=
    app_res ((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)) (top_le_preimage_iU U hU) _

  have hx2 : ((pullbackComp (Spec.map (i.app U)) (iU U hU)).inv.app M).app ((Spec.map (i.app U) ≫ iU U hU) ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction (Spec.map (i.app U) ≫ iU U hU)).unit.app M).app U m)
      = ((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)).app ((iU U hU) ⁻¹ᵁ U)
            (((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m) :=
    ConcreteCategory.congr_hom (UnitCalculus.unit_app_comp (Spec.map (i.app U)) (iU U hU) M U) m
  have e2 : ((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app ((Spec.map (i.app U)) ⁻¹ᵁ ((iU U hU) ⁻¹ᵁ U))
        (((pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)).app ((iU U hU) ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m))
      = ((pullbackPushforwardAdjunction (Spec.map (i.app U) ≫ iU U hU)).unit.app M).app U m :=
    (congrArg _ hx2.symm).trans (hom_inv_app_apply ((pullbackComp (Spec.map (i.app U)) (iU U hU)).app M) _ _)

  have e3 : ((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app ⊤ (ηφ i U hU M (ρ U hU M m))
      = ((Scheme.Modules.pullback (Spec.map (i.app U) ≫ iU U hU)).obj M).presheaf.map (homOfLE (le1 i U hU)).op
          (((pullbackPushforwardAdjunction (Spec.map (i.app U) ≫ iU U hU)).unit.app M).app U m) :=
    (congrArg _ e1).trans ((app_res ((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M) (le1 i U hU) _).trans
      (congrArg _ e2))

  have hx4 := ConcreteCategory.congr_hom
    (UnitCalculus.unit_app_congr_res (j_i i U hU).symm M U ⊤ (le1 i U hU) le3) m
  have e4 : ((pullbackCongr (j_i i U hU).symm).hom.app M).app ⊤
        (((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app ⊤ (ηφ i U hU M (ρ U hU M m)))
      = ((Scheme.Modules.pullback (j i U hU ≫ i)).obj M).presheaf.map (homOfLE le3).op
          (((pullbackPushforwardAdjunction (j i U hU ≫ i)).unit.app M).app U m) :=
    (congrArg _ e3).trans ((app_res ((pullbackCongr (j_i i U hU).symm).hom.app M) (le1 i U hU) _).trans hx4)

  have hx5 : ((pullbackComp (j i U hU) i).inv.app M).app ((j i U hU ≫ i) ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction (j i U hU ≫ i)).unit.app M).app U m)
      = ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction i).unit.app M).app U m) :=
    ConcreteCategory.congr_hom (UnitCalculus.unit_app_comp (j i U hU) i M U) m
  have e5 : ((pullbackComp (j i U hU) i).inv.app M).app ⊤
        (((pullbackCongr (j_i i U hU).symm).hom.app M).app ⊤
          (((pullbackComp (Spec.map (i.app U)) (iU U hU)).hom.app M).app ⊤ (ηφ i U hU M (ρ U hU M m))))
      = θ i U hU M (η i U M m) :=
    (congrArg _ e4).trans ((app_res ((pullbackComp (j i U hU) i).inv.app M) le3 _).trans
      (congrArg _ hx5))
  exact (σ_hom_app i U hU M ⊤ _).trans e5

end AlgebraicGeometry.Scheme.Modules.SectionsCI

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom IsAffineOpen.opensRange_fromSpec Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf moduleSpecΓFunctor IsAffineOpen.SpecMap_appLE_fromSpec IsAffineOpen.fromSpec_preimage_self Spec Spec.map Scheme IsAffineOpen.fromSpec_app_self IsOpenImmersion IsClosedImmersion Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE tilde IsAffineHom Scheme.Modules.map_smul Scheme.Hom.appLE Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.pushforwardSpecCompΓIso Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom mk Γ Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.comp_app Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.app_eq_appLE Modules.map_smul restrict Hom.appLE Modules.pullbackComp ΓSpecIso Modules.pushforwardSpecCompΓIso Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app pushforwardComp_hom_app_app Hom pushforward_map_app Hom.id_app Hom.app restrictAdjunction fromTildeΓ pullbackCongr pullbackPushforwardAdjunction restrict conjugateEquiv_pullbackComp_inv map_smul pullbackComp pushforwardSpecCompΓIso isIso_fromTildeGamma_of_locallyTrivial isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace SectionsCI
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules"

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)

scoped instance opensMapFinal' {Y Z : Scheme.{u}} (f : Y ⟶ Z) : (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

def pullbackUnitIso' {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Z.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf := by
  haveI h : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  exact @asIso _ _ _ _ _ h

theorem locallyTrivial_pullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) (L : Z.Modules)
    (htriv : ∀ z : Z, ∃ (V : Z.Opens), z ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj L ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    ∀ y : Y, ∃ (V : Y.Opens), y ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback f).obj L) ≅
        SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  intro y
  obtain ⟨V, hyV, ⟨eV⟩⟩ := htriv (f.base y)
  refine ⟨f ⁻¹ᵁ V, hyV, ⟨?_⟩⟩
  have hfact : (f ⁻¹ᵁ V).ι ≫ f = (f ∣_ V) ≫ V.ι := (morphismRestrict_ι f V).symm
  exact
    (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hfact).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ V)).mapIso eV ≪≫
    pullbackUnitIso' (f ∣_ V)

abbrev N' : ModuleCat Γ(X, U) := (moduleSpecΓFunctor (R := Γ(X, U))).obj (M' U hU M)

theorem N'_smul_def (b : Γ(X, U)) (n : N' U hU M) :
    b • n = (((Spec Γ(X, U)).presheaf.map (homOfLE (le_top : (⊤ : (Spec Γ(X, U)).Opens) ≤ ⊤)).op).hom
      ((StructureSheaf.globalSectionsIso Γ(X, U)).hom.hom b)) • (show Γ(M' U hU M, ⊤) from n) := rfl

omit hU M in
theorem res_top_top' (s : Γ(Spec Γ(X, U), ⊤)) :
    ((Spec Γ(X, U)).presheaf.map (homOfLE (le_top : (⊤ : (Spec Γ(X, U)).Opens) ≤ ⊤)).op).hom s = s := by
  rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec Γ(X, U)).Opens) ≤ ⊤)) (𝟙 _), op_id,
    CategoryTheory.Functor.map_id]
  rfl

theorem iU_appLE (b : Γ(X, U)) :
    ((Spec Γ(X, U)).presheaf.map (homOfLE (top_le_preimage_iU U hU)).op).hom (((iU U hU).app U).hom b)
      = (Scheme.ΓSpecIso Γ(X, U)).inv.hom b := by
  have h := IsAffineOpen.fromSpec_app_self hU

  have hb := congrArg (fun t => ((Spec Γ(X, U)).presheaf.map (homOfLE (top_le_preimage_iU U hU)).op).hom
    ((CommRingCat.Hom.hom t) b)) h
  simp only [CommRingCat.comp_apply] at hb
  refine hb.trans ?_
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  have : ((eqToHom (hU.fromSpec_preimage_self)).op ≫ (homOfLE (top_le_preimage_iU U hU)).op :
      op (⊤ : (Spec Γ(X, U)).Opens) ⟶ op ⊤) = 𝟙 _ := Subsingleton.elim _ _
  erw [this, CategoryTheory.Functor.map_id]
  rfl

theorem N'_smul_def' (b : Γ(X, U)) (n : N' U hU M) :
    b • n = ((Scheme.ΓSpecIso Γ(X, U)).inv.hom b) • (show Γ(M' U hU M, ⊤) from n) := by
  rw [N'_smul_def, res_top_top']
  rfl

theorem unit_iU_smul (b : Γ(X, U)) (m : Γ(M, U)) :
    ((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U (b • m)
      = ((iU U hU).app U).hom b •
        (show Γ(M' U hU M, (iU U hU) ⁻¹ᵁ U) from ((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m) :=
  Scheme.Modules.Hom.app_smul _ _ _

theorem ρ_smul (b : Γ(X, U)) (m : Γ(M, U)) :
    ρ U hU M (b • m) = (b • (show N' U hU M from ρ U hU M m) : N' U hU M) := by
  have h2 := congrArg ((M' U hU M).presheaf.map (homOfLE (top_le_preimage_iU U hU)).op) (unit_iU_smul U hU M b m)
  have h3 := Scheme.Modules.map_smul (M' U hU M) (homOfLE (top_le_preimage_iU U hU)) (((iU U hU).app U).hom b)
    (show Γ(M' U hU M, (iU U hU) ⁻¹ᵁ U) from ((pullbackPushforwardAdjunction (iU U hU)).unit.app M).app U m)
  rw [iU_appLE] at h3
  exact (h2.trans h3).trans (N'_smul_def' U hU M b _).symm

def ρlin : Γ(M, U) →ₗ[Γ(X, U)] N' U hU M where
  toFun m := ρ U hU M m
  map_add' x y := map_add _ x y
  map_smul' b m := ρ_smul U hU M b m

theorem ρlin_apply (m : Γ(M, U)) : ρlin U hU M m = ρ U hU M m := rfl

end AlgebraicGeometry.Scheme.Modules.SectionsCI
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom IsAffineOpen.opensRange_fromSpec Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf moduleSpecΓFunctor IsAffineOpen.SpecMap_appLE_fromSpec IsAffineOpen.fromSpec_preimage_self Spec Spec.map Scheme IsAffineOpen.fromSpec_app_self IsOpenImmersion IsClosedImmersion Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE tilde IsAffineHom Scheme.Modules.map_smul Scheme.Hom.appLE Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.pushforwardSpecCompΓIso Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom mk Γ Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.comp_app Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.app_eq_appLE Modules.map_smul restrict Hom.appLE Modules.pullbackComp ΓSpecIso Modules.pushforwardSpecCompΓIso Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app pushforwardComp_hom_app_app Hom pushforward_map_app Hom.id_app Hom.app restrictAdjunction fromTildeΓ pullbackCongr pullbackPushforwardAdjunction restrict conjugateEquiv_pullbackComp_inv map_smul pullbackComp pushforwardSpecCompΓIso isIso_fromTildeGamma_of_locallyTrivial isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace SectionsCI
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules"

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)

def ρR : Γ(M, U) ≃ₗ[Γ(X, U)] N' U hU M :=
  { (ρlin U hU M : Γ(M, U) →ₗ[Γ(X, U)] N' U hU M) with
    invFun := (Equiv.ofBijective _ (bijective_ρ U hU M)).invFun
    left_inv := (Equiv.ofBijective _ (bijective_ρ U hU M)).left_inv
    right_inv := (Equiv.ofBijective _ (bijective_ρ U hU M)).right_inv }

theorem ρR_apply (m : Γ(M, U)) : ρR U hU M m = ρ U hU M m := rfl

abbrev T₁ : Type u := ((ModuleCat.extendScalars (i.app U).hom).obj (N' U hU M) : Type u)

abbrev S₁ : ModuleCat Γ(X, U) :=
  (ModuleCat.restrictScalars (i.app U).hom).obj (ModuleCat.of Γ(Y, i ⁻¹ᵁ U) Γ(Y, i ⁻¹ᵁ U))

def Kfwd : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) →+ T₁ i U hU M :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  TensorProduct.liftAddHom
    { toFun := fun a =>
        (TensorProduct.mk Γ(X, U) (S₁ i U) (N' U hU M) (a : S₁ i U)).toAddMonoidHom.comp
          (ρlin U hU M).toAddMonoidHom
      map_zero' := by
        apply AddMonoidHom.ext; intro m
        change ((((0 : Γ(Y, i ⁻¹ᵁ U)) : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m)) : T₁ i U hU M) = 0
        exact TensorProduct.zero_tmul _ _
      map_add' := fun a a' => by
        apply AddMonoidHom.ext; intro m
        change ((((a + a' : Γ(Y, i ⁻¹ᵁ U)) : S₁ i U)) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M)
          = ((a : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M)
            + ((a' : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M)
        exact TensorProduct.add_tmul _ _ _ }
    (fun b a m => by
      change (((b • a : Γ(Y, i ⁻¹ᵁ U)) : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M)
        = ((a : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M (b • m)) : T₁ i U hU M)
      rw [LinearMap.map_smul, ← TensorProduct.smul_tmul]
      try rfl
      try congr 1)

theorem Kfwd_tmul (a : Γ(Y, i ⁻¹ᵁ U)) (m : Γ(M, U)) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Kfwd i U hU M (a ⊗ₜ[Γ(X, U)] m)
      = ((a : S₁ i U) ⊗ₜ[Γ(X, U)] (ρlin U hU M m) : T₁ i U hU M) := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  exact TensorProduct.liftAddHom_tmul _ _ a m

def Kbwd₀ : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Γ(Y, i ⁻¹ᵁ U) →+ (N' U hU M →+ Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U)) :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  { toFun := fun a =>
      (TensorProduct.mk Γ(X, U) Γ(Y, i ⁻¹ᵁ U) Γ(M, U) a).toAddMonoidHom.comp
        ((ρR U hU M).symm : N' U hU M →ₗ[Γ(X, U)] Γ(M, U)).toAddMonoidHom
    map_zero' := by apply AddMonoidHom.ext; intro n; exact TensorProduct.zero_tmul _ _
    map_add' := fun a a' => by apply AddMonoidHom.ext; intro n; exact TensorProduct.add_tmul _ _ _ }

theorem Kbwd₀_apply (a : Γ(Y, i ⁻¹ᵁ U)) (n : N' U hU M) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Kbwd₀ i U hU M a n = a ⊗ₜ[Γ(X, U)] (ρR U hU M).symm n := rfl

def Kbwd : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    T₁ i U hU M →+ Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  TensorProduct.liftAddHom
    (show S₁ i U →+ (N' U hU M →+ Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U)) from Kbwd₀ i U hU M)
    (fun b a n => by
      change Kbwd₀ i U hU M (b • a) n = Kbwd₀ i U hU M a (b • n)
      rw [Kbwd₀_apply, Kbwd₀_apply, LinearEquiv.map_smul, ← TensorProduct.smul_tmul]
      try rfl
      try congr 1)

theorem Kbwd_tmul (a : Γ(Y, i ⁻¹ᵁ U)) (n : N' U hU M) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Kbwd i U hU M ((a : S₁ i U) ⊗ₜ[Γ(X, U)] n : T₁ i U hU M) = Kbwd₀ i U hU M a n := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  exact TensorProduct.liftAddHom_tmul _ _ a n

def κ : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃+ T₁ i U hU M :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  { Kfwd i U hU M with
    invFun := Kbwd i U hU M
    left_inv := fun z => by
      change Kbwd i U hU M (Kfwd i U hU M z) = z
      induction z using TensorProduct.induction_on with
      | zero =>
        exact (congrArg (Kbwd i U hU M) (map_zero (Kfwd i U hU M))).trans (map_zero (Kbwd i U hU M))
      | add x y hx hy =>
        exact (congrArg (Kbwd i U hU M) (map_add (Kfwd i U hU M) x y)).trans
          ((map_add (Kbwd i U hU M) _ _).trans (congrArg₂ (· + ·) hx hy))
      | tmul a m =>
        rw [Kfwd_tmul]
        refine (Kbwd_tmul i U hU M _ _).trans ?_
        rw [Kbwd₀_apply]
        congr 1
        exact (ρR U hU M).symm_apply_apply m
    right_inv := fun t => by
      change Kfwd i U hU M (Kbwd i U hU M t) = t
      induction t using TensorProduct.induction_on with
      | zero =>
        exact (congrArg (Kfwd i U hU M) (map_zero (Kbwd i U hU M))).trans (map_zero (Kfwd i U hU M))
      | add x y hx hy =>
        exact (congrArg (Kfwd i U hU M) (map_add (Kbwd i U hU M) x y)).trans
          ((map_add (Kfwd i U hU M) _ _).trans (congrArg₂ (· + ·) hx hy))
      | tmul a n =>
        refine (congrArg (Kfwd i U hU M) (Kbwd_tmul i U hU M a n)).trans ?_
        refine (congrArg (Kfwd i U hU M) (Kbwd₀_apply i U hU M a n)).trans ?_
        refine (Kfwd_tmul i U hU M a ((ρR U hU M).symm n)).trans ?_
        congr 1
        exact (ρR U hU M).apply_symm_apply n }

theorem κ_tmul (a : Γ(Y, i ⁻¹ᵁ U)) (m : Γ(M, U)) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    κ i U hU M (a ⊗ₜ[Γ(X, U)] m) = ((a : S₁ i U) ⊗ₜ[Γ(X, U)] ρ U hU M m : T₁ i U hU M) :=
  Kfwd_tmul i U hU M a m

end AlgebraicGeometry.Scheme.Modules.SectionsCI
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom IsAffineOpen.opensRange_fromSpec Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf moduleSpecΓFunctor IsAffineOpen.SpecMap_appLE_fromSpec IsAffineOpen.fromSpec_preimage_self Spec Spec.map Scheme IsAffineOpen.fromSpec_app_self IsOpenImmersion IsClosedImmersion Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction StructureSheaf.globalSectionsIso IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE tilde IsAffineHom Scheme.Modules.map_smul Scheme.Hom.appLE Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.pushforwardSpecCompΓIso Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul ringCatSheaf Modules.pullback Hom.id_app Hom mk Γ Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Hom.comp_app Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.app_eq_appLE Modules.map_smul restrict Hom.appLE Modules.pullbackComp ΓSpecIso Modules.pushforwardSpecCompΓIso Modules.isIso_fromTildeGamma_of_locallyTrivial Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pullback presheaf Hom.comp_app pushforwardComp_hom_app_app Hom pushforward_map_app Hom.id_app Hom.app restrictAdjunction fromTildeΓ pullbackCongr pullbackPushforwardAdjunction restrict conjugateEquiv_pullbackComp_inv map_smul pullbackComp pushforwardSpecCompΓIso isIso_fromTildeGamma_of_locallyTrivial isIso_baseChange_sections_of_isIso_fromTildeGamma"
namespace SectionsCI
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules"

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsAffineHom i]
variable (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules)

abbrev Q : ModuleCat (Γ(Y, i ⁻¹ᵁ U)) :=
  (moduleSpecΓFunctor (R := Γ(Y, i ⁻¹ᵁ U))).obj ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M))

def β : (ModuleCat.extendScalars (i.app U).hom).obj (N' U hU M) ⟶ Q i U hU M :=
  ((ModuleCat.extendRestrictScalarsAdj (i.app U).hom).homEquiv (N' U hU M) (Q i U hU M)).symm
    ((moduleSpecΓFunctor (R := Γ(X, U))).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app (M' U hU M)) ≫
      (Scheme.Modules.pushforwardSpecCompΓIso (i.app U)).hom.app
        ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M)))

theorem β_tmul (x : Γ(Y, i ⁻¹ᵁ U)) (n : N' U hU M) :
    (β i U hU M).hom ((x : S₁ i U) ⊗ₜ[Γ(X, U)] n : T₁ i U hU M) = x • (show Q i U hU M from ηφ i U hU M n) := by
  unfold β
  rw [Adjunction.homEquiv_counit]
  rfl

theorem Q_smul_def (x : Γ(Y, i ⁻¹ᵁ U)) (q : Q i U hU M) :
    x • q = ((Scheme.ΓSpecIso (Γ(Y, i ⁻¹ᵁ U))).inv.hom x) •
      (show Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), ⊤) from q) := by
  have h1 : x • q = (((Spec Γ(Y, i ⁻¹ᵁ U)).presheaf.map (homOfLE (le_top : (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ≤ ⊤)).op).hom
      ((StructureSheaf.globalSectionsIso (Γ(Y, i ⁻¹ᵁ U))).hom.hom x)) •
      (show Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), ⊤) from q) := rfl
  rw [h1]
  congr 1
  all_goals try (rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ≤ ⊤)) (𝟙 _), op_id,
    CategoryTheory.Functor.map_id]; rfl)

theorem σ_smul (t : Γ(Spec Γ(Y, i ⁻¹ᵁ U), ⊤)) (q : Γ((Scheme.Modules.pullback (Spec.map (i.app U))).obj (M' U hU M), ⊤)) :
    (σ i U hU M).hom.app ⊤ (t • q) = t • (σ i U hU M).hom.app ⊤ q :=
  Scheme.Modules.Hom.app_smul _ _ _

theorem θ_smul (s : Γ(Y, i ⁻¹ᵁ U)) (y : Γ(MY i M, i ⁻¹ᵁ U)) :
    θ i U hU M (s • y) =
      ((j i U hU).appLE (i ⁻¹ᵁ U) ⊤ (top_le_preimage_j i U hU)).hom s • θ i U hU M y := by
  have h1 : ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U) (s • y)
      = ((j i U hU).app (i ⁻¹ᵁ U)).hom s •
        (show Γ((Scheme.Modules.pullback (j i U hU)).obj (MY i M), (j i U hU) ⁻¹ᵁ (i ⁻¹ᵁ U)) from
          ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U) y) :=
    Scheme.Modules.Hom.app_smul _ _ _
  have h2 := congrArg (((Scheme.Modules.pullback (j i U hU)).obj (MY i M)).presheaf.map
    (homOfLE (top_le_preimage_j i U hU)).op) h1
  have h3 := Scheme.Modules.map_smul ((Scheme.Modules.pullback (j i U hU)).obj (MY i M))
    (homOfLE (top_le_preimage_j i U hU)) (((j i U hU).app (i ⁻¹ᵁ U)).hom s)
    (show Γ((Scheme.Modules.pullback (j i U hU)).obj (MY i M), (j i U hU) ⁻¹ᵁ (i ⁻¹ᵁ U)) from
      ((pullbackPushforwardAdjunction (j i U hU)).unit.app (MY i M)).app (i ⁻¹ᵁ U) y)
  exact h2.trans h3

theorem scalar_key (a : Γ(Y, i ⁻¹ᵁ U)) :
    ((j i U hU).appLE (i ⁻¹ᵁ U) ⊤ (top_le_preimage_j i U hU)).hom a
      = (Scheme.ΓSpecIso Γ(Y, i ⁻¹ᵁ U)).inv.hom a := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  have h := IsAffineOpen.fromSpec_app_self (hU.preimage i)
  have hb := congrArg (fun t => ((Spec Γ(Y, i ⁻¹ᵁ U)).presheaf.map (homOfLE (top_le_preimage_j i U hU)).op).hom
    ((CommRingCat.Hom.hom t) a)) h
  simp only [CommRingCat.comp_apply] at hb
  refine hb.trans ?_
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  have : ((eqToHom ((hU.preimage i).fromSpec_preimage_self)).op ≫ (homOfLE (top_le_preimage_j i U hU)).op :
      op (⊤ : (Spec Γ(Y, i ⁻¹ᵁ U)).Opens) ⟶ op ⊤) = 𝟙 _ := Subsingleton.elim _ _
  erw [this, CategoryTheory.Functor.map_id]
  rfl

abbrev P : Type u := (Γ(MY i M, i ⁻¹ᵁ U) : Type u)

abbrev instRP : Module Γ(X, U) (P i U M) := Module.compHom (P i U M) (i.app U).hom

theorem isScalarTower_RSP : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    letI := instRP i U M; IsScalarTower Γ(X, U) Γ(Y, i ⁻¹ᵁ U) (P i U M) :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  letI := instRP i U M
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem unit_smul (b : Γ(X, U)) (m : Γ(M, U)) :
    ((pullbackPushforwardAdjunction i).unit.app M).app U (b • m)
      = (i.app U).hom b • (show P i U M from ((pullbackPushforwardAdjunction i).unit.app M).app U m) :=
  Scheme.Modules.Hom.app_smul _ _ _

def ηR : letI := instRP i U M
    Γ(M, U) →ₗ[Γ(X, U)] P i U M :=
  letI := instRP i U M
  { toFun := fun m => η i U M m
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r m => by
      show η i U M (r • m) = ((i.app U).hom r) • η i U M m
      exact unit_smul i U M r m }

theorem ηR_apply (m : Γ(M, U)) : letI := instRP i U M
    ηR i U M m = η i U M m := rfl

def e₀ : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(Y, i ⁻¹ᵁ U)] P i U M :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  letI := instRP i U M
  haveI := isScalarTower_RSP i U M
  LinearMap.liftBaseChange Γ(Y, i ⁻¹ᵁ U) (ηR i U M)

theorem e₀_tmul (a : Γ(Y, i ⁻¹ᵁ U)) (m : Γ(M, U)) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    e₀ i U M (a ⊗ₜ[Γ(X, U)] m) = a • η i U M m :=
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  letI := instRP i U M
  haveI := isScalarTower_RSP i U M
  LinearMap.liftBaseChange_tmul Γ(Y, i ⁻¹ᵁ U) (ηR i U M) a m

theorem θ_e₀ (z : letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
      Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U)) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    θ i U hU M (e₀ i U M z) = (σ i U hU M).hom.app ⊤ ((β i U hU M).hom (κ i U hU M z)) := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    first | rfl | exact (map_zero _).symm
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    first | rfl | exact (map_add _ _ _).symm
  | tmul a m =>
    rw [e₀_tmul, κ_tmul, β_tmul, Q_smul_def, σ_smul, chase, θ_smul, scalar_key]

include hU in

theorem bijective_e₀
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hB2c : ∀ (N : (Spec Γ(X, U)).Modules),
      (∀ y : Spec Γ(X, U), ∃ (V : (Spec Γ(X, U)).Opens), y ∈ V ∧
        Nonempty ((Scheme.Modules.pullback V.ι).obj N ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) →
      IsIso N.fromTildeΓ)
    (hC1 : ∀ (N : (Spec Γ(X, U)).Modules), IsIso N.fromTildeΓ →
      IsIso (((ModuleCat.extendRestrictScalarsAdj (i.app U).hom).homEquiv
        ((moduleSpecΓFunctor (R := Γ(X, U))).obj N)
        ((moduleSpecΓFunctor (R := Γ(Y, i ⁻¹ᵁ U))).obj ((Scheme.Modules.pullback (Spec.map (i.app U))).obj N))).symm
      ((moduleSpecΓFunctor (R := Γ(X, U))).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app N) ≫
        (Scheme.Modules.pushforwardSpecCompΓIso (i.app U)).hom.app
          ((Scheme.Modules.pullback (Spec.map (i.app U))).obj N)))) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    Function.Bijective (e₀ i U M) := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  have hM' : IsIso (M' U hU M).fromTildeΓ := hB2c _ (locallyTrivial_pullback (iU U hU) M htriv)
  have hβ : IsIso (β i U hU M) := hC1 _ hM'
  have bβ : Function.Bijective (β i U hU M).hom := by
    have := ConcreteCategory.bijective_of_isIso (β i U hU M); exact this
  have bσ : Function.Bijective ((σ i U hU M).hom.app ⊤) := by
    rw [← ConcreteCategory.isIso_iff_bijective]; infer_instance
  have bθ := bijective_θ i U hU M
  have bκ : Function.Bijective (κ i U hU M) := (κ i U hU M).bijective
  have hcomp : Function.Bijective (fun z => θ i U hU M (e₀ i U M z)) := by
    have heq : (fun z => θ i U hU M (e₀ i U M z))
        = (fun z => (σ i U hU M).hom.app ⊤ ((β i U hU M).hom (κ i U hU M z))) := funext (θ_e₀ i U hU M)
    rw [heq]
    exact bσ.comp (bβ.comp bκ)
  constructor
  · exact Function.Injective.of_comp hcomp.1
  · intro p
    obtain ⟨z, hz⟩ := hcomp.2 (θ i U hU M p)
    exact ⟨z, bθ.1 hz⟩

include hU in
theorem main
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hB2c : ∀ (N : (Spec Γ(X, U)).Modules),
      (∀ y : Spec Γ(X, U), ∃ (V : (Spec Γ(X, U)).Opens), y ∈ V ∧
        Nonempty ((Scheme.Modules.pullback V.ι).obj N ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) →
      IsIso N.fromTildeΓ)
    (hC1 : ∀ (N : (Spec Γ(X, U)).Modules), IsIso N.fromTildeΓ →
      IsIso (((ModuleCat.extendRestrictScalarsAdj (i.app U).hom).homEquiv
        ((moduleSpecΓFunctor (R := Γ(X, U))).obj N)
        ((moduleSpecΓFunctor (R := Γ(Y, i ⁻¹ᵁ U))).obj ((Scheme.Modules.pullback (Spec.map (i.app U))).obj N))).symm
      ((moduleSpecΓFunctor (R := Γ(X, U))).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (i.app U))).unit.app N) ≫
        (Scheme.Modules.pushforwardSpecCompΓIso (i.app U)).hom.app
          ((Scheme.Modules.pullback (Spec.map (i.app U))).obj N)))) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    ∃ e : Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(Y, i ⁻¹ᵁ U)] Γ((Scheme.Modules.pullback i).obj M, i ⁻¹ᵁ U),
      ∀ m : Γ(M, U), e (1 ⊗ₜ m) = (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U).hom m := by
  letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  refine ⟨LinearEquiv.ofBijective (e₀ i U M) (bijective_e₀ i U hU M htriv hB2c hC1), fun m => ?_⟩
  rw [LinearEquiv.ofBijective_apply, e₀_tmul, one_smul]
  rfl

end AlgebraicGeometry.Scheme.Modules.SectionsCI
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry in

theorem solution
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (M : X.Modules)
    (htriv : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    ∃ e : Γ(Y, i ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(Y, i ⁻¹ᵁ U)] Γ((Scheme.Modules.pullback i).obj M, i ⁻¹ᵁ U),
      ∀ m : Γ(M, U), e (1 ⊗ₜ m) = (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U).hom m :=
  AlgebraicGeometry.Scheme.Modules.SectionsCI.main i U hU M htriv
    (fun N h => AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial N h)
    (fun N h => AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma (i.app U) N h)

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SectionsCI"

end S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_pullback_of_isClosedImmersion_of_locallyTrivial (solution)
