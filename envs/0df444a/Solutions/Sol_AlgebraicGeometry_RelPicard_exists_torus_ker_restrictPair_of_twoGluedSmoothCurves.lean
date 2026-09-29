-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_torus_ker_restrictPair_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0ff2410e-0da5-5ee5-b0f8-09275261bbae

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_TwoGluedCurvesNodeUnitModule
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_exists_rationalPoint_enumeration_of_natCard_pullback_eq
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_isNodeUnitModule_one_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isInvertible_isNodeUnitModule
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_pullback_baseChangeSnd
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_tensor
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_smul_units
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_exists_isNodeUnitModule_of_pullback_curveChange_iso_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_exists_eq_mul_of_iso
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_nonempty_pullback_curveChange_iso_unit
import Theorems.Thm_AlgebraicGeometry_TwoGluedCurves_IsNodeUnitModule_fibrewiseAlgEquivZero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_pullback_pullback_of_rigidify_iso_unit
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_one_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_ker_restrictPair_of_twoGluedSmoothCurves
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"
set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_ker_restrictPair_of_twoGluedSmoothCurves.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_ker_restrictPair_of_twoGluedSmoothCurves.AlgebraicGeometry.RelPicard AlgebraicGeometry.SplitTorus"

p2m_open "AlgebraicGeometry.TwoGluedCurves CategoryTheory.MonoidalCategory"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.toSpecΓ_appTop Scheme.Hom.comp_appTop Spec.map_injective IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Spec.map_id toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso toSpecΓ Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso exists_rationalPoint_enumeration_of_natCard_pullback_eq Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw curveChange rigSection_curveChange RigidifiedLineBundle.pullbackAlongPullbackAlongIso' RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_pullbackAlong_one_iso"
namespace TorusPtAssembly
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k]

noncomputable def coordUnit (k : Type u) [Field k] (n : ℕ) (j : Fin n) : (torusCoord k n)ˣ :=
  (AddMonoidAlgebra.of k (Fin n → ℤ)).toHomUnits (Multiplicative.ofAdd (Pi.single j 1))

noncomputable def univUnits (s : ℕ) : Fin s → Γ(torusScheme k (s - 1), ⊤)ˣ := fun j =>
  if h : j.1 = 0 then 1 else
    Units.map (Scheme.ΓSpecIso (CommRingCat.of (torusCoord k (s - 1)))).inv.hom.toMonoidHom
      (coordUnit k (s - 1) ⟨j.1 - 1, by omega⟩)

end AlgebraicGeometry.RelPicard.TorusPtAssembly

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.toSpecΓ_appTop Scheme.Hom.comp_appTop Spec.map_injective IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Spec.map_id toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso toSpecΓ Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso exists_rationalPoint_enumeration_of_natCard_pullback_eq Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw curveChange rigSection_curveChange RigidifiedLineBundle.pullbackAlongPullbackAlongIso' RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_pullbackAlong_one_iso"
namespace TorusPtAssembly
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k]

def pullbackAlongCompIso {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}
    {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    {t'' : T'' ⟶ Spec (CommRingCat.of k)}
    (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) (φ : SchemeHomOver t'' t') :
    (M.pullbackAlong (NeronModelInfra.schemeHomOverComp φ ψ)).L ≅ ((M.pullbackAlong ψ).pullbackAlong φ).L :=
  (RigidifiedLineBundle.pullbackAlongPullbackAlongIso' M ψ φ).symm

section restrict

variable {X C₁ : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of k)} {c₁ : C₁ ⟶ Spec (CommRingCat.of k)}
  (i₁ : SchemeHomOver c₁ x)
  {ε : SchemeHomOver (𝟙 _) x} {ε₁ : SchemeHomOver (𝟙 _) c₁} (hε : ε₁.1 ≫ i₁.1 = ε.1)
  {D : RelativePic0Designation k x} (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
  {D₁ : RelativePic0Designation k c₁} (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)

theorem classify_poincare_pullbackAlong {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : SchemeHomOver t D.toBase) :
    hD.classify t (hD.poincare.pullbackAlong a)
      ((algEquivZeroCut x ε).pullback_mem _ _ a _ hD.poincare_mem) = a :=
  (hD.classify_unique t _ _ a ⟨Iso.refl _⟩).symm

include hε in

theorem nonempty_poincare_pullbackAlong_comp_pullbackHom_iso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : SchemeHomOver t D.toBase) :
    Nonempty ((hD₁.poincare.pullbackAlong
        (NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁))).L ≅
      (Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj (hD.poincare.pullbackAlong a).L) := by
  have h1 : NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁) =
      postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
        (hD.classify t (hD.poincare.pullbackAlong a)
          ((algEquivZeroCut x ε).pullback_mem _ _ a _ hD.poincare_mem)) := by
    rw [classify_poincare_pullbackAlong]; rfl
  rw [h1, RepresentsRelSubPic.postComp_pullbackHom_classify]
  exact hD₁.classify_spec t _ _

include hε in

theorem comp_pullbackHom_eq_one_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (a : SchemeHomOver t D.toBase) :
    NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ↔
      Nonempty ((Scheme.Modules.pullback (curveChange i₁.1 i₁.2 t)).obj (hD.poincare.pullbackAlong a).L ≅
        SheafOfModules.unit (pullback c₁ t).ringCatSheaf) := by
  obtain ⟨e⟩ := nonempty_poincare_pullbackAlong_comp_pullbackHom_iso i₁ hε hD hD₁ t a
  obtain ⟨e1⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_one_iso (P := algEquivZeroGroupCut c₁ ε₁) hD₁ t
  constructor
  · intro h
    rw [h] at e
    exact ⟨e.symm ≪≫ e1⟩
  · rintro ⟨f⟩
    exact hD₁.ext_of_iso t _ _ ⟨e ≪≫ f ≪≫ e1.symm⟩

end restrict

section restrict₂

variable {X C₂ : Scheme.{u}} {x : X ⟶ Spec (CommRingCat.of k)} {c₂ : C₂ ⟶ Spec (CommRingCat.of k)}
  (i₂ : SchemeHomOver c₂ x)
  {ε : SchemeHomOver (𝟙 _) x} {ε₂ : SchemeHomOver (𝟙 _) c₂}
  {D : RelativePic0Designation k x} (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
  {D₂ : RelativePic0Designation k c₂} (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
  (ν₂ : SchemeHomOver D.toBase D₂.toBase)
  (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
      Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
        Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
          ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))

include hν₂ in

theorem comp_ν₂_eq_one_iff {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase) :
    NeronModelInfra.schemeHomOverComp a ν₂ =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t ↔
      Nonempty (Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
          ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L) ≅
        SheafOfModules.unit (pullback c₂ t).ringCatSheaf) := by
  obtain ⟨e⟩ := hν₂ t a
  obtain ⟨e1⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_one_iso (P := algEquivZeroGroupCut c₂ ε₂) hD₂ t
  constructor
  · intro h
    rw [h] at e
    exact ⟨e.symm ≪≫ e1⟩
  · rintro ⟨f⟩
    exact hD₂.ext_of_iso t _ _ ⟨e ≪≫ f ≪≫ e1.symm⟩

end restrict₂

end AlgebraicGeometry.RelPicard.TorusPtAssembly

end

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.toSpecΓ_appTop Scheme.Hom.comp_appTop Spec.map_injective IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Spec.map_id toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso toSpecΓ Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso exists_rationalPoint_enumeration_of_natCard_pullback_eq Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw curveChange rigSection_curveChange RigidifiedLineBundle.pullbackAlongPullbackAlongIso' RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_pullbackAlong_one_iso"
namespace TorusPtAssembly
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k]

theorem isIntegral_of_geometricallyIntegral {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [GeometricallyIntegral c] : IsIntegral C :=
  haveI : IsIntegral (pullback c (𝟙 (Spec (CommRingCat.of k)))) :=
    GeometricallyIntegral.geometrically_isIntegral (f := c) (𝟙 _) (pullback.fst c (𝟙 _)) (pullback.snd c (𝟙 _))
      (IsPullback.of_hasPullback c (𝟙 _))
  IsIntegral.of_isIso (pullback.fst c (𝟙 (Spec (CommRingCat.of k))))

theorem appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  have := Scheme.ΓSpecIso_inv_naturality φ
  exact (congrArg (fun f => f.hom r) this).symm

theorem exists_eq_torusPtId (n : ℕ) (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (torusStr k n)) :
    ∃ χ : torusCoord k n →ₐ[k] k, y = torusPtId k n χ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective y.1
  have hcomp : (CommRingCat.ofHom (algebraMap k (torusCoord k n))) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_id]
    exact y.2
  refine ⟨{ φ.hom with commutes' := fun r => ?_ }, ?_⟩
  · exact congrArg (fun f => f.hom r) hcomp
  · apply Subtype.ext
    show y.1 = Spec.map _
    rw [← hφ]
    rfl

theorem algHom_ext_coordUnit (n : ℕ) {A : Type u} [CommRing A] [Algebra k A] (χ χ' : torusCoord k n →ₐ[k] A)
    (h : ∀ j : Fin n, χ (coordUnit k n j : torusCoord k n) = χ' (coordUnit k n j : torusCoord k n)) : χ = χ' := by

  let m : Multiplicative (Fin n → ℤ) →* A := (χ : torusCoord k n →* A).comp (AddMonoidAlgebra.of k (Fin n → ℤ))
  let m' : Multiplicative (Fin n → ℤ) →* A := (χ' : torusCoord k n →* A).comp (AddMonoidAlgebra.of k (Fin n → ℤ))
  have hmm : m = m' := by
    have : MonoidHom.toAdditiveRight m = MonoidHom.toAdditiveRight m' := by
      refine AddMonoidHom.functions_ext _ _ _ fun j x => ?_
      have hx : ∀ (g : (Fin n → ℤ) →+ Additive A), g (Pi.single j x) =
          (g.comp (AddMonoidHom.single (fun _ : Fin n => ℤ) j)) x := fun g => rfl
      rw [hx, hx]
      congr 1
      refine AddMonoidHom.ext_int ?_
      show m (Multiplicative.ofAdd (Pi.single j 1)) = m' (Multiplicative.ofAdd (Pi.single j 1))
      exact h j
    exact MonoidHom.toAdditiveRight.injective this
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  have := congrArg (fun f => f (Multiplicative.ofAdd v)) hmm
  simpa [m, m', AddMonoidAlgebra.of_apply] using this

theorem torusPt_ext (n : ℕ) (y y' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (torusStr k n))
    (h : ∀ j : Fin n,
      y.1.appTop ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv ((coordUnit k n j : (torusCoord k n)ˣ) : torusCoord k n)) =
        y'.1.appTop ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv ((coordUnit k n j : (torusCoord k n)ˣ) : torusCoord k n))) :
    y = y' := by
  obtain ⟨χ, rfl⟩ := exists_eq_torusPtId n y
  obtain ⟨χ', rfl⟩ := exists_eq_torusPtId n y'
  have hχ : χ = χ' := by
    refine algHom_ext_coordUnit n χ χ' fun j => ?_
    have := h j
    change (Spec.map (CommRingCat.ofHom χ.toRingHom)).appTop _ =
      (Spec.map (CommRingCat.ofHom χ'.toRingHom)).appTop _ at this
    rw [appTop_ΓSpecIso_inv, appTop_ΓSpecIso_inv] at this
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective this
  rw [hχ]

end AlgebraicGeometry.RelPicard.TorusPtAssembly

end

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Spec IsIntegral Spec.map Scheme.toSpecΓ_naturality Scheme.ΓSpecIso_inv_naturality Scheme Spec.map_surjective Scheme.toSpecΓ_appTop Scheme.Hom.comp_appTop Spec.map_injective IsClosedImmersion IsReduced Scheme.Modules.pullbackCongr Spec.map_id toSpecΓ_SpecMap_ΓSpecIso_inv Scheme.Modules.pullbackId Scheme.Modules IsIntegral.of_isIso toSpecΓ Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso exists_rationalPoint_enumeration_of_natCard_pullback_eq Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection postComp RigidifiedLineBundle RigidifiedLineBundle.unit RepresentsRelSubPic FibrewiseAlgEquivZero algEquivZeroCut algEquivZeroGroupCut RepresentsRelSubPic.relativeGroupLaw curveChange rigSection_curveChange RigidifiedLineBundle.pullbackAlongPullbackAlongIso' RepresentsRelSubPic.pullbackHom RepresentsRelSubPic.postComp_pullbackHom_classify rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso RepresentsRelSubPic.nonempty_pullbackAlong_one_iso"
namespace TorusPtAssembly
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {k : Type u} [Field k]

def unitsMonoidHom {n : ℕ} {M : Type*} [CommGroup M] (v : Fin n → M) : Multiplicative (Fin n → ℤ) →* M where
  toFun w := ∏ j, v j ^ (Multiplicative.toAdd w j)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem unitsMonoidHom_single {n : ℕ} {M : Type*} [CommGroup M] (v : Fin n → M) (j : Fin n) :
    unitsMonoidHom v (Multiplicative.ofAdd (Pi.single j 1)) = v j := by
  classical
  simp only [unitsMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

theorem exists_torusPt_of_units (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (v : Fin n → Γ(T, ⊤)ˣ) :
    ∃ y : SchemeHomOver t (torusStr k n), ∀ j : Fin n,
      y.1.appTop ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv
        ((coordUnit k n j : (torusCoord k n)ˣ) : torusCoord k n)) = (v j : Γ(T, ⊤)) := by
  classical
  letI : Algebra k Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop).hom.toAlgebra
  have halg : algebraMap k Γ(T, ⊤) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ t.appTop).hom := rfl
  let m : Multiplicative (Fin n → ℤ) →* Γ(T, ⊤) := (Units.coeHom _).comp (unitsMonoidHom v)
  let φ : torusCoord k n →ₐ[k] Γ(T, ⊤) := AddMonoidAlgebra.lift k Γ(T, ⊤) (Fin n → ℤ) m
  refine ⟨⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩, fun j => ?_⟩
  · change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (torusCoord k n))) = t
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : φ.toRingHom.comp (algebraMap k (torusCoord k n)) = algebraMap k Γ(T, ⊤) := φ.comp_algebraMap
    rw [this, halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  · change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop _ = _
    rw [Scheme.Hom.comp_appTop]
    change T.toSpecΓ.appTop ((Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop _) = _
    rw [appTop_ΓSpecIso_inv, Scheme.toSpecΓ_appTop]
    change ((Scheme.ΓSpecIso Γ(T, ⊤)).inv ≫ (Scheme.ΓSpecIso Γ(T, ⊤)).hom) (φ _) = _
    rw [Iso.inv_hom_id]
    change φ (coordUnit k n j : torusCoord k n) = _
    simp only [coordUnit, MonoidHom.coe_toHomUnits, φ, AddMonoidAlgebra.lift_of, m, MonoidHom.coe_comp,
      Function.comp_apply, unitsMonoidHom_single, Units.coeHom_apply]

theorem conv_single {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] {M : Type} [AddCommMonoid M]
    (χ ψ : WithConv (AddMonoidAlgebra S M →ₐ[S] T)) (g : M) :
    (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) =
      χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
  rw [AlgHom.convMul_def]
  simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]

theorem appTop_torusPtId_coordUnit (n : ℕ) (χ : torusCoord k n →ₐ[k] k) (j : Fin n) :
    (torusPtId k n χ).1.appTop ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k n))).inv
        ((coordUnit k n j : (torusCoord k n)ˣ) : torusCoord k n)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv (χ (coordUnit k n j : torusCoord k n)) := by
  change (Spec.map (CommRingCat.ofHom χ.toRingHom)).appTop _ = _
  rw [appTop_ΓSpecIso_inv]
  rfl

end AlgebraicGeometry.RelPicard.TorusPtAssembly

end

open AlgebraicGeometry.RelPicard.TorusPtAssembly in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L))) :
    ∃ τ : SchemeHomOver (torusStr k (s - 1)) D.toBase,
      (∀ χ χ' : WithConv (torusCoord k (s - 1) →ₐ[k] k),
        NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) (χ * χ').ofConv) τ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul _
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ'.ofConv) τ)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        (NeronModelInfra.schemeHomOverComp a ν₁ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ∧
          NeronModelInfra.schemeHomOverComp a ν₂ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t) ↔
        ∃ y : SchemeHomOver t (torusStr k (s - 1)), NeronModelInfra.schemeHomOverComp y τ = a) ∧
      (∀ y y' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (torusStr k (s - 1)),
        NeronModelInfra.schemeHomOverComp y τ = NeronModelInfra.schemeHomOverComp y' τ → y = y') := by
  classical
  haveI : IsReduced X := hXred

  obtain ⟨p₁, p₂, hinj, hnode, hinter⟩ :=
    AlgebraicGeometry.exists_rationalPoint_enumeration_of_natCard_pullback_eq k x i₁ i₂ s hs hs0

  obtain ⟨MU, hMUinv, hMU⟩ := exists_isInvertible_isNodeUnitModule k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr
    (torusStr k (s - 1)) (univUnits s)
  obtain ⟨⟨eU₁⟩, ⟨eU₂⟩⟩ := IsNodeUnitModule.nonempty_pullback_curveChange_iso_unit k x i₁ i₂ hjs p₁ p₂ hinj hnode
    hinter hcr hMUinv hMU

  let PU : RigidifiedLineBundle x ε (torusStr k (s - 1)) :=
    { L := MU
      isInvertible := hMUinv
      rigidified := ⟨(Scheme.Modules.pullbackCongr (rigSection_curveChange i₁.1 i₁.2 hε _).symm).app MU ≪≫
        ((Scheme.Modules.pullbackComp _ _).app MU).symm ≪≫
        (Scheme.Modules.pullback _).mapIso eU₁ ≪≫ Scheme.Modules.pullbackUnitIso _⟩ }
  have hPU : FibrewiseAlgEquivZero PU :=
    IsNodeUnitModule.fibrewiseAlgEquivZero k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr ε PU hMU
  let τ : SchemeHomOver (torusStr k (s - 1)) D.toBase := hD.classify _ PU hPU
  have hτ : Nonempty ((hD.poincare.pullbackAlong τ).L ≅ MU) := hD.classify_spec _ PU hPU

  have hPy : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (y : SchemeHomOver t (torusStr k (s - 1))),
      Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp y τ)).L ≅
        (Scheme.Modules.pullback (baseChangeSnd x y)).obj MU) := fun y =>
    ⟨pullbackAlongCompIso hD.poincare τ y ≪≫ (Scheme.Modules.pullback _).mapIso hτ.some⟩
  refine ⟨τ, ?_, ?_, ?_⟩
  ·
    intro χ χ'
    apply hD.ext_of_iso (𝟙 _)
    obtain ⟨eL⟩ := hPy (torusPtId k (s - 1) (χ * χ').ofConv)
    obtain ⟨eχ⟩ := hPy (torusPtId k (s - 1) χ.ofConv)
    obtain ⟨eχ'⟩ := hPy (torusPtId k (s - 1) χ'.ofConv)
    obtain ⟨em⟩ := RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso (P := algEquivZeroGroupCut x ε) hD (𝟙 _)
      (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ.ofConv) τ)
      (NeronModelInfra.schemeHomOverComp (torusPtId k (s - 1) χ'.ofConv) τ)
    have hNχ := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hMUinv hMU
      (torusPtId k (s - 1) χ.ofConv)
    have hNχ' := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hMUinv hMU
      (torusPtId k (s - 1) χ'.ofConv)
    have hNχχ' := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hMUinv hMU
      (torusPtId k (s - 1) (χ * χ').ofConv)
    have hT := IsNodeUnitModule.tensor k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr (hMUinv.pullback _) hNχ
      (hMUinv.pullback _) hNχ'
    have hunits : (fun j => Units.map (torusPtId k (s - 1) (χ * χ').ofConv).1.appTop.hom.toMonoidHom (univUnits s j)) =
        (fun j => Units.map (torusPtId k (s - 1) χ.ofConv).1.appTop.hom.toMonoidHom (univUnits s j)) *
        (fun j => Units.map (torusPtId k (s - 1) χ'.ofConv).1.appTop.hom.toMonoidHom (univUnits s j)) := by
      funext j
      by_cases hj : j.1 = 0
      · simp [univUnits, hj]
      · apply Units.ext
        simp only [univUnits, hj, dif_neg, not_false_eq_true, Pi.mul_apply, Units.val_mul, Units.coe_map,
          RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
        rw [appTop_torusPtId_coordUnit, appTop_torusPtId_coordUnit, appTop_torusPtId_coordUnit, ← map_mul]
        congr 1
        exact conv_single χ χ' _
    rw [hunits] at hNχχ'
    obtain ⟨ee⟩ := IsNodeUnitModule.nonempty_iso hNχχ' hT
    exact ⟨eL ≪≫ ee ≪≫ (eχ.symm ⊗ᵢ eχ'.symm) ≪≫ em.symm⟩
  ·
    intro T t a
    constructor
    · rintro ⟨h1, h2⟩
      rw [hν₁, comp_pullbackHom_eq_one_iff i₁ hε hD hD₁ t] at h1
      obtain ⟨f₁⟩ := h1
      rw [comp_ν₂_eq_one_iff i₂ hD hD₂ ν₂ hν₂ t] at h2
      obtain ⟨g₂⟩ := h2
      have hPinv : Scheme.Modules.IsInvertible (hD.poincare.pullbackAlong a).L := (hD.poincare.pullbackAlong a).isInvertible

      obtain ⟨r⟩ := Scheme.Modules.IsInvertible.nonempty_iso_pullback_pullback_of_rigidify_iso_unit
        (rigSection c₂ t ε₂) (pullback.snd c₂ t) (hPinv.pullback (curveChange i₂.1 i₂.2 t)) ⟨g₂⟩

      have n12 : nodeSectionFst p₁ t ⟨0, hs0⟩ ≫ curveChange i₁.1 i₁.2 t =
          nodeSectionSnd p₂ t ⟨0, hs0⟩ ≫ curveChange i₂.1 i₂.2 t := by
        simp only [nodeSectionFst, nodeSectionSnd]
        rw [rigSection_curveChange i₁.1 i₁.2 (ε := ⟨(p₁ ⟨0, hs0⟩).1 ≫ i₁.1, by
              rw [Category.assoc, i₁.2]; exact (p₁ ⟨0, hs0⟩).2⟩) rfl,
          rigSection_curveChange i₂.1 i₂.2 (ε := ⟨(p₁ ⟨0, hs0⟩).1 ≫ i₁.1, by
              rw [Category.assoc, i₁.2]; exact (p₁ ⟨0, hs0⟩).2⟩) (hnode ⟨0, hs0⟩).symm]
      have hN : Nonempty ((Scheme.Modules.pullback (rigSection c₂ t ε₂)).obj
          ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L) ≅
            SheafOfModules.unit T.ringCatSheaf) := by

        have s₂ : nodeSectionSnd p₂ t ⟨0, hs0⟩ ≫ pullback.snd c₂ t = 𝟙 T := rigSection_snd _ _
        refine ⟨?_⟩
        refine ((Scheme.Modules.pullbackId _).app _).symm ≪≫ (Scheme.Modules.pullbackCongr s₂.symm).app _ ≪≫
          ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
          ((Scheme.Modules.pullback (nodeSectionSnd p₂ t ⟨0, hs0⟩)).mapIso r).symm ≪≫
          (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr n12.symm).app _ ≪≫
          ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
          (Scheme.Modules.pullback (nodeSectionFst p₁ t ⟨0, hs0⟩)).mapIso f₁ ≪≫ Scheme.Modules.pullbackUnitIso _
      have f₂ : (Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L ≅
          SheafOfModules.unit (pullback c₂ t).ringCatSheaf :=
        r ≪≫ (Scheme.Modules.pullback _).mapIso hN.some ≪≫ Scheme.Modules.pullbackUnitIso _

      obtain ⟨u, hu⟩ := exists_isNodeUnitModule_of_pullback_curveChange_iso_unit k x i₁ i₂ hjs p₁ p₂ hinj hnode
        hinter hcr t _ hPinv ⟨f₁⟩ ⟨f₂⟩
      have hu' := IsNodeUnitModule.smul_units hu (u ⟨0, hs0⟩)⁻¹
      obtain ⟨y, hy⟩ := exists_torusPt_of_units (s - 1) t (fun j => (u ⟨0, hs0⟩)⁻¹ * u ⟨j.1 + 1, by omega⟩)
      refine ⟨y, hD.ext_of_iso t _ _ ?_⟩
      obtain ⟨e⟩ := hPy y
      have hN4 := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hMUinv hMU y
      have huy : (fun j => Units.map y.1.appTop.hom.toMonoidHom (univUnits s j)) = fun j => (u ⟨0, hs0⟩)⁻¹ * u j := by
        funext j
        by_cases hj : j.1 = 0
        · have : j = ⟨0, hs0⟩ := Fin.ext hj
          subst this
          simp [univUnits]
        · apply Units.ext
          have := hy ⟨j.1 - 1, by omega⟩
          simp only [univUnits, hj, dif_neg, not_false_eq_true] at this ⊢
          have hj' : (⟨j.1 - 1 + 1, by omega⟩ : Fin s) = j := Fin.ext (by simp only; omega)
          rw [hj'] at this
          exact this
      rw [huy] at hN4
      obtain ⟨ee⟩ := IsNodeUnitModule.nonempty_iso hN4 hu'
      exact ⟨e ≪≫ ee⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨e⟩ := hPy y
      have hN := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hMUinv hMU y
      obtain ⟨⟨f₁⟩, ⟨f₂⟩⟩ := IsNodeUnitModule.nonempty_pullback_curveChange_iso_unit k x i₁ i₂ hjs p₁ p₂ hinj
        hnode hinter hcr (hMUinv.pullback _) hN
      constructor
      · rw [hν₁, comp_pullbackHom_eq_one_iff i₁ hε hD hD₁ t]
        exact ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ f₁⟩
      · rw [comp_ν₂_eq_one_iff i₂ hD hD₂ ν₂ hν₂ t]
        obtain ⟨ru⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
          (RigidifiedLineBundle.unit (c := c₂) (ε := ε₂) t)
        exact ⟨Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback _).mapIso e ≪≫ f₂) ≪≫ ru⟩
  ·
    intro y y' hyy
    haveI : IsIntegral C₁ := isIntegral_of_geometricallyIntegral c₁
    haveI : IsIntegral C₂ := isIntegral_of_geometricallyIntegral c₂
    have hiso : Nonempty ((Scheme.Modules.pullback (baseChangeSnd x y)).obj MU ≅
        (Scheme.Modules.pullback (baseChangeSnd x y')).obj MU) := by
      obtain ⟨e⟩ := hPy y
      obtain ⟨e'⟩ := hPy y'
      rw [hyy] at e
      exact ⟨e.symm ≪≫ e'⟩
    have hN := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hMUinv hMU y
    have hN' := IsNodeUnitModule.pullback_baseChangeSnd k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr hMUinv hMU y'
    obtain ⟨c, hc⟩ := IsNodeUnitModule.exists_eq_mul_of_iso k x i₁ i₂ hjs p₁ p₂ hinj hnode hinter hcr
      (hMUinv.pullback _) (hMUinv.pullback _) hN hN' hiso
    have hc0 := hc ⟨0, hs0⟩
    simp only [univUnits, dif_pos, map_one] at hc0
    have hc1 : c = 1 := by simpa using hc0.symm
    subst hc1
    refine torusPt_ext (s - 1) y y' fun j => ?_
    have hj := hc ⟨j.1 + 1, by omega⟩
    simp only [univUnits, Nat.add_one_ne_zero, dif_neg, not_false_eq_true, one_mul, Nat.add_sub_cancel,
      Fin.eta] at hj
    exact (congrArg Units.val hj).symm

end S_AlgebraicGeometry_RelPicard_exists_torus_ker_restrictPair_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_torus_ker_restrictPair_of_twoGluedSmoothCurves (solution)
