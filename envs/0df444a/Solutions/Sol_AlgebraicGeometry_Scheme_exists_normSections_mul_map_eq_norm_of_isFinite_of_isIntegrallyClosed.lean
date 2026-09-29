-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7b7f3d70-0355-5877-b925-a165353285ce

import Mathlib
import Theorems.Thm_Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq
import Theorems.Thm_Algebra_norm_algebraMap_eq_of_isPushout_of_isFractionRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry TopologicalSpace Opposite"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Surjective Scheme.germToFunctionField Scheme.Hom Scheme.germToFunctionField_injective Scheme.Hom.germ_stalkMap_apply IsFinite IsAffine isPullback_morphismRestrict Spec IsIntegral Spec.map Scheme Scheme.Hom.appTop functionField_isFractionRing_of_isAffineOpen Scheme.Hom.comp_appTop Flat Scheme.Hom.preimage_mono IsFinite.finite_app Scheme.isoSpec_hom_naturality Scheme.Spec Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.resLE_comp_ι_assoc Scheme.Hom.app_eq_appLE Scheme.Hom.resLE_eq_morphismRestrict Scheme.Hom.resLE_app_top Flat.generalizingMap Scheme.Hom.comp_preimage IsAffineHom Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq"
namespace NormSections
p2m_open "AlgebraicGeometry"

variable {X Y : Scheme.{u}}

theorem genericPoint_mem (Z : Scheme.{u}) [IsIntegral Z] (U : Z.Opens) [h : Nonempty U] : genericPoint Z ∈ U :=
  ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by obtain ⟨⟨z, hz⟩⟩ := h; exact ⟨z, trivial, hz⟩)

section gen

variable (π : X ⟶ Y) [IsIntegral X] [IsIntegral Y]

theorem base_genericPoint_eq_of_surjective [Surjective π] : π.base (genericPoint X) = genericPoint Y := by
  apply IsGenericPoint.eq _ (genericPoint_spec Y)
  have h := (genericPoint_spec X).image π.base.hom.continuous
  have hsurj : Function.Surjective π.base := π.surjective
  rwa [Set.image_univ, hsurj.range_eq, closure_univ] at h

theorem base_genericPoint_eq_of_flat [Flat π] : π.base (genericPoint X) = genericPoint Y := by
  have hspec : genericPoint Y ⤳ π.base (genericPoint X) :=
    (genericPoint_spec Y).specializes (by simp)
  obtain ⟨x, hx, hxy⟩ := Flat.generalizingMap π hspec

  have hx' : x = genericPoint X :=
    (hx.antisymm ((genericPoint_spec X).specializes (by simp))).eq
  rw [← hxy, hx']

variable {π}

theorem nonempty_preimage (hgen : π.base (genericPoint X) = genericPoint Y) (V : Y.Opens) [Nonempty V] :
    Nonempty (π ⁻¹ᵁ V) :=
  ⟨⟨genericPoint X, show π.base (genericPoint X) ∈ V by rw [hgen]; exact genericPoint_mem Y V⟩⟩

variable (π) in

noncomputable def fieldMap (hgen : π.base (genericPoint X) = genericPoint Y) : Y.functionField →+* X.functionField :=
  ((Y.presheaf.stalkCongr (Inseparable.of_eq hgen.symm)).hom ≫ π.stalkMap (genericPoint X)).hom

theorem germ_app (hgen : π.base (genericPoint X) = genericPoint Y) (V : Y.Opens) [Nonempty V] (a : Γ(Y, V)) :
    @Scheme.germToFunctionField X _ (π ⁻¹ᵁ V) (nonempty_preimage hgen V) (π.app V a) =
      fieldMap π hgen (Y.germToFunctionField V a) := by
  haveI := nonempty_preimage hgen V
  have hξ : π.base (genericPoint X) ∈ V := by rw [hgen]; exact genericPoint_mem Y V
  have h1 : (Y.presheaf.stalkCongr (Inseparable.of_eq hgen.symm)).hom (Y.germToFunctionField V a) =
      Y.presheaf.germ V (π.base (genericPoint X)) hξ a := by
    show (Y.presheaf.stalkCongr _).hom (Y.presheaf.germ V (genericPoint Y) (genericPoint_mem Y V) a) = _
    rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_apply]
  show X.presheaf.germ (π ⁻¹ᵁ V) (genericPoint X) _ (π.app V a) =
    π.stalkMap (genericPoint X) ((Y.presheaf.stalkCongr _).hom (Y.germToFunctionField V a))
  rw [h1, Scheme.Hom.germ_stalkMap_apply]

end gen

theorem germ_res {Z : Scheme.{u}} [IsIntegral Z] {V V' : Z.Opens} (h : V' ≤ V) [Nonempty V] [Nonempty V']
    (s : Γ(Z, V)) : Z.germToFunctionField V' (Z.presheaf.map (homOfLE h).op s) = Z.germToFunctionField V s := by
  show Z.presheaf.germ V' (genericPoint Z) _ (Z.presheaf.map (homOfLE h).op s) = Z.presheaf.germ V (genericPoint Z) _ s
  exact TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) (genericPoint Z) (genericPoint_mem Z V') s

theorem subsingleton_of_eq_bot {Z : Scheme.{u}} {V : Z.Opens} (hV : V = ⊥) (s t : Γ(Z, V)) : s = t := by
  subst hV
  exact Z.sheaf.eq_of_locally_eq' (fun i : PEmpty.{u + 1} => (⊥ : Z.Opens)) ⊥ (fun i => i.elim) bot_le s t
    (fun i => i.elim)

theorem eq_bot_or_nonempty {Z : Scheme.{u}} (V : Z.Opens) : V = ⊥ ∨ Nonempty V := by
  rcases (V : Set Z).eq_empty_or_nonempty with h | ⟨z, hz⟩
  · left; ext1; exact h
  · right; exact ⟨⟨z, hz⟩⟩

end AlgebraicGeometry.NormSections

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Surjective Scheme.germToFunctionField Scheme.Hom Scheme.germToFunctionField_injective Scheme.Hom.germ_stalkMap_apply IsFinite IsAffine isPullback_morphismRestrict Spec IsIntegral Spec.map Scheme Scheme.Hom.appTop functionField_isFractionRing_of_isAffineOpen Scheme.Hom.comp_appTop Flat Scheme.Hom.preimage_mono IsFinite.finite_app Scheme.isoSpec_hom_naturality Scheme.Spec Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.resLE_comp_ι_assoc Scheme.Hom.app_eq_appLE Scheme.Hom.resLE_eq_morphismRestrict Scheme.Hom.resLE_app_top Flat.generalizingMap Scheme.Hom.comp_preimage IsAffineHom Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq"
namespace NormSections
namespace S4
p2m_open "AlgebraicGeometry"

open CategoryTheory.Limits

variable {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X)
  (sq : IsPullback g' π' π g)

include sq in
theorem preimage_le (V : Y.Opens) (V' : Y'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V) : π' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ (π ⁻¹ᵁ V) := by
  intro x hx
  show (g' ≫ π).base x ∈ V
  rw [sq.w]
  exact hV' hx

include sq in

theorem isPullback_resLE (V : Y.Opens) (V' : Y'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V) :
    IsPullback (g'.resLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ V') (preimage_le π g π' g' sq V V' hV'))
      (π'.resLE V' (π' ⁻¹ᵁ V') le_rfl) (π.resLE V (π ⁻¹ᵁ V) le_rfl) (g.resLE V V' hV') := by
  have big : IsPullback ((π' ⁻¹ᵁ V').ι ≫ g') (π' ∣_ V') π (V'.ι ≫ g) :=
    (isPullback_morphismRestrict π' V').flip.paste_horiz sq
  rw [← Scheme.Hom.resLE_comp_ι g' (preimage_le π g π' g' sq V V' hV'), ← Scheme.Hom.resLE_comp_ι g hV',
    ← Scheme.Hom.resLE_eq_morphismRestrict] at big
  have right : IsPullback (π ⁻¹ᵁ V).ι (π.resLE V (π ⁻¹ᵁ V) le_rfl) π V.ι := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict π V).flip
  refine IsPullback.of_right big ?_ right
  rw [← cancel_mono V.ι]
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
  rw [Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc, sq.w]

theorem isPushout_appTop {P Q R S : Scheme.{u}} [IsAffine P] [IsAffine Q] [IsAffine R] [IsAffine S]
    {fst : P ⟶ Q} {snd : P ⟶ R} {f : Q ⟶ S} {k : R ⟶ S} (h : IsPullback fst snd f k) :
    IsPushout f.appTop k.appTop fst.appTop snd.appTop := by

  have h' : IsPullback (Spec.map fst.appTop) (Spec.map snd.appTop) (Spec.map f.appTop) (Spec.map k.appTop) := by
    refine IsPullback.of_iso h P.isoSpec Q.isoSpec R.isoSpec S.isoSpec ?_ ?_ ?_ ?_
    · exact (Scheme.isoSpec_hom_naturality fst).symm
    · exact (Scheme.isoSpec_hom_naturality snd).symm
    · exact (Scheme.isoSpec_hom_naturality f).symm
    · exact (Scheme.isoSpec_hom_naturality k).symm

  have h'' : IsPullback fst.appTop.op snd.appTop.op f.appTop.op k.appTop.op :=
    IsPullback.of_map Scheme.Spec (by rw [← op_comp, ← op_comp, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h.w]) h'
  exact h''.unop.flip

end AlgebraicGeometry.NormSections.S4

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Surjective Scheme.germToFunctionField Scheme.Hom Scheme.germToFunctionField_injective Scheme.Hom.germ_stalkMap_apply IsFinite IsAffine isPullback_morphismRestrict Spec IsIntegral Spec.map Scheme Scheme.Hom.appTop functionField_isFractionRing_of_isAffineOpen Scheme.Hom.comp_appTop Flat Scheme.Hom.preimage_mono IsFinite.finite_app Scheme.isoSpec_hom_naturality Scheme.Spec Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.resLE_comp_ι_assoc Scheme.Hom.app_eq_appLE Scheme.Hom.resLE_eq_morphismRestrict Scheme.Hom.resLE_app_top Flat.generalizingMap Scheme.Hom.comp_preimage IsAffineHom Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq"
namespace NormSections
namespace S4
p2m_open "AlgebraicGeometry"

open CategoryTheory.Limits

variable {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X)
  (sq : IsPullback g' π' π g)

include sq in

theorem isPushout_app (V : Y.Opens) (hV : IsAffineOpen V) (V' : Y'.Opens) (hV'a : IsAffineOpen V')
    (hV' : V' ≤ g ⁻¹ᵁ V) [IsAffineHom π] [IsAffineHom π'] :
    IsPushout (π.app V) (g.appLE V V' hV')
      (g'.appLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ V') (preimage_le π g π' g' sq V V' hV')) (π'.app V') := by
  haveI : IsAffine V := hV
  haveI : IsAffine V' := hV'a
  haveI : IsAffine (π ⁻¹ᵁ V) := hV.preimage π
  haveI : IsAffine (π' ⁻¹ᵁ V') := hV'a.preimage π'
  have hP := isPushout_appTop (isPullback_resLE π g π' g' sq V V' hV')
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at hP
  have hQ : IsPushout (π.appLE V (π ⁻¹ᵁ V) le_rfl) (g.appLE V V' hV')
      (g'.appLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ V') (preimage_le π g π' g' sq V V' hV')) (π'.appLE V' (π' ⁻¹ᵁ V') le_rfl) :=
    IsPushout.of_iso hP V.topIso (π ⁻¹ᵁ V).topIso V'.topIso (π' ⁻¹ᵁ V').topIso
      (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  rw [← Scheme.Hom.app_eq_appLE, ← Scheme.Hom.app_eq_appLE] at hQ
  exact hQ

end AlgebraicGeometry.NormSections.S4

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Surjective Scheme.germToFunctionField Scheme.Hom Scheme.germToFunctionField_injective Scheme.Hom.germ_stalkMap_apply IsFinite IsAffine isPullback_morphismRestrict Spec IsIntegral Spec.map Scheme Scheme.Hom.appTop functionField_isFractionRing_of_isAffineOpen Scheme.Hom.comp_appTop Flat Scheme.Hom.preimage_mono IsFinite.finite_app Scheme.isoSpec_hom_naturality Scheme.Spec Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.resLE_comp_ι_assoc Scheme.Hom.app_eq_appLE Scheme.Hom.resLE_eq_morphismRestrict Scheme.Hom.resLE_app_top Flat.generalizingMap Scheme.Hom.comp_preimage IsAffineHom Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq"
namespace NormSections
p2m_open "AlgebraicGeometry"

theorem germ_map {Z : Scheme.{u}} [IsIntegral Z] {V V' : Z.Opens} (i : V' ⟶ V) [Nonempty V] [Nonempty V']
    (s : Γ(Z, V)) : Z.germToFunctionField V' (Z.presheaf.map i.op s) = Z.germToFunctionField V s := by
  show Z.presheaf.germ V' (genericPoint Z) _ (Z.presheaf.map i.op s) = Z.presheaf.germ V (genericPoint Z) _ s
  exact TopCat.Presheaf.germ_res_apply Z.presheaf i (genericPoint Z) (genericPoint_mem Z V') s

theorem exists_isAffineOpen_le {Z : Scheme.{u}} (W : Z.Opens) [hW : Nonempty W] :
    ∃ V : Z.Opens, IsAffineOpen V ∧ V ≤ W ∧ Nonempty V := by
  obtain ⟨⟨z, hz⟩⟩ := hW
  obtain ⟨U, hU, hzU, hUW⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Z)) hz
  exact ⟨U, hU, hUW, ⟨⟨z, hzU⟩⟩⟩

theorem app_injective {X Y : Scheme.{u}} (π : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    (hgen : π.base (genericPoint X) = genericPoint Y) (V : Y.Opens) [Nonempty V] :
    Function.Injective (π.app V) := by
  haveI := nonempty_preimage hgen V
  intro a b h
  apply Scheme.germToFunctionField_injective Y V
  apply (fieldMap π hgen).injective
  rw [← germ_app hgen V a, ← germ_app hgen V b]
  exact congrArg _ h

theorem germ_app_eq_norm_of_isPullback
    {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' π' π g)
    [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y] [Flat g] [IsIntegral X'] [IsIntegral Y']
    [IsFinite π'] [Surjective π']
    (W : Y.Opens) [Nonempty W] [Nonempty (g ⁻¹ᵁ W)] [Nonempty (π ⁻¹ᵁ W)] [Nonempty (π' ⁻¹ᵁ (g ⁻¹ᵁ W))]
    (a : Γ(X, π ⁻¹ᵁ W)) (t : Γ(Y, W))
    (ht : letI := (fieldMap π (base_genericPoint_eq_of_surjective π)).toAlgebra
      Y.germToFunctionField W t = Algebra.norm Y.functionField (X.germToFunctionField (π ⁻¹ᵁ W) a)) :
    letI := (fieldMap π' (base_genericPoint_eq_of_surjective π')).toAlgebra
    Y'.germToFunctionField (g ⁻¹ᵁ W) (g.app W t) =
      Algebra.norm Y'.functionField (X'.germToFunctionField (π' ⁻¹ᵁ (g ⁻¹ᵁ W))
        (X'.presheaf.map (eqToHom (show π' ⁻¹ᵁ (g ⁻¹ᵁ W) = g' ⁻¹ᵁ (π ⁻¹ᵁ W) by
          rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w])).op ((g'.app (π ⁻¹ᵁ W)).hom a))) := by

  have hπ := base_genericPoint_eq_of_surjective π
  have hπ' := base_genericPoint_eq_of_surjective π'
  have hg := base_genericPoint_eq_of_flat g
  haveI : Flat g' := MorphismProperty.of_isPullback (P := @Flat) sq.flip inferInstance
  have hg' := base_genericPoint_eq_of_flat g'
  letI algKL : Algebra Y.functionField X.functionField := (fieldMap π hπ).toAlgebra
  letI algK'L' : Algebra Y'.functionField X'.functionField := (fieldMap π' hπ').toAlgebra
  haveI : Nonempty (g' ⁻¹ᵁ (π ⁻¹ᵁ W)) := nonempty_preimage hg' _

  rw [germ_app hg W t, ht, germ_map, germ_app hg' (π ⁻¹ᵁ W) a]
  change fieldMap g hg (Algebra.norm Y.functionField (X.germToFunctionField (π ⁻¹ᵁ W) a)) =
    Algebra.norm Y'.functionField (fieldMap g' hg' (X.germToFunctionField (π ⁻¹ᵁ W) a))

  obtain ⟨V, hVaff, hVW, hVne⟩ := exists_isAffineOpen_le W
  haveI := hVne
  haveI : Nonempty (g ⁻¹ᵁ V) := nonempty_preimage hg V
  obtain ⟨V', hV'aff, hV'le, hV'ne⟩ := exists_isAffineOpen_le (g ⁻¹ᵁ V)
  haveI := hV'ne
  haveI : Nonempty (π ⁻¹ᵁ V) := nonempty_preimage hπ V
  haveI : Nonempty (π' ⁻¹ᵁ V') := nonempty_preimage hπ' V'
  haveI : Nonempty (g' ⁻¹ᵁ (π ⁻¹ᵁ V)) := nonempty_preimage hg' _
  rw [← germ_res (π.preimage_mono hVW) a]
  set b := X.presheaf.map (homOfLE (π.preimage_mono hVW)).op a with hb

  have hle := S4.preimage_le π g π' g' sq V V' hV'le
  letI iAB : Algebra Γ(Y, V) Γ(X, π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  letI iAA' : Algebra Γ(Y, V) Γ(Y', V') := (g.appLE V V' hV'le).hom.toAlgebra
  letI iA'B' : Algebra Γ(Y', V') Γ(X', π' ⁻¹ᵁ V') := (π'.app V').hom.toAlgebra
  letI iBB' : Algebra Γ(X, π ⁻¹ᵁ V) Γ(X', π' ⁻¹ᵁ V') := (g'.appLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ V') hle).hom.toAlgebra
  letI iAB' : Algebra Γ(Y, V) Γ(X', π' ⁻¹ᵁ V') := ((π'.app V').hom.comp (g.appLE V V' hV'le).hom).toAlgebra
  haveI : IsScalarTower Γ(Y, V) Γ(Y', V') Γ(X', π' ⁻¹ᵁ V') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hP := S4.isPushout_app π g π' g' sq V hVaff V' hV'aff hV'le
  haveI : IsScalarTower Γ(Y, V) Γ(X, π ⁻¹ᵁ V) Γ(X', π' ⁻¹ᵁ V') := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    have h := CategoryTheory.ConcreteCategory.congr_hom hP.w x
    rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
    exact h.symm
  haveI : Algebra.IsPushout Γ(Y, V) Γ(X, π ⁻¹ᵁ V) Γ(Y', V') Γ(X', π' ⁻¹ᵁ V') :=
    CommRingCat.isPushout_iff_isPushout.mp hP
  haveI : Module.Finite Γ(Y, V) Γ(X, π ⁻¹ᵁ V) := RingHom.finite_algebraMap.mp (IsFinite.finite_app π V hVaff)
  have hAB : Function.Injective (algebraMap Γ(Y, V) Γ(X, π ⁻¹ᵁ V)) := app_injective π hπ V
  have hA'B' : Function.Injective (algebraMap Γ(Y', V') Γ(X', π' ⁻¹ᵁ V')) := app_injective π' hπ' V'

  letI algAL : Algebra Γ(Y, V) X.functionField :=
    ((X.germToFunctionField (π ⁻¹ᵁ V)).hom.comp (π.app V).hom).toAlgebra
  haveI : IsScalarTower Γ(Y, V) Γ(X, π ⁻¹ᵁ V) X.functionField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(Y, V) Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    show (X.germToFunctionField (π ⁻¹ᵁ V)) (π.app V x) = fieldMap π hπ (Y.germToFunctionField V x)
    exact germ_app hπ V x
  letI algA'L' : Algebra Γ(Y', V') X'.functionField :=
    ((X'.germToFunctionField (π' ⁻¹ᵁ V')).hom.comp (π'.app V').hom).toAlgebra
  haveI : IsScalarTower Γ(Y', V') Γ(X', π' ⁻¹ᵁ V') X'.functionField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(Y', V') Y'.functionField X'.functionField := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    show (X'.germToFunctionField (π' ⁻¹ᵁ V')) (π'.app V' x) = fieldMap π' hπ' (Y'.germToFunctionField V' x)
    exact germ_app hπ' V' x
  haveI : IsFractionRing Γ(Y, V) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y V hVaff
  haveI : IsFractionRing Γ(X, π ⁻¹ᵁ V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X _ (hVaff.preimage π)
  haveI : IsFractionRing Γ(Y', V') Y'.functionField := functionField_isFractionRing_of_isAffineOpen Y' V' hV'aff
  haveI : IsFractionRing Γ(X', π' ⁻¹ᵁ V') X'.functionField :=
    functionField_isFractionRing_of_isAffineOpen X' _ (hV'aff.preimage π')

  have hφ : (fieldMap g hg).comp (algebraMap Γ(Y, V) Y.functionField) =
      (algebraMap Γ(Y', V') Y'.functionField).comp (algebraMap Γ(Y, V) Γ(Y', V')) := by
    ext x
    change fieldMap g hg (Y.germToFunctionField V x) =
      Y'.germToFunctionField V' (Y'.presheaf.map (homOfLE hV'le).op (g.app V x))
    rw [← germ_app hg V x, germ_res]

  have hd := Algebra.norm_algebraMap_eq_of_isPushout_of_isFractionRing
    (A := Γ(Y, V)) (B := Γ(X, π ⁻¹ᵁ V)) (A' := Γ(Y', V')) (B' := Γ(X', π' ⁻¹ᵁ V')) hAB hA'B'
    Y.functionField X.functionField Y'.functionField X'.functionField (fieldMap g hg) hφ b
  have eB : algebraMap Γ(X', π' ⁻¹ᵁ V') X'.functionField (algebraMap Γ(X, π ⁻¹ᵁ V) Γ(X', π' ⁻¹ᵁ V') b) =
      fieldMap g' hg' (X.germToFunctionField (π ⁻¹ᵁ V) b) := by
    change X'.germToFunctionField (π' ⁻¹ᵁ V')
      (X'.presheaf.map (homOfLE hle).op (g'.app (π ⁻¹ᵁ V) b)) = _
    rw [germ_res, germ_app hg']
  rw [eB] at hd
  exact hd

end AlgebraicGeometry.NormSections

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom.resLE_comp_ι Surjective Scheme.germToFunctionField Scheme.Hom Scheme.germToFunctionField_injective Scheme.Hom.germ_stalkMap_apply IsFinite IsAffine isPullback_morphismRestrict Spec IsIntegral Spec.map Scheme Scheme.Hom.appTop functionField_isFractionRing_of_isAffineOpen Scheme.Hom.comp_appTop Flat Scheme.Hom.preimage_mono IsFinite.finite_app Scheme.isoSpec_hom_naturality Scheme.Spec Scheme.isBasis_affineOpens IsAffineOpen Scheme.Hom.resLE_comp_ι_assoc Scheme.Hom.app_eq_appLE Scheme.Hom.resLE_eq_morphismRestrict Scheme.Hom.resLE_app_top Flat.generalizingMap Scheme.Hom.comp_preimage IsAffineHom Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq"
namespace NormSections
p2m_open "AlgebraicGeometry"

variable {X Y : Scheme.{u}}

section normGerm

variable (π : X ⟶ Y) [IsIntegral X] [IsIntegral Y]

noncomputable def normGerm (hgen : π.base (genericPoint X) = genericPoint Y) (W : Y.Opens) [Nonempty W]
    (a : Γ(X, π ⁻¹ᵁ W)) : Y.functionField :=
  letI := (fieldMap π hgen).toAlgebra
  haveI := nonempty_preimage hgen W
  Algebra.norm Y.functionField (X.germToFunctionField (π ⁻¹ᵁ W) a)

variable {π}

theorem normGerm_def (hgen : π.base (genericPoint X) = genericPoint Y) (W : Y.Opens) [Nonempty W]
    [Nonempty (π ⁻¹ᵁ W)] (a : Γ(X, π ⁻¹ᵁ W)) :
    normGerm π hgen W a =
      letI := (fieldMap π hgen).toAlgebra
      Algebra.norm Y.functionField (X.germToFunctionField (π ⁻¹ᵁ W) a) := rfl

theorem normGerm_one (hgen : π.base (genericPoint X) = genericPoint Y) (W : Y.Opens) [Nonempty W] :
    normGerm π hgen W 1 = 1 := by
  haveI := nonempty_preimage hgen W
  rw [normGerm_def, map_one, map_one]

theorem normGerm_mul (hgen : π.base (genericPoint X) = genericPoint Y) (W : Y.Opens) [Nonempty W]
    (a b : Γ(X, π ⁻¹ᵁ W)) : normGerm π hgen W (a * b) = normGerm π hgen W a * normGerm π hgen W b := by
  haveI := nonempty_preimage hgen W
  rw [normGerm_def, normGerm_def, normGerm_def, map_mul, map_mul]

theorem normGerm_res (hgen : π.base (genericPoint X) = genericPoint Y) {W W' : Y.Opens} (h : W' ≤ W) [Nonempty W]
    [Nonempty W'] (a : Γ(X, π ⁻¹ᵁ W)) :
    normGerm π hgen W' (X.presheaf.map (homOfLE (π.preimage_mono h)).op a) = normGerm π hgen W a := by
  haveI := nonempty_preimage hgen W
  haveI := nonempty_preimage hgen W'
  rw [normGerm_def, normGerm_def, germ_res]

end normGerm

open Classical in

noncomputable def Nf ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) (W : Y.Opens) (a : Γ(X, π ⁻¹ᵁ W)) : Γ(Y, W) :=
  if h : ∃ s : Γ(Y, W), ∃ (hX : IsIntegral X) (hY : IsIntegral Y) (hW : Nonempty W)
      (hgen : π.base (genericPoint X) = genericPoint Y), Y.germToFunctionField W s = normGerm π hgen W a
  then h.choose else 1

theorem germ_Nf {π : X ⟶ Y} [IsIntegral X] [IsIntegral Y] (hgen : π.base (genericPoint X) = genericPoint Y)
    (W : Y.Opens) [Nonempty W] (a : Γ(X, π ⁻¹ᵁ W)) (hex : ∃ s : Γ(Y, W), Y.germToFunctionField W s = normGerm π hgen W a) :
    Y.germToFunctionField W (Nf π W a) = normGerm π hgen W a := by
  have h : ∃ s : Γ(Y, W), ∃ (hX : IsIntegral X) (hY : IsIntegral Y) (hW : Nonempty W)
      (hgen : π.base (genericPoint X) = genericPoint Y), Y.germToFunctionField W s = normGerm π hgen W a := by
    obtain ⟨s, hs⟩ := hex
    exact ⟨s, inferInstance, inferInstance, inferInstance, hgen, hs⟩
  rw [Nf, dif_pos h]
  obtain ⟨_, _, _, _, hs⟩ := h.choose_spec
  exact hs

section Existence

variable (π : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsFinite π] [Surjective π]

theorem exists_germ_eq_normGerm_of_isAffineOpen (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (hic : IsIntegrallyClosed Γ(Y, V)) (b : Γ(X, π ⁻¹ᵁ V)) :
    ∃ s : Γ(Y, V), Y.germToFunctionField V s = normGerm π (base_genericPoint_eq_of_surjective π) V b := by
  have hgen := base_genericPoint_eq_of_surjective π
  haveI : Nonempty (π ⁻¹ᵁ V) := nonempty_preimage hgen V
  letI : Algebra Y.functionField X.functionField := (fieldMap π hgen).toAlgebra

  letI algAB : Algebra Γ(Y, V) Γ(X, π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  letI algAL : Algebra Γ(Y, V) X.functionField :=
    ((X.germToFunctionField (π ⁻¹ᵁ V)).hom.comp (π.app V).hom).toAlgebra
  haveI : IsScalarTower Γ(Y, V) Γ(X, π ⁻¹ᵁ V) X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(Y, V) Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show (X.germToFunctionField (π ⁻¹ᵁ V)) (π.app V a) = fieldMap π hgen (Y.germToFunctionField V a)
    exact germ_app hgen V a
  haveI : Module.Finite Γ(Y, V) Γ(X, π ⁻¹ᵁ V) :=
    RingHom.finite_algebraMap.mp (IsFinite.finite_app π V hV)
  haveI : Algebra.IsIntegral Γ(Y, V) Γ(X, π ⁻¹ᵁ V) := Algebra.IsIntegral.of_finite _ _
  haveI : IsFractionRing Γ(Y, V) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y V hV
  obtain ⟨N, hN⟩ := Algebra.exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed
    (A := Γ(Y, V)) (B := Γ(X, π ⁻¹ᵁ V)) Y.functionField X.functionField
  exact ⟨N b, hN b⟩

theorem exists_germ_eq_normGerm (hic : ∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U))
    (W : Y.Opens) [Nonempty W] (a : Γ(X, π ⁻¹ᵁ W)) :
    ∃ s : Γ(Y, W), Y.germToFunctionField W s = normGerm π (base_genericPoint_eq_of_surjective π) W a := by
  have hgen := base_genericPoint_eq_of_surjective π

  let ι : Type u := {V : Y.Opens // IsAffineOpen V ∧ V ≤ W ∧ Nonempty V}
  let V : ι → Y.Opens := fun i => i.1
  haveI hVi : ∀ i, Nonempty (V i) := fun i => i.2.2.2
  have hcov : iSup V = W := by
    apply le_antisymm (iSup_le fun i => i.2.2.1)
    intro y hy
    obtain ⟨U, hU, hyU, hUW⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)) hy
    exact Opens.mem_iSup.mpr ⟨⟨U, hU, hUW, ⟨⟨y, hyU⟩⟩⟩, hyU⟩

  have hs : ∀ i, ∃ s : Γ(Y, V i), Y.germToFunctionField (V i) s = normGerm π hgen W a := by
    intro i
    obtain ⟨s, hs⟩ := exists_germ_eq_normGerm_of_isAffineOpen π (V i) i.2.1 (hic _ i.2.1)
      (X.presheaf.map (homOfLE (π.preimage_mono i.2.2.1)).op a)
    exact ⟨s, by rw [hs, normGerm_res hgen i.2.2.1]⟩
  choose s hs using hs
  obtain ⟨t, ⟨ht, -⟩, -⟩ := Scheme.existsUnique_germToFunctionField_eq_of_iSup_eq V W hcov
    (normGerm π hgen W a) s hs
  exact ⟨t, ht⟩

end Existence

section Affine

variable (π : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsFinite π] [Surjective π]

theorem isLocalization_functionField (W : Y.Opens) (hW : IsAffineOpen W) [Nonempty W] [Nonempty (π ⁻¹ᵁ W)]
    (hinj : Function.Injective (π.app W)) :
    letI := (π.app W).hom.toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid Γ(X, π ⁻¹ᵁ W) (nonZeroDivisors Γ(Y, W))) X.functionField := by
  letI algAB : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
  replace hinj : Function.Injective (algebraMap Γ(Y, W) Γ(X, π ⁻¹ᵁ W)) := hinj
  have hW' : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  haveI : IsFractionRing Γ(X, π ⁻¹ᵁ W) X.functionField := functionField_isFractionRing_of_isAffineOpen X _ hW'
  haveI : Module.Finite Γ(Y, W) Γ(X, π ⁻¹ᵁ W) :=
    RingHom.finite_algebraMap.mp (IsFinite.finite_app π W hW)
  haveI : Algebra.IsIntegral Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsAlgebraic Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := Algebra.IsIntegral.isAlgebraic
  refine (IsLocalization.iff_of_le_of_exists_dvd
    (Algebra.algebraMapSubmonoid Γ(X, π ⁻¹ᵁ W) (nonZeroDivisors Γ(Y, W))) (nonZeroDivisors Γ(X, π ⁻¹ᵁ W))
    ?_ ?_).mpr inferInstance
  · rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    rw [map_ne_zero_iff _ hinj]
    exact nonZeroDivisors.ne_zero hr
  · intro n hn
    obtain ⟨r, hr, hdvd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := Γ(Y, W)) n).exists_nonzero_dvd hn
    exact ⟨algebraMap _ _ r, ⟨r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩, hdvd⟩

theorem germ_norm_eq_normGerm (W : Y.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (hfree : letI := (π.app W).hom.toAlgebra; Module.Free Γ(Y, W) Γ(X, π ⁻¹ᵁ W))
    (hfin : letI := (π.app W).hom.toAlgebra; Module.Finite Γ(Y, W) Γ(X, π ⁻¹ᵁ W)) (a : Γ(X, π ⁻¹ᵁ W)) :
    letI := (π.app W).hom.toAlgebra
    Y.germToFunctionField W (Algebra.norm Γ(Y, W) a) = normGerm π (base_genericPoint_eq_of_surjective π) W a := by
  have hgen := base_genericPoint_eq_of_surjective π
  haveI : Nonempty (π ⁻¹ᵁ W) := nonempty_preimage hgen W
  letI algAB : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
  haveI := hfree
  haveI := hfin
  have hinj : Function.Injective (π.app W) := FaithfulSMul.algebraMap_injective Γ(Y, W) Γ(X, π ⁻¹ᵁ W)
  letI : Algebra Y.functionField X.functionField := (fieldMap π hgen).toAlgebra
  letI algAL : Algebra Γ(Y, W) X.functionField :=
    ((X.germToFunctionField (π ⁻¹ᵁ W)).hom.comp (π.app W).hom).toAlgebra
  haveI : IsScalarTower Γ(Y, W) Γ(X, π ⁻¹ᵁ W) X.functionField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(Y, W) Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show (X.germToFunctionField (π ⁻¹ᵁ W)) (π.app W a) = fieldMap π hgen (Y.germToFunctionField W a)
    exact germ_app hgen W a
  haveI : IsFractionRing Γ(Y, W) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y W hW
  haveI := isLocalization_functionField π W hW hinj
  rw [normGerm_def]
  exact (Algebra.norm_localization Γ(Y, W) (nonZeroDivisors Γ(Y, W)) (Rₘ := Y.functionField)
    (Sₘ := X.functionField) a).symm

end Affine

end AlgebraicGeometry.NormSections

open AlgebraicGeometry.NormSections in
theorem solution :
    ∃ Nf : ∀ ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) (W : Y.Opens), Γ(X, π ⁻¹ᵁ W) → Γ(Y, W),
      ∀ ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →

        (∀ W : Y.Opens, Nf π W 1 = 1 ∧ ∀ a b : Γ(X, π ⁻¹ᵁ W), Nf π W (a * b) = Nf π W a * Nf π W b) ∧

        (∀ (W W' : Y.Opens) (h : W' ≤ W) (a : Γ(X, π ⁻¹ᵁ W)),
          Nf π W' (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π h)).op a) =
            Y.presheaf.map (homOfLE h).op (Nf π W a)) ∧

        (∀ (W : Y.Opens), IsAffineOpen W →
          letI : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
          ∀ [Module.Free Γ(Y, W) Γ(X, π ⁻¹ᵁ W)] [Module.Finite Γ(Y, W) Γ(X, π ⁻¹ᵁ W)],
          ∀ a : Γ(X, π ⁻¹ᵁ W), Nf π W a = Algebra.norm Γ(Y, W) a) ∧

        (∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' π' π g),
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ (W : Y.Opens) (a : Γ(X, π ⁻¹ᵁ W)),
            Nf π' (g ⁻¹ᵁ W) (X'.presheaf.map (eqToHom (show π' ⁻¹ᵁ (g ⁻¹ᵁ W) = g' ⁻¹ᵁ (π ⁻¹ᵁ W) by
                rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w])).op
              ((g'.app (π ⁻¹ᵁ W)).hom a)) =
            (g.app W).hom (Nf π W a)) := by
  refine ⟨Nf, ?_⟩
  intro X Y π _ _ _ _ hic
  have hgen := base_genericPoint_eq_of_surjective π

  have key : ∀ (W : Y.Opens) [Nonempty W] (a : Γ(X, π ⁻¹ᵁ W)),
      Y.germToFunctionField W (Nf π W a) = normGerm π hgen W a :=
    fun W _ a => germ_Nf hgen W a (exists_germ_eq_normGerm π hic W a)
  have inj : ∀ (W : Y.Opens) [Nonempty W], Function.Injective (Y.germToFunctionField W) :=
    fun W _ => Scheme.germToFunctionField_injective Y W
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro W
    rcases eq_bot_or_nonempty W with hW | hW
    · exact ⟨subsingleton_of_eq_bot hW _ _, fun a b => subsingleton_of_eq_bot hW _ _⟩
    · haveI := hW
      refine ⟨inj W ?_, fun a b => inj W ?_⟩
      · rw [key, normGerm_one, map_one]
      · rw [key, map_mul, key, key, normGerm_mul]
  ·
    intro W W' h a
    rcases eq_bot_or_nonempty W' with hW' | hW'
    · exact subsingleton_of_eq_bot hW' _ _
    · haveI := hW'
      haveI : Nonempty W := by obtain ⟨⟨y, hy⟩⟩ := hW'; exact ⟨⟨y, h hy⟩⟩
      apply inj W'
      rw [key, normGerm_res hgen h, germ_res, key]
  ·
    intro W hW _ _ a
    rcases eq_bot_or_nonempty W with hW0 | hW0
    · exact subsingleton_of_eq_bot hW0 _ _
    · haveI := hW0
      apply inj W
      rw [key, germ_norm_eq_normGerm π W hW inferInstance inferInstance a]
  ·
    intro X' Y' g π' g' sq _ _ _ hic' W a
    rcases eq_bot_or_nonempty (g ⁻¹ᵁ W) with hW0 | hW0
    · exact subsingleton_of_eq_bot hW0 _ _
    · haveI := hW0
      haveI : Nonempty W := by obtain ⟨⟨y, hy⟩⟩ := hW0; exact ⟨⟨g.base y, hy⟩⟩
      haveI : IsFinite π' := MorphismProperty.of_isPullback (P := @IsFinite) sq inferInstance
      haveI : Surjective π' := MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
      have hgen' := base_genericPoint_eq_of_surjective π'
      haveI : Nonempty (π ⁻¹ᵁ W) := nonempty_preimage hgen W
      haveI : Nonempty (π' ⁻¹ᵁ (g ⁻¹ᵁ W)) := nonempty_preimage hgen' (g ⁻¹ᵁ W)
      have hseam := germ_app_eq_norm_of_isPullback π g π' g' sq W a (Nf π W a) (key W a)

      have hex : ∃ s : Γ(Y', g ⁻¹ᵁ W), Y'.germToFunctionField (g ⁻¹ᵁ W) s = normGerm π' hgen' (g ⁻¹ᵁ W)
          (X'.presheaf.map (eqToHom (show π' ⁻¹ᵁ (g ⁻¹ᵁ W) = g' ⁻¹ᵁ (π ⁻¹ᵁ W) by
            rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w])).op ((g'.app (π ⁻¹ᵁ W)).hom a)) :=
        ⟨(g.app W).hom (Nf π W a), by rw [normGerm_def]; exact hseam⟩
      apply Scheme.germToFunctionField_injective Y' (g ⁻¹ᵁ W)
      rw [germ_Nf hgen' (g ⁻¹ᵁ W) _ hex, normGerm_def]
      exact hseam.symm

end S_AlgebraicGeometry_Scheme_exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed (solution)
