-- Prove2me | solution 1 for AlgebraicGeometry.DescentCharacter.hasValue_comp_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c3227ef4-39dd-5794-adb2-bc63f0a69500

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Theorems.Thm_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_comp_of_comp_eq
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

namespace KcDescCharHom

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

theorem pullbackCongr_hom_app {g g' : X ⟶ Y} (e : g = g') (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr e).hom.app M =
      eqToHom (show (Scheme.Modules.pullback g).obj M = (Scheme.Modules.pullback g').obj M by rw [e]) := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

theorem pullbackComp_comp_hom_app (T₁ T₂ : X ⟶ X) (q : X ⟶ Y) (M : Y.Modules) :
    (Scheme.Modules.pullbackComp (T₁ ≫ T₂) q).hom.app M =
      (Scheme.Modules.pullbackComp T₁ T₂).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback T₁).map ((Scheme.Modules.pullbackComp T₂ q).hom.app M) ≫
          (Scheme.Modules.pullbackComp T₁ (T₂ ≫ q)).hom.app M ≫
            eqToHom (show (Scheme.Modules.pullback (T₁ ≫ T₂ ≫ q)).obj M =
              (Scheme.Modules.pullback ((T₁ ≫ T₂) ≫ q)).obj M by rw [Category.assoc]) := by
  have assoc := congrArg (fun α => NatTrans.app α M) (Scheme.Modules.pseudofunctor_associativity T₁ T₂ q)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    eqToHom_app, Functor.comp_obj, Category.id_comp] at assoc
  rw [← Iso.app_inv, Iso.inv_comp_eq, ← Iso.app_inv, ← Functor.mapIso_inv, Iso.inv_comp_eq,
    ← Iso.app_hom, ← Category.assoc, ← Iso.trans_hom, ← Iso.eq_inv_comp] at assoc
  rw [assoc]
  erw [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_hom, Iso.app_inv]
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc]

@[reassoc]
theorem pullbackComp_congr {X' : Scheme.{u}} (f : X ⟶ X') {g g' : X' ⟶ Y} (e : g = g') (M : Y.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr e).hom.app M) ≫
        (Scheme.Modules.pullbackComp f g').hom.app M =
      (Scheme.Modules.pullbackComp f g).hom.app M ≫
        (Scheme.Modules.pullbackCongr (show f ≫ g = f ≫ g' by rw [e])).hom.app M := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

theorem transportIso_comp_hom {T₁ T₂ : X ⟶ X} {q : X ⟶ Y} (h₁ : T₁ ≫ q = q) (h₂ : T₂ ≫ q = q)
    (h₁₂ : (T₁ ≫ T₂) ≫ q = q) (M : Y.Modules) :
    (transportIso h₁₂ M).hom =
      (Scheme.Modules.pullbackComp T₁ T₂).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback T₁).map (transportIso h₂ M).hom ≫ (transportIso h₁ M).hom := by
  have key : (Scheme.Modules.pullback T₁).map ((Scheme.Modules.pullbackCongr h₂).hom.app M) ≫
      (Scheme.Modules.pullbackComp T₁ q).hom.app M ≫ (Scheme.Modules.pullbackCongr h₁).hom.app M =
      (Scheme.Modules.pullbackComp T₁ (T₂ ≫ q)).hom.app M ≫
        eqToHom (show (Scheme.Modules.pullback (T₁ ≫ T₂ ≫ q)).obj M =
          (Scheme.Modules.pullback ((T₁ ≫ T₂) ≫ q)).obj M by rw [Category.assoc]) ≫
        (Scheme.Modules.pullbackCongr h₁₂).hom.app M := by
    rw [pullbackComp_congr_assoc T₁ h₂ M]
    congr 1
    simp only [pullbackCongr_hom_app, eqToHom_trans]
  have e1 : (transportIso h₁₂ M).hom =
      (Scheme.Modules.pullbackComp T₁ T₂).inv.app ((Scheme.Modules.pullback q).obj M) ≫
        (Scheme.Modules.pullback T₁).map ((Scheme.Modules.pullbackComp T₂ q).hom.app M) ≫
          (Scheme.Modules.pullbackComp T₁ (T₂ ≫ q)).hom.app M ≫
            eqToHom (show (Scheme.Modules.pullback (T₁ ≫ T₂ ≫ q)).obj M =
              (Scheme.Modules.pullback ((T₁ ≫ T₂) ≫ q)).obj M by rw [Category.assoc]) ≫
            (Scheme.Modules.pullbackCongr h₁₂).hom.app M := by
    change (Scheme.Modules.pullbackComp (T₁ ≫ T₂) q).hom.app M ≫ (Scheme.Modules.pullbackCongr h₁₂).hom.app M = _
    rw [pullbackComp_comp_hom_app]
    try dsimp only [Functor.comp_obj]
    simp only [Category.assoc]
  rw [e1]
  simp only [transportIso, Iso.trans_hom, Iso.app_hom, Functor.map_comp]
  try dsimp only [Functor.comp_obj]
  try simp only [Category.assoc]
  try dsimp only [Functor.comp_obj] at key
  rw [key]

theorem transportIso_comp_inv {T₁ T₂ : X ⟶ X} {q : X ⟶ Y} (h₁ : T₁ ≫ q = q) (h₂ : T₂ ≫ q = q)
    (h₁₂ : (T₁ ≫ T₂) ≫ q = q) (M : Y.Modules) :
    (transportIso h₁₂ M).inv =
      (transportIso h₁ M).inv ≫ (Scheme.Modules.pullback T₁).map (transportIso h₂ M).inv ≫
        (Scheme.Modules.pullbackComp T₁ T₂).hom.app ((Scheme.Modules.pullback q).obj M) := by
  rw [← cancel_mono (transportIso h₁₂ M).hom, Iso.inv_hom_id, transportIso_comp_hom h₁ h₂ h₁₂ M]
  try dsimp only [Functor.comp_obj]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

theorem translateIso_comp {T₁ T₂ : X ⟶ X} {q : X ⟶ Y} (h₁ : T₁ ≫ q = q) (h₂ : T₂ ≫ q = q)
    (h₁₂ : (T₁ ≫ T₂) ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    translateIso h₁₂ β = translateIso h₁ (translateIso h₂ β) := by
  ext : 1
  simp only [translateIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp]
  rw [transportIso_comp_hom h₁ h₂ h₁₂ M, transportIso_comp_inv h₁ h₂ h₁₂ N]
  try dsimp only [Functor.comp_obj]
  simp only [Category.assoc]
  congr 2

  have nat := (Scheme.Modules.pullbackComp T₁ T₂).hom.naturality β.hom
  simp only [Functor.comp_map] at nat
  try dsimp only [Functor.comp_obj] at nat
  erw [← Category.assoc, ← nat, Category.assoc, Iso.hom_inv_id_app_assoc]

theorem translateIso_trans {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M P : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj P) :
    translateIso h (β ≪≫ β') = translateIso h β ≪≫ translateIso h β' := by
  ext : 1
  simp [translateIso, Functor.mapIso_trans]

theorem translateIso_eq {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M) :
    translateIso h β = β ≪≫ discrepancy h β := by
  ext : 1
  simp [discrepancy]

theorem isBaseScalar_comp (f : X ⟶ Spec (CommRingCat.of R)) {M : X.Modules} {σ σ' : M ⟶ M} {c c' : R}
    (hσ : IsBaseScalar f σ c) (hσ' : IsBaseScalar f σ' c') : IsBaseScalar f (σ ≫ σ') (c * c') := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply, hσ U s, Scheme.Modules.Hom.app_smul, hσ' U,
    smul_smul, baseSection_mul, mul_comm]

theorem isBaseScalar_conj (f : X ⟶ Spec (CommRingCat.of R)) {M M' : X.Modules} (e : M ≅ M') {σ : M ⟶ M} {c : R}
    (hσ : IsBaseScalar f σ c) : IsBaseScalar f (e.inv ≫ σ ≫ e.hom) c := by
  intro U s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, hσ U, Scheme.Modules.Hom.app_smul, ← CategoryTheory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

theorem isBaseScalar_pullback_map_self (f : X ⟶ Spec (CommRingCat.of R)) {T : X ⟶ X} (hT : T ≫ f = f)
    {M : X.Modules} {σ : M ⟶ M} {c : R} (hσ : IsBaseScalar f σ c) :
    IsBaseScalar f ((Scheme.Modules.pullback T).map σ) c := by
  have hg : T ≫ f = f ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [hT, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  exact AlgebraicGeometry.DescentCharacter.isBaseScalar_pullback_map T f f (RingHom.id R) hg hσ

theorem hasValue_comp_of_comp_eq (f : X ⟶ Spec (CommRingCat.of R))
    {T₁ T₂ : X ⟶ X} {q : X ⟶ Y} (h₁ : T₁ ≫ q = q) (h₂ : T₂ ≫ q = q) (hT₁ : T₁ ≫ f = f)
    (h₁₂ : (T₁ ≫ T₂) ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c₁ c₂ : R) (hβ₁ : HasValue f h₁ β c₁) (hβ₂ : HasValue f h₂ β c₂) :
    HasValue f h₁₂ β (c₁ * c₂) := by

  have hdisc : (discrepancy h₁₂ β).hom =
      (discrepancy h₁ β).hom ≫ (translateIso h₁ (discrepancy h₂ β)).hom := by
    have e1 : (discrepancy h₁₂ β).hom = β.inv ≫ (translateIso h₁₂ β).hom := rfl
    rw [e1, translateIso_comp h₁ h₂ h₁₂ β, translateIso_eq h₂ β, translateIso_trans, Iso.trans_hom,
      translateIso_eq h₁ β, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]

  have htr : IsBaseScalar f (translateIso h₁ (discrepancy h₂ β)).hom c₂ := by
    have hpb := isBaseScalar_pullback_map_self f hT₁ hβ₂
    have := isBaseScalar_conj f (transportIso h₁ M) hpb
    simpa [translateIso] using this
  unfold HasValue
  rw [hdisc]
  exact isBaseScalar_comp f hβ₁ htr

end KcDescCharHom

theorem solution
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T₁ T₂ : X ⟶ X} {q : X ⟶ Y} (h₁ : T₁ ≫ q = q) (h₂ : T₂ ≫ q = q) (hT₁ : T₁ ≫ f = f)
    (h₁₂ : (T₁ ≫ T₂) ≫ q = q) {N M : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (c₁ c₂ : R) (hβ₁ : HasValue f h₁ β c₁) (hβ₂ : HasValue f h₂ β c₂) :
    HasValue f h₁₂ β (c₁ * c₂) :=
  KcDescCharHom.hasValue_comp_of_comp_eq f h₁ h₂ hT₁ h₁₂ β c₁ c₂ hβ₁ hβ₂

end S_AlgebraicGeometry_DescentCharacter_hasValue_comp_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_comp_of_comp_eq (solution)
