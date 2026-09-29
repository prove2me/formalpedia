-- Prove2me | solution 1 for AlgebraicGeometry.DescentCharacter.hasValue_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/07f55719-fa36-5912-a21b-484dd488014f

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensor_hom_ext_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_tensor
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.DescentCharacter"

namespace TV22

open TopologicalSpace Opposite

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

noncomputable abbrev resTop (r : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top (a := U))).op r

noncomputable def smulLin (r : Γ(X, ⊤)) (P : X.Modules) (U : X.Opens) : Γ(P, U) →ₗ[Γ(X, U)] Γ(P, U) :=
  DistribSMul.toLinearMap Γ(X, U) Γ(P, U) (resTop r U)

@[scoped simp] theorem smulLin_apply (r : Γ(X, ⊤)) (P : X.Modules) (U : X.Opens) (s : Γ(P, U)) :
    smulLin r P U s = resTop r U • s := rfl

theorem smul_eq (P : X.Modules) (U : (Opens X)ᵒᵖ) (a : X.ringCatSheaf.obj.obj U) (x : P.val.obj U) :
    (show Γ(P, U.unop) from (a • x : P.val.obj U)) =
      (show Γ(X, U.unop) from a) • (show Γ(P, U.unop) from x) := rfl

noncomputable def scalarEnd (r : Γ(X, ⊤)) (P : X.Modules) : P ⟶ P :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (smulLin r P U.unop).toAddMonoidHom
      naturality := by
        intro U V i
        ext s
        change (resTop r V.unop • (show Γ(P, V.unop) from P.presheaf.map i (show Γ(P, U.unop) from s)) :
            Γ(P, V.unop)) =
          (show Γ(P, V.unop) from P.presheaf.map i (resTop r U.unop • (show Γ(P, U.unop) from s)))
        have hi : i = (i.unop).op := rfl
        rw [hi, Scheme.Modules.map_smul, ← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
        rfl }
    (fun U a x => by
      change resTop r U.unop • (show Γ(P, U.unop) from (a • x : P.val.obj U)) =
        (show Γ(P, U.unop) from (a • (show P.val.obj U from resTop r U.unop • (show Γ(P, U.unop) from x)) :
          P.val.obj U))
      rw [smul_eq, smul_eq, smul_smul, smul_smul, mul_comm])⟩

theorem scalarEnd_app (r : Γ(X, ⊤)) (P : X.Modules) (U : X.Opens) (s : Γ(P, U)) :
    (scalarEnd r P).app U s = resTop r U • s := rfl

noncomputable abbrev bconst (f : X ⟶ Spec (CommRingCat.of R)) (c : R) : Γ(X, ⊤) :=
  f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)

theorem baseSection_eq (f : X ⟶ Spec (CommRingCat.of R)) (c : R) (U : X.Opens) :
    baseSection f c U = resTop (bconst f c) U := rfl

theorem isBaseScalar_scalarEnd (f : X ⟶ Spec (CommRingCat.of R)) (c : R) (P : X.Modules) :
    IsBaseScalar f (scalarEnd (bconst f c) P) c :=
  fun _ _ => rfl

theorem eq_scalarEnd (f : X ⟶ Spec (CommRingCat.of R)) {P : X.Modules} {σ : P ⟶ P} {c : R} (h : IsBaseScalar f σ c) :
    σ = scalarEnd (bconst f c) P := by
  ext U s
  exact h U s

theorem scalarEnd_comm (r : Γ(X, ⊤)) {P Q : X.Modules} (φ : P ⟶ Q) : φ ≫ scalarEnd r Q = scalarEnd r P ≫ φ := by
  ext U s
  change (scalarEnd r Q).app U (φ.app U s) = φ.app U ((scalarEnd r P).app U s)
  rw [scalarEnd_app, scalarEnd_app, Scheme.Modules.Hom.app_smul]

theorem scalarEnd_tensor (r r' : Γ(X, ⊤)) (P Q : X.Modules) :
    (scalarEnd r P ⊗ₘ scalarEnd r' Q) = scalarEnd (r * r') (P ⊗ Q) := by
  apply AlgebraicGeometry.Scheme.Modules.tensor_hom_ext_monoidalV2
  intro U p q
  rw [AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections_monoidalV2, scalarEnd_app, scalarEnd_app, scalarEnd_app,
    Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right, smul_smul]
  congr 1
  simp only [resTop, map_mul]

theorem isBaseScalar_conj (f : X ⟶ Spec (CommRingCat.of R)) {P Q : X.Modules} (e : Q ≅ P) {σ : P ⟶ P} {c : R}
    (h : IsBaseScalar f σ c) : IsBaseScalar f (e.hom ≫ σ ≫ e.inv) c := by
  rw [eq_scalarEnd f h, ← Category.assoc, scalarEnd_comm, Category.assoc, e.hom_inv_id, Category.comp_id]
  exact isBaseScalar_scalarEnd f c Q

theorem isBaseScalar_tensor (f : X ⟶ Spec (CommRingCat.of R)) {P Q : X.Modules} {σ : P ⟶ P} {τ : Q ⟶ Q} {c c' : R}
    (hσ : IsBaseScalar f σ c) (hτ : IsBaseScalar f τ c') : IsBaseScalar f (σ ⊗ₘ τ) (c * c') := by
  rw [eq_scalarEnd f hσ, eq_scalarEnd f hτ, scalarEnd_tensor]
  have : bconst f c * bconst f c' = bconst f (c * c') := by
    simp only [bconst, ← map_mul]
  rw [this]
  exact isBaseScalar_scalarEnd f (c * c') _

theorem pullbackCongr_app_tensorObj {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (M N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).app (M ⊗ N) =
      Scheme.Modules.pullbackTensorObjIso f₁ M N ≪≫
        ((Scheme.Modules.pullbackCongr h).app M ⊗ᵢ (Scheme.Modules.pullbackCongr h).app N) ≪≫
        (Scheme.Modules.pullbackTensorObjIso f₂ M N).symm := by
  subst h
  ext
  simp [Scheme.Modules.pullbackCongr]

theorem transportIso_tensorObj {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (M M' : Y.Modules) :
    transportIso h (M ⊗ M') =
      (Scheme.Modules.pullback T).mapIso (Scheme.Modules.pullbackTensorObjIso q M M') ≪≫
        Scheme.Modules.pullbackTensorObjIso T ((Scheme.Modules.pullback q).obj M) ((Scheme.Modules.pullback q).obj M') ≪≫
        (transportIso h M ⊗ᵢ transportIso h M') ≪≫
        (Scheme.Modules.pullbackTensorObjIso q M M').symm := by
  unfold transportIso
  rw [AlgebraicGeometry.Scheme.Modules.pullbackComp_app_tensorObj T q M M', pullbackCongr_app_tensorObj h M M']
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
    tensorHom_comp_tensorHom_assoc]

theorem pullback_map_tensorHom (T : X ⟶ X) {A B A' B' : X.Modules} (φ : A ⟶ B) (ψ : A' ⟶ B') :
    (Scheme.Modules.pullback T).map (φ ⊗ₘ ψ) =
      (Scheme.Modules.pullbackTensorObjIso T A A').hom ≫ ((Scheme.Modules.pullback T).map φ ⊗ₘ (Scheme.Modules.pullback T).map ψ) ≫
        (Scheme.Modules.pullbackTensorObjIso T B B').inv := by
  have hnat := Functor.LaxMonoidal.μ_natural (Scheme.Modules.pullback T) φ ψ
  simp only [Scheme.Modules.pullbackTensorObjIso, Iso.symm_hom, Iso.symm_inv, Functor.Monoidal.μIso_hom,
    Functor.Monoidal.μIso_inv]
  symm
  rw [hnat, ← Category.assoc, Functor.Monoidal.δ_μ, Category.id_comp]

theorem discrepancy_tensor {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) {N M N' M' : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj N' ≅ (Scheme.Modules.pullback q).obj M') :
    (discrepancy h
      (Scheme.Modules.pullbackTensorObjIso q N N' ≪≫ (β ⊗ᵢ β') ≪≫ (Scheme.Modules.pullbackTensorObjIso q M M').symm)).hom =
      (Scheme.Modules.pullbackTensorObjIso q M M').hom ≫ ((discrepancy h β).hom ⊗ₘ (discrepancy h β').hom) ≫
        (Scheme.Modules.pullbackTensorObjIso q M M').inv := by
  simp only [discrepancy, translateIso, transportIso_tensorObj, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, tensorIso_hom, tensorIso_inv, Iso.trans_assoc, Category.assoc,
    Functor.map_comp, pullback_map_tensorHom]
  simp only [Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc, Category.assoc, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom]

end TV22
p2m_reactivate "P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_tensor.TV22"

open TV22 in

theorem solution
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q)
    {N M N' M' : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj N' ≅ (Scheme.Modules.pullback q).obj M')
    (c c' : R) (hβ : HasValue f h β c) (hβ' : HasValue f h β' c') :
    HasValue f h
      (Scheme.Modules.pullbackTensorObjIso q N N' ≪≫ (β ⊗ᵢ β') ≪≫ (Scheme.Modules.pullbackTensorObjIso q M M').symm)
      (c * c') := by
  show IsBaseScalar f _ _
  rw [discrepancy_tensor h β β']
  exact isBaseScalar_conj f (Scheme.Modules.pullbackTensorObjIso q M M') (isBaseScalar_tensor f hβ hβ')

end S_AlgebraicGeometry_DescentCharacter_hasValue_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_DescentCharacter_hasValue_tensor (solution)
