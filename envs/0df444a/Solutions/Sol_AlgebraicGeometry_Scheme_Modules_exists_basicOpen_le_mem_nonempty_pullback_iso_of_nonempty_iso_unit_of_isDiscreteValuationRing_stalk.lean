-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/229f6374-00b7-5806-8601-c7a541af99ea

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_isUnit_mul_pow_eq_mul_pow_of_isDiscreteValuationRing_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Opposite

namespace P2mA3iiiK66

theorem exists_iso_forall_app_eq_of_iSup_eq_top
    {X : Scheme.{0}} (M N : X.Modules) {ι : Type} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (f : ∀ (W : X.Opens), (∃ i, W ≤ U i) → (Γ(M, W) ≃ₗ[Γ(X, W)] Γ(N, W)))
    (hf : ∀ (W W' : X.Opens) (hW : ∃ i, W ≤ U i) (h : W' ≤ W) (x : Γ(M, W)),
      N.presheaf.map (homOfLE h).op (f W hW x) = f W' (hW.imp fun _ hi => h.trans hi) (M.presheaf.map (homOfLE h).op x)) :
    ∃ F : M ≅ N, ∀ (W : X.Opens) (hW : ∃ i, W ≤ U i) (x : Γ(M, W)), F.hom.app W x = f W hW x := by
  classical

  obtain ⟨F, hF, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top M N U hU
    (fun W hW => (f W hW).toLinearMap) (fun W W' hW h x => hf W W' hW h x)

  have hg : ∀ (W W' : X.Opens) (hW : ∃ i, W ≤ U i) (h : W' ≤ W) (y : Γ(N, W)),
      M.presheaf.map (homOfLE h).op ((f W hW).symm y) =
        (f W' (hW.imp fun _ hi => h.trans hi)).symm (N.presheaf.map (homOfLE h).op y) := by
    intro W W' hW h y
    apply (f W' (hW.imp fun _ hi => h.trans hi)).injective
    rw [LinearEquiv.apply_symm_apply, ← hf W W' hW h, LinearEquiv.apply_symm_apply]
  obtain ⟨G, hG, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top N M U hU
    (fun W hW => (f W hW).symm.toLinearMap) hg

  have uM := AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top M M U hU
    (fun W _ => LinearMap.id) (fun W W' hW h x => rfl)
  have uN := AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top N N U hU
    (fun W _ => LinearMap.id) (fun W W' hW h x => rfl)
  have h1 : F ≫ G = 𝟙 M := by
    apply uM.unique
    · intro W hW x
      rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
      simp only [LinearMap.id_coe, id_eq]
      rw [hG W hW (F.app W x), hF W hW x]
      simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    · intro W hW x
      rfl
  have h2 : G ≫ F = 𝟙 N := by
    apply uN.unique
    · intro W hW y
      rw [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
      simp only [LinearMap.id_coe, id_eq]
      rw [hF W hW (G.app W y), hG W hW y]
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    · intro W hW y
      rfl
  refine ⟨⟨F, G, h1, h2⟩, ?_⟩
  intro W hW x
  exact hF W hW x

end P2mA3iiiK66

namespace P2mA3iiiK66

section transport

variable {X : Scheme.{0}} (P : X.Modules)

theorem map_op_congr {A B : X.Opens} (i j : A ⟶ B) (x : Γ(P, B)) :
    P.presheaf.map i.op x = P.presheaf.map j.op x := by
  rw [Subsingleton.elim i j]

theorem map_op_self {A : X.Opens} (i : A ⟶ A) (x : Γ(P, A)) : P.presheaf.map i.op x = x := by
  rw [Subsingleton.elim i (𝟙 A), op_id, P.presheaf.map_id]; rfl

theorem map_op_map_op {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (x : Γ(P, C)) :
    P.presheaf.map i.op (P.presheaf.map j.op x) = P.presheaf.map (i ≫ j).op x := by
  rw [op_comp, P.presheaf.map_comp]; rfl

theorem sheaf_map_op_self {A : X.Opens} (i : A ⟶ A) (r : Γ(X, A)) : X.presheaf.map i.op r = r := by
  rw [Subsingleton.elim i (𝟙 A), op_id, X.presheaf.map_id]; rfl

theorem sheaf_map_op_map_op {A B C : X.Opens} (i : A ⟶ B) (j : B ⟶ C) (r : Γ(X, C)) :
    X.presheaf.map i.op (X.presheaf.map j.op r) = X.presheaf.map (i ≫ j).op r := by
  rw [op_comp, X.presheaf.map_comp]; rfl

end transport

section restrictIso

variable {X : Scheme.{0}} (U : X.Opens) (M N : X.Modules)

def castM (A : U.toScheme.Opens) (m : Γ(M.restrict U.ι, A)) : Γ(M, U.ι ''ᵁ A) := m

def castR (A : U.toScheme.Opens) (m : Γ(M, U.ι ''ᵁ A)) : Γ(M.restrict U.ι, A) := m

@[scoped simp] theorem castM_castR (A : U.toScheme.Opens) (m : Γ(M, U.ι ''ᵁ A)) : castM U M A (castR U M A m) = m := rfl
@[scoped simp] theorem castR_castM (A : U.toScheme.Opens) (m : Γ(M.restrict U.ι, A)) : castR U M A (castM U M A m) = m := rfl
theorem castM_add (A : U.toScheme.Opens) (a b : Γ(M.restrict U.ι, A)) : castM U M A (a + b) = castM U M A a + castM U M A b := rfl
theorem castR_add (A : U.toScheme.Opens) (a b : Γ(M, U.ι ''ᵁ A)) : castR U M A (a + b) = castR U M A a + castR U M A b := rfl

theorem castM_smul (A : U.toScheme.Opens) (s : Γ(U.toScheme, A)) (m : Γ(M.restrict U.ι, A)) :
    castM U M A (s • m) = (U.ι.appIso A).inv s • castM U M A m := rfl

variable (φ : M.restrict U.ι ⟶ N.restrict U.ι)

theorem cast_app_map {A B : U.toScheme.Opens} (k : A ⟶ B) (m : Γ(M, U.ι ''ᵁ B)) :
    castM U N A (φ.app A (castR U M A (M.presheaf.map (U.ι.opensFunctor.map k).op m))) =
      N.presheaf.map (U.ι.opensFunctor.map k).op (castM U N B (φ.app B (castR U M B m))) := by
  have h := φ.mapPresheaf.naturality k.op
  have h2 := congrArg (fun g => g (castR U M B m)) h
  simp [Scheme.Modules.mapPresheaf_app] at h2
  exact h2

theorem cast_app_smul (A : U.toScheme.Opens) (t : Γ(X, U.ι ''ᵁ A)) (m : Γ(M, U.ι ''ᵁ A)) :
    castM U N A (φ.app A (castR U M A (t • m))) = t • castM U N A (φ.app A (castR U M A m)) := by
  have h := Scheme.Modules.Hom.app_smul φ ((U.ι.appIso A).hom t) (castR U M A m)
  have e1 : ((U.ι.appIso A).hom t • castR U M A m) = castR U M A (t • m) := by
    show castR U M A ((U.ι.appIso A).inv ((U.ι.appIso A).hom t) • m) = castR U M A (t • m)
    rw [Iso.hom_inv_id_apply]
  rw [e1] at h
  rw [h]
  show (U.ι.appIso A).inv ((U.ι.appIso A).hom t) • castM U N A (φ.app A (castR U M A m)) = _
  rw [Iso.hom_inv_id_apply]

end restrictIso

theorem exists_linearEquiv_forall_app_eq_of_restrict_iso
    {X : Scheme.{0}} (U : X.Opens) (M N : X.Modules) (ψ : M.restrict U.ι ≅ N.restrict U.ι) :
    ∃ f : ∀ O : X.Opens, O ≤ U → (Γ(M, O) ≃ₗ[Γ(X, O)] Γ(N, O)),
      (∀ (O O' : X.Opens) (hO : O ≤ U) (h : O' ≤ O) (x : Γ(M, O)),
          N.presheaf.map (homOfLE h).op (f O hO x) = f O' (h.trans hO) (M.presheaf.map (homOfLE h).op x)) ∧
      (∀ (O'' : U.toScheme.Opens) (h : U.ι ''ᵁ O'' ≤ U) (x : Γ(M, U.ι ''ᵁ O'')),
          f (U.ι ''ᵁ O'') h x = ψ.hom.app O'' x) := by
  classical
  have hEq : ∀ (O : X.Opens), O ≤ U → U.ι ''ᵁ (U.ι ⁻¹ᵁ O) = O := fun O hO => by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hO]
  have hinvhom : ∀ (A : U.toScheme.Opens) (m : Γ(M.restrict U.ι, A)), ψ.inv.app A (ψ.hom.app A m) = m := by
    intro A m
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
  have hhominv : ∀ (A : U.toScheme.Opens) (n : Γ(N.restrict U.ι, A)), ψ.hom.app A (ψ.inv.app A n) = n := by
    intro A n
    rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl

  let gfun : ∀ O : X.Opens, O ≤ U → Γ(M, O) → Γ(N, O) := fun O hO x =>
    N.presheaf.map (homOfLE (hEq O hO).ge).op
      (castM U N _ (ψ.hom.app (U.ι ⁻¹ᵁ O) (castR U M _ (M.presheaf.map (homOfLE (hEq O hO).le).op x))))
  let ginv : ∀ O : X.Opens, O ≤ U → Γ(N, O) → Γ(M, O) := fun O hO y =>
    M.presheaf.map (homOfLE (hEq O hO).ge).op
      (castM U M _ (ψ.inv.app (U.ι ⁻¹ᵁ O) (castR U N _ (N.presheaf.map (homOfLE (hEq O hO).le).op y))))
  have gadd : ∀ O hO (x y : Γ(M, O)), gfun O hO (x + y) = gfun O hO x + gfun O hO y := by
    intro O hO x y
    simp only [gfun]
    rw [map_add, castR_add, map_add, castM_add, map_add]
  have gsmul : ∀ O hO (r : Γ(X, O)) (x : Γ(M, O)), gfun O hO (r • x) = r • gfun O hO x := by
    intro O hO r x
    simp only [gfun]
    rw [Scheme.Modules.map_smul, cast_app_smul, Scheme.Modules.map_smul, sheaf_map_op_map_op, sheaf_map_op_self]
  have gleft : ∀ O hO (x : Γ(M, O)), ginv O hO (gfun O hO x) = x := by
    intro O hO x
    simp only [gfun, ginv]
    rw [map_op_map_op N, map_op_self N, castR_castM, hinvhom, castM_castR, map_op_map_op M, map_op_self M]
  have gright : ∀ O hO (y : Γ(N, O)), gfun O hO (ginv O hO y) = y := by
    intro O hO y
    simp only [gfun, ginv]
    rw [map_op_map_op M, map_op_self M, castR_castM, hhominv, castM_castR, map_op_map_op N, map_op_self N]
  let f : ∀ O : X.Opens, O ≤ U → (Γ(M, O) ≃ₗ[Γ(X, O)] Γ(N, O)) := fun O hO =>
    { toFun := gfun O hO
      map_add' := gadd O hO
      map_smul' := gsmul O hO
      invFun := ginv O hO
      left_inv := gleft O hO
      right_inv := gright O hO }
  refine ⟨f, ?_, ?_⟩
  · intro O O' hO h x
    show N.presheaf.map (homOfLE h).op (gfun O hO x) = gfun O' (h.trans hO) (M.presheaf.map (homOfLE h).op x)
    simp only [gfun]
    have hk : U.ι ⁻¹ᵁ O' ≤ U.ι ⁻¹ᵁ O := Scheme.Hom.preimage_mono _ h
    rw [map_op_map_op N, map_op_map_op M,
      map_op_congr M ((homOfLE (hEq O' (h.trans hO)).le) ≫ homOfLE h)
        (U.ι.opensFunctor.map (homOfLE hk) ≫ homOfLE (hEq O hO).le),
      ← map_op_map_op M, cast_app_map, map_op_map_op N]
    exact map_op_congr N _ _ _
  · intro O'' h x
    show gfun (U.ι ''ᵁ O'') h x = ψ.hom.app O'' x
    simp only [gfun]
    have hk : U.ι ⁻¹ᵁ (U.ι ''ᵁ O'') = O'' := Scheme.Hom.preimage_image_eq _ O''
    rw [map_op_congr M (homOfLE (hEq _ h).le) (U.ι.opensFunctor.map (eqToHom hk)), cast_app_map, map_op_map_op N,
      map_op_self N]
    rfl

end P2mA3iiiK66
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk.P2mA3iiiK66"

namespace K63iii

variable {X : Scheme.{0}} (W : X.Opens)

noncomputable abbrev RU₁ : (W : Scheme.{0}).Modules :=
  Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf : X.Modules) W.ι
noncomputable abbrev RU₂ : (W : Scheme.{0}).Modules :=
  (SheafOfModules.unit (W : Scheme.{0}).ringCatSheaf : (W : Scheme.{0}).Modules)

noncomputable def φ₁₂ : (RU₁ W).val.presheaf ⟶ (RU₂ W).val.presheaf where
  app O := AddCommGrpCat.ofHom
    { toFun := fun s => (s : Γ(X, W.ι ''ᵁ O.unop))
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality U V f := by
    ext x
    rfl

noncomputable def φ₂₁ : (RU₂ W).val.presheaf ⟶ (RU₁ W).val.presheaf where
  app O := AddCommGrpCat.ofHom
    { toFun := fun s => (s : Γ(X, W.ι ''ᵁ O.unop))
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality U V f := by
    ext x
    rfl

theorem smul_eq (O : ((W : Scheme.{0}).Opens)ᵒᵖ) (r : Γ(X, W.ι ''ᵁ O.unop)) (m : Γ(X, W.ι ''ᵁ O.unop)) :
    (W.ι.appIso O.unop).inv.hom r * m = r * m := by
  rw [Scheme.Opens.ι_appIso]
  rfl

noncomputable def hom₁₂ : RU₁ W ⟶ RU₂ W :=
  ⟨PresheafOfModules.homMk (φ₁₂ W) (fun O r m => smul_eq W O r m)⟩

noncomputable def hom₂₁ : RU₂ W ⟶ RU₁ W :=
  ⟨PresheafOfModules.homMk (φ₂₁ W) (fun O r m => (smul_eq W O r m).symm)⟩

noncomputable def restrictUnitIso : RU₁ W ≅ RU₂ W where
  hom := hom₁₂ W
  inv := hom₂₁ W
  hom_inv_id := by
    apply Scheme.Modules.hom_ext; intro U; ext x; rfl
  inv_hom_id := by
    apply Scheme.Modules.hom_ext; intro U; ext x; rfl

theorem exists_restrict_unit_iso_unit {X : Scheme.{0}} (W : X.Opens) :
    ∃ ρ : Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf : X.Modules) W.ι ≅
        (SheafOfModules.unit (W : Scheme.{0}).ringCatSheaf : (W : Scheme.{0}).Modules),
      ∀ (O : (W : Scheme.{0}).Opens)
        (s : Γ(Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf : X.Modules) W.ι, O)),
        ρ.hom.app O s = (s : Γ(X, W.ι ''ᵁ O)) :=
  ⟨restrictUnitIso W, fun _ _ => rfl⟩

end K63iii
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk.P2mA3iiiK66"

namespace K63iii

theorem exists_trivSec {X : Scheme.{0}} (W : X.Opens) (M : X.Modules)
    (e : (Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit (W : Scheme.{0}).ringCatSheaf) :
    ∃ f : ∀ O : X.Opens, O ≤ W → (Γ(M, O) ≃ₗ[Γ(X, O)] Γ(X, O)),
      ∀ (O O' : X.Opens) (hO : O ≤ W) (h : O' ≤ O) (x : Γ(M, O)),
          X.presheaf.map (homOfLE h).op (f O hO x) = f O' (h.trans hO) (M.presheaf.map (homOfLE h).op x) := by
  obtain ⟨ρ, -⟩ := exists_restrict_unit_iso_unit W
  let ψ : M.restrict W.ι ≅ Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf : X.Modules) W.ι :=
    (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M ≪≫ e ≪≫ ρ.symm
  obtain ⟨f, hf, -⟩ := P2mA3iiiK66.exists_linearEquiv_forall_app_eq_of_restrict_iso W M _ ψ
  exact ⟨f, hf⟩

theorem eq_smul_gen {X : Scheme.{0}} {M : X.Modules} {O : X.Opens} (f : Γ(M, O) ≃ₗ[Γ(X, O)] Γ(X, O))
    (s : Γ(M, O)) : s = f s • f.symm 1 := by
  apply f.injective
  rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

end K63iii
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk.P2mA3iiiK66"

theorem solution
    {X : Scheme.{0}} (t : Γ(X, ⊤)) (ξ : X)
    [IsDomain (X.presheaf.stalk ξ)] [IsDiscreteValuationRing (X.presheaf.stalk ξ)]
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) = Ideal.span {X.presheaf.Γgerm ξ t})
    (L L' : X.Modules) (W : X.Opens) (hξ : ξ ∈ W)
    (hLW : Nonempty ((Scheme.Modules.pullback W.ι).obj L ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (hL'W : Nonempty ((Scheme.Modules.pullback W.ι).obj L' ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (h : Nonempty ((Scheme.Modules.pullback (X.basicOpen t).ι).obj L ≅ (Scheme.Modules.pullback (X.basicOpen t).ι).obj L')) :
    ∃ V : X.Opens, X.basicOpen t ≤ V ∧ ξ ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj L ≅ (Scheme.Modules.pullback V.ι).obj L') := by
  classical
  obtain ⟨eW⟩ := hLW
  obtain ⟨eW'⟩ := hL'W
  obtain ⟨φ⟩ := h
  set U : X.Opens := X.basicOpen t with hUdef

  let φr : L.restrict U.ι ≅ L'.restrict U.ι :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app L ≪≫ φ ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L').symm
  obtain ⟨fφ, hfφ, -⟩ := P2mA3iiiK66.exists_linearEquiv_forall_app_eq_of_restrict_iso U L L' φr
  obtain ⟨fe, hfe⟩ := K63iii.exists_trivSec W L eW
  obtain ⟨fe', hfe'⟩ := K63iii.exists_trivSec W L' eW'

  have hfe_symm : ∀ (O O' : X.Opens) (hO : O ≤ W) (hh : O' ≤ O) (r : Γ(X, O)),
      L.presheaf.map (homOfLE hh).op ((fe O hO).symm r) =
        (fe O' (hh.trans hO)).symm (X.presheaf.map (homOfLE hh).op r) := by
    intro O O' hO hh r
    apply (fe O' (hh.trans hO)).injective
    rw [LinearEquiv.apply_symm_apply, ← hfe O O' hO hh, LinearEquiv.apply_symm_apply]
  have hfe'_symm : ∀ (O O' : X.Opens) (hO : O ≤ W) (hh : O' ≤ O) (r : Γ(X, O)),
      L'.presheaf.map (homOfLE hh).op ((fe' O hO).symm r) =
        (fe' O' (hh.trans hO)).symm (X.presheaf.map (homOfLE hh).op r) := by
    intro O O' hO hh r
    apply (fe' O' (hh.trans hO)).injective
    rw [LinearEquiv.apply_symm_apply, ← hfe' O O' hO hh, LinearEquiv.apply_symm_apply]

  let uO : ∀ O : X.Opens, O ≤ W ⊓ U → Γ(X, O) := fun O hO =>
    fe' O (hO.trans inf_le_left) (fφ O (hO.trans inf_le_right) ((fe O (hO.trans inf_le_left)).symm 1))
  have huO_res : ∀ (O O' : X.Opens) (hO : O ≤ W ⊓ U) (hh : O' ≤ O),
      X.presheaf.map (homOfLE hh).op (uO O hO) = uO O' (hh.trans hO) := by
    intro O O' hO hh
    simp only [uO]
    rw [hfe', hfφ, hfe_symm, map_one]
  have huO_unit : ∀ (O : X.Opens) (hO : O ≤ W ⊓ U), IsUnit (uO O hO) := by
    intro O hO
    set u' : Γ(X, O) := fe O (hO.trans inf_le_left)
      ((fφ O (hO.trans inf_le_right)).symm ((fe' O (hO.trans inf_le_left)).symm 1)) with hu'
    refine isUnit_iff_exists_inv.mpr ⟨u', ?_⟩

    have h1 := K63iii.eq_smul_gen (fe O (hO.trans inf_le_left))
      ((fφ O (hO.trans inf_le_right)).symm ((fe' O (hO.trans inf_le_left)).symm 1))
    rw [← hu'] at h1
    have h2 := congrArg (fun s => fe' O (hO.trans inf_le_left) (fφ O (hO.trans inf_le_right) s)) h1
    simp only [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul] at h2
    rw [mul_comm]; exact h2.symm
  set u := uO (W ⊓ U) le_rfl with hudef

  obtain ⟨W', hW'W, hξ', a, b, v, hv, hE⟩ :=
    AlgebraicGeometry.Scheme.exists_isUnit_mul_pow_eq_mul_pow_of_isDiscreteValuationRing_stalk
      t ξ hmax W hξ u (huO_unit _ le_rfl)

  have resres : ∀ {O₁ O₂ O₃ : X.Opens} (h₁₂ : O₂ ≤ O₁) (h₂₃ : O₃ ≤ O₂) (x : Γ(X, O₁)),
      X.presheaf.map (homOfLE h₂₃).op (X.presheaf.map (homOfLE h₁₂).op x) =
        X.presheaf.map (homOfLE (h₂₃.trans h₁₂)).op x := by
    intro O₁ O₂ O₃ h₁₂ h₂₃ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  have resirr : ∀ {O₁ O₂ : X.Opens} (h h' : O₂ ≤ O₁) (x : Γ(X, O₁)),
      X.presheaf.map (homOfLE h).op x = X.presheaf.map (homOfLE h').op x := fun _ _ _ => rfl
  have resresL' : ∀ {O₁ O₂ O₃ : X.Opens} (h₁₂ : O₂ ≤ O₁) (h₂₃ : O₃ ≤ O₂) (x : Γ(L', O₁)),
      L'.presheaf.map (homOfLE h₂₃).op (L'.presheaf.map (homOfLE h₁₂).op x) =
        L'.presheaf.map (homOfLE (h₂₃.trans h₁₂)).op x := by
    intro O₁ O₂ O₃ h₁₂ h₂₃ x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

  have htU : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le t)).op t) := RingedSpace.isUnit_res_basicOpen _ t
  let tU : Γ(X, U)ˣ := htU.unit
  let g : Γ(X, U)ˣ := tU ^ a * (tU ^ b)⁻¹
  let resU : ∀ (O : X.Opens), O ≤ U → (Γ(X, U) →* Γ(X, O)) := fun O hO =>
    (X.presheaf.map (homOfLE hO).op).hom.toMonoidHom

  let fφ' : ∀ O : X.Opens, O ≤ U → (Γ(L, O) ≃ₗ[Γ(X, O)] Γ(L', O)) := fun O hO =>
    (fφ O hO).trans (LinearEquiv.smulOfUnit (Units.map (resU O hO) g))
  have fφ'_apply : ∀ (O : X.Opens) (hO : O ≤ U) (y : Γ(L, O)),
      fφ' O hO y = X.presheaf.map (homOfLE hO).op (g : Γ(X, U)) • fφ O hO y := fun _ _ _ => rfl
  have hfφ' : ∀ (O O' : X.Opens) (hO : O ≤ U) (hh : O' ≤ O) (x : Γ(L, O)),
      L'.presheaf.map (homOfLE hh).op (fφ' O hO x) = fφ' O' (hh.trans hO) (L.presheaf.map (homOfLE hh).op x) := by
    intro O O' hO hh x
    rw [fφ'_apply, fφ'_apply, ← hfφ O O' hO hh]
    rw [show L'.presheaf.map (homOfLE hh).op (X.presheaf.map (homOfLE hO).op (g : Γ(X, U)) • fφ O hO x) =
      X.presheaf.map (homOfLE hh).op (X.presheaf.map (homOfLE hO).op (g : Γ(X, U))) •
        L'.presheaf.map (homOfLE hh).op (fφ O hO x) from L'.val.map_smul _ _ _]
    rw [resres]

  let resW' : ∀ (O : X.Opens), O ≤ W' → (Γ(X, W') →* Γ(X, O)) := fun O hO =>
    (X.presheaf.map (homOfLE hO).op).hom.toMonoidHom
  let fv : ∀ O : X.Opens, O ≤ W' → (Γ(L, O) ≃ₗ[Γ(X, O)] Γ(L', O)) := fun O hO =>
    ((fe O (hO.trans hW'W)).trans (LinearEquiv.smulOfUnit (Units.map (resW' O hO) hv.unit))).trans
      (fe' O (hO.trans hW'W)).symm
  have fv_apply : ∀ (O : X.Opens) (hO : O ≤ W') (y : Γ(L, O)),
      fv O hO y = (fe' O (hO.trans hW'W)).symm (X.presheaf.map (homOfLE hO).op v • fe O (hO.trans hW'W) y) :=
    fun _ _ _ => rfl
  have hfv : ∀ (O O' : X.Opens) (hO : O ≤ W') (hh : O' ≤ O) (x : Γ(L, O)),
      L'.presheaf.map (homOfLE hh).op (fv O hO x) = fv O' (hh.trans hO) (L.presheaf.map (homOfLE hh).op x) := by
    intro O O' hO hh x
    rw [fv_apply, fv_apply, hfe'_symm O O' (hO.trans hW'W) hh, smul_eq_mul, smul_eq_mul, map_mul, resres,
      hfe O O' (hO.trans hW'W) hh]

  have hagree : ∀ (O : X.Opens) (hOU : O ≤ U) (hOW' : O ≤ W') (y : Γ(L, O)), fφ' O hOU y = fv O hOW' y := by
    intro O hOU hOW' y
    have hOW : O ≤ W := hOW'.trans hW'W

    rw [K63iii.eq_smul_gen (fe O hOW) y, map_smul, map_smul]
    congr 1
    rw [fφ'_apply, fv_apply, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    apply (fe' O hOW).injective
    rw [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul]

    have h1 : fe' O hOW (fφ O hOU ((fe O hOW).symm 1)) = uO O (le_inf hOW hOU) := rfl
    rw [h1, ← huO_res (W ⊓ U) O le_rfl (le_inf hOW hOU)]

    have hO₁ : O ≤ W' ⊓ X.basicOpen t := le_inf hOW' hOU
    have hE' := congrArg (X.presheaf.map (homOfLE hO₁).op) hE
    simp only [map_mul, map_pow, resres] at hE'

    have htO : X.presheaf.map (homOfLE (hO₁.trans (le_top))).op t = X.presheaf.map (homOfLE hOU).op (tU : Γ(X, U)) := by
      show _ = X.presheaf.map (homOfLE hOU).op (X.presheaf.map (homOfLE (X.basicOpen_le t)).op t)
      rw [resres]
    have hgO : X.presheaf.map (homOfLE hOU).op (g : Γ(X, U)) =
        (Units.map (resU O hOU) tU ^ a * (Units.map (resU O hOU) tU ^ b)⁻¹ : Γ(X, O)ˣ) := by
      rw [← map_pow, ← map_pow, ← map_inv, ← map_mul]
      rfl
    rw [hgO]
    have htO' : (Units.map (resU O hOU) tU : Γ(X, O)) = X.presheaf.map (homOfLE (hO₁.trans le_top)).op t := by
      rw [htO]; rfl

    set τ : Γ(X, O)ˣ := Units.map (resU O hOU) tU with hτ
    rw [htO'.symm] at hE'
    rw [resirr (hO₁.trans (inf_le_inf_right (X.basicOpen t) hW'W)) (le_inf hOW hOU)] at hE'
    rw [resirr (hO₁.trans inf_le_left) hOW'] at hE'

    rw [Units.val_mul, mul_comm, ← mul_assoc, Units.val_pow_eq_pow_val, hE', mul_assoc,
      ← Units.val_pow_eq_pow_val, Units.mul_inv, mul_one]

  let V : X.Opens := U ⊔ W'
  let S : Scheme.{0} := V
  let Uc : Bool → S.Opens := fun i => if i then V.ι ⁻¹ᵁ U else V.ι ⁻¹ᵁ W'
  have hUc : ⨆ i, Uc i = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    rw [Opens.mem_iSup]
    have hxV : V.ι.base x ∈ (V : X.Opens) := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
    rcases hxV with hx | hx
    · exact ⟨true, by simp only [Uc, if_true]; exact hx⟩
    · exact ⟨false, by simp only [Uc]; exact hx⟩
  have himU : ∀ O : S.Opens, O ≤ Uc true → V.ι ''ᵁ O ≤ U := by
    intro O hO
    rintro _ ⟨x, hx, rfl⟩
    have := hO hx
    simp [Uc] at this
    exact this
  have himW : ∀ O : S.Opens, O ≤ Uc false → V.ι ''ᵁ O ≤ W' := by
    intro O hO
    rintro _ ⟨x, hx, rfl⟩
    have := hO hx
    simp [Uc] at this
    exact this
  have hcase : ∀ O : S.Opens, (∃ i, O ≤ Uc i) → ¬ V.ι ''ᵁ O ≤ U → V.ι ''ᵁ O ≤ W' := by
    rintro O ⟨i, hi⟩ hnot
    cases i with
    | true => exact absurd (himU O hi) hnot
    | false => exact himW O hi

  let conv : ∀ (O : S.Opens), (Γ(L, V.ι ''ᵁ O) ≃ₗ[Γ(X, V.ι ''ᵁ O)] Γ(L', V.ι ''ᵁ O)) →
      (Γ(L.restrict V.ι, O) ≃ₗ[Γ(S, O)] Γ(L'.restrict V.ι, O)) := fun O e =>
    { toFun := e, invFun := e.symm, map_add' := e.map_add,
      map_smul' := fun r m => e.map_smul ((V.ι.appIso O).inv.hom r) m,
      left_inv := e.left_inv, right_inv := e.right_inv }
  have conv_apply : ∀ (O : S.Opens) (e : Γ(L, V.ι ''ᵁ O) ≃ₗ[Γ(X, V.ι ''ᵁ O)] Γ(L', V.ι ''ᵁ O))
      (x : Γ(L, V.ι ''ᵁ O)), conv O e x = e x := fun _ _ _ => rfl
  let f : ∀ (O : S.Opens), (∃ i, O ≤ Uc i) → (Γ(L.restrict V.ι, O) ≃ₗ[Γ(S, O)] Γ(L'.restrict V.ι, O)) :=
    fun O hO => conv O (if hOU : V.ι ''ᵁ O ≤ U then fφ' (V.ι ''ᵁ O) hOU else fv (V.ι ''ᵁ O) (hcase O hO hOU))
  have hf : ∀ (O O' : S.Opens) (hO : ∃ i, O ≤ Uc i) (hh : O' ≤ O) (x : Γ(L.restrict V.ι, O)),
      (L'.restrict V.ι).presheaf.map (homOfLE hh).op (f O hO x) =
        f O' (hO.imp fun _ hi => hh.trans hi) ((L.restrict V.ι).presheaf.map (homOfLE hh).op x) := by
    intro O O' hO hh x
    have hh' : V.ι ''ᵁ O' ≤ V.ι ''ᵁ O := Scheme.Hom.image_mono V.ι hh
    show L'.presheaf.map (homOfLE hh').op (conv O _ x) = conv O' _ (L.presheaf.map (homOfLE hh').op x)
    rw [conv_apply, conv_apply]
    by_cases hOU : V.ι ''ᵁ O ≤ U
    · have hO'U : V.ι ''ᵁ O' ≤ U := hh'.trans hOU
      rw [dif_pos hOU, dif_pos hO'U, hfφ']
    · by_cases hO'U : V.ι ''ᵁ O' ≤ U
      · rw [dif_neg hOU, dif_pos hO'U, hfv _ _ (hcase O hO hOU) hh',
          ← hagree _ hO'U (hh'.trans (hcase O hO hOU))]
      · rw [dif_neg hOU, dif_neg hO'U, hfv]
  obtain ⟨F, -⟩ := P2mA3iiiK66.exists_iso_forall_app_eq_of_iSup_eq_top (L.restrict V.ι) (L'.restrict V.ι) Uc hUc f hf

  refine ⟨V, le_sup_left, le_sup_right (α := X.Opens) hξ', ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app L).symm ≪≫ F ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).app L'

end S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_basicOpen_le_mem_nonempty_pullback_iso_of_nonempty_iso_unit_of_isDiscreteValuationRing_stalk (solution)
