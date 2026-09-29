-- Prove2me | solution 1 for AlgebraicGeometry.DescentCharacter.isBaseScalar_pullback_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3fb92c0f-2ebf-5705-beb9-6a14c430fe27

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry AlgebraicGeometry.DescentCharacter

namespace KcDescCharConst

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

theorem isBaseScalar_scalarEnd {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (c : R) (P : X.Modules) :
    IsBaseScalar f (scalarEnd (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)) P) c :=
  fun _ _ => rfl

theorem app_baseSection {X' : Scheme.{u}} (g : X' ⟶ X) {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    (hg : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ)) (c : R) (U : X.Opens) :
    g.app U (baseSection f c U) = baseSection f' (φ c) (g ⁻¹ᵁ U) := by
  unfold baseSection
  have h1 : g.app U (X.presheaf.map (homOfLE (le_top (a := U))).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))) =
      X'.presheaf.map ((Opens.map g.base).map (homOfLE (le_top (a := U)))).op
        (g.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))) := by
    rw [← CategoryTheory.comp_apply, g.naturality]
    rfl
  rw [h1]
  have h2 : g.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)) =
      f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv (φ c)) := by
    rw [← CategoryTheory.comp_apply, ← Scheme.Hom.comp_appTop, hg, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
    congr 1
    have h3 := congrArg (fun k => (ConcreteCategory.hom k) c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h3
    exact h3.symm
  rw [h2]
  rfl

theorem isBaseScalar_pullback_map {X' : Scheme.{u}} (g : X' ⟶ X) {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    (hg : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    {M : X.Modules} {σ : M ⟶ M} {c : R} (hσ : IsBaseScalar f σ c) :
    IsBaseScalar f' ((Scheme.Modules.pullback g).map σ) (φ c) := by
  have key : (Scheme.Modules.pullback g).map σ =
      scalarEnd (f'.appTop ((Scheme.ΓSpecIso (CommRingCat.of R')).inv (φ c))) ((Scheme.Modules.pullback g).obj M) := by
    apply Scheme.Modules.pullback_hom_ext g
    intro U s
    rw [← Scheme.Modules.pullbackLocalSection_app, hσ U s, Scheme.Modules.pullbackLocalSection_smul,
      scalarEnd_app, app_baseSection g f f' φ hg]
    rfl
  rw [key]
  exact isBaseScalar_scalarEnd f' (φ c) _

end KcDescCharConst
p2m_reactivate "P2MW.S_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map.KcDescCharConst"

theorem solution
    {X X' : Scheme.{u}} (g : X' ⟶ X) {R R' : Type u} [CommRing R] [CommRing R']
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : R →+* R')
    (hg : g ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ))
    {M : X.Modules} {σ : M ⟶ M} {c : R} (hσ : IsBaseScalar f σ c) :
    IsBaseScalar f' ((Scheme.Modules.pullback g).map σ) (φ c) :=
  KcDescCharConst.isBaseScalar_pullback_map g f f' φ hg hσ

end S_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map
end P2MW
export P2MW.S_AlgebraicGeometry_DescentCharacter_isBaseScalar_pullback_map (solution)
