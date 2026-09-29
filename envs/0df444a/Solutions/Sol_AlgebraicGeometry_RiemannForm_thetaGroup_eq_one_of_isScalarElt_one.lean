-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.thetaGroup.eq_one_of_isScalarElt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/cc07818d-e1e8-5d3d-bdc7-95849d17137b

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ThetaGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_eq_one_of_isScalarElt_one

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm"

noncomputable section

namespace ScalSec
set_option backward.isDefEq.respectTransparency false

section homothety
open Opposite
variable {X : Scheme.{0}}

def res (r : Γ(X, ⊤)) (U : (X.Opens)ᵒᵖ) : ↑(X.ringCatSheaf.obj.obj U) :=
  (X.ringCatSheaf.obj.map (homOfLE (le_top (a := U.unop))).op) (show ↑(X.ringCatSheaf.obj.obj (op ⊤)) from r)

theorem res_map (r : Γ(X, ⊤)) {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V) :
    X.ringCatSheaf.obj.map i (res r U) = res r V := by
  change (X.ringCatSheaf.obj.map (homOfLE (le_top (a := U.unop))).op ≫ X.ringCatSheaf.obj.map i) _ = _
  rw [← Functor.map_comp]
  rfl

theorem res_comm (r : Γ(X, ⊤)) (U : (X.Opens)ᵒᵖ) (a : ↑(X.ringCatSheaf.obj.obj U)) :
    res r U * a = a * res r U := by
  change (res r U : Γ(X, U.unop)) * (a : Γ(X, U.unop)) = (a : Γ(X, U.unop)) * (res r U : Γ(X, U.unop))
  exact @mul_comm Γ(X, U.unop) _ _ _

def homothety (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun s => (res r U) • s
          map_add' := fun a b => smul_add _ a b
          map_smul' := fun a s => by
            change res r U • (a • s) = a • (res r U • s)
            rw [smul_smul, smul_smul, res_comm] }
     naturality := fun {U V} i => by
        ext s
        change res r V • (M.val.map i s) = M.val.map i (res r U • s)
        rw [PresheafOfModules.map_smul, res_map] }⟩

def res' (r : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) := X.presheaf.map (homOfLE (le_top (a := U))).op r

theorem homothety_app (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (s : Γ(M, U)) :
    (homothety M r).app U s = res' r U • s := rfl

theorem res'_mul (r s : Γ(X, ⊤)) (U : X.Opens) : res' (r * s) U = res' r U * res' s U := by
  simp only [res', map_mul]

theorem res'_one (U : X.Opens) : res' (1 : Γ(X, ⊤)) U = 1 := by
  simp only [res', map_one]

theorem homothety_comp (M : X.Modules) (r s : Γ(X, ⊤)) :
    homothety M r ≫ homothety M s = homothety M (s * r) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change (homothety M s).app U ((homothety M r).app U m) = (homothety M (s * r)).app U m
  rw [homothety_app, homothety_app, homothety_app, smul_smul, res'_mul]

theorem homothety_one (M : X.Modules) : homothety M 1 = 𝟙 M := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change (homothety M 1).app U m = m
  rw [homothety_app, res'_one, one_smul]

def homothetyIso (M : X.Modules) (r s : Γ(X, ⊤)) (h : s * r = 1) : M ≅ M where
  hom := homothety M r
  inv := homothety M s
  hom_inv_id := by rw [homothety_comp, h, homothety_one]
  inv_hom_id := by rw [homothety_comp, mul_comm, h, homothety_one]

end homothety

section const
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

def constFun (c : k) : Γ(A, ⊤) := f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)

theorem constFun_mul (c d : k) : constFun f (c * d) = constFun f c * constFun f d := by
  simp only [constFun, map_mul]

theorem constFun_one : constFun f (1 : k) = 1 := by
  simp only [constFun, map_one]

theorem isConstScalar_homothety (M : A.Modules) (c : k) : IsConstScalar f (homothety M (constFun f c)) c :=
  fun U s => rfl

theorem isConstScalar_congr {M : A.Modules} {σ τ : M ⟶ M} {c : k} (h : σ = τ) (hσ : IsConstScalar f σ c) :
    IsConstScalar f τ c := h ▸ hσ

theorem eq_id_of_isConstScalar_one {M : A.Modules} {σ : M ⟶ M} (hσ : IsConstScalar f σ 1) : σ = 𝟙 M := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  have h := hσ U s
  rw [map_one, map_one, map_one, one_smul] at h
  exact h

variable (L : RelativeGroupLaw k f) (hc : L.IsCommutative)

theorem fib_mapId_inv_app (M : A.Modules) :
    (Scheme.Modules.fibration.mapId ⟨Opposite.op A⟩).inv.toNatTrans.app M = (Scheme.Modules.pullbackId A).inv.app M := by
  simp [Scheme.Modules.fibration, Scheme.Modules.pseudofunctor, Pseudofunctor.comp, Bicategory.Adj.forget₁,
    LocallyDiscrete.mkPseudofunctor]

def scalarFiber (M : A.Modules) (c : k) (hc0 : c ≠ 0) :
    M ≅ (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj M :=
  homothetyIso M (constFun f c) (constFun f c⁻¹) (by rw [← constFun_mul, inv_mul_cancel₀ hc0, constFun_one]) ≪≫
    ((Scheme.Modules.pullbackId A).app M).symm ≪≫
      ((Scheme.Modules.pullbackCongr (translation_toPoint_zero f L hc)).app M).symm

theorem exists_isScalarElt (M : A.Modules) (c : k) (hc0 : c ≠ 0) :
    ∃ g : thetaGroup f L hc M, thetaGroup.pt f L hc M g = 1 ∧ thetaGroup.IsScalarElt f L hc M g c := by
  refine ⟨thetaGroup.liftOfIso f L hc M 0 (scalarFiber f L hc M c hc0).symm, rfl, ⟨rfl, ?_⟩⟩
  refine isConstScalar_congr f ?_ (isConstScalar_homothety f M c)
  simp only [thetaGroup.unitReading, thetaGroup.liftOfIso_hom_fiber, scalarFiber, homothetyIso, Iso.symm_inv,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

theorem hom_eq_id (M : A.Modules) (u : modulePair (A := A) M ⟶ modulePair (A := A) M) (hB : u.base = 𝟙 A)
    (hfib : u.fiber = (Scheme.Modules.pullbackId A).inv.app M ≫ (Scheme.Modules.pullbackCongr hB).inv.app M) :
    u = 𝟙 _ := by
  obtain ⟨B, φ⟩ := u
  change B = 𝟙 A at hB
  subst hB
  change φ = _ at hfib
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (by rfl) ?_
  simp only [eqToHom_refl, Category.comp_id, Pseudofunctor.CoGrothendieck.categoryStruct_id_fiber, modulePair_base,
    modulePair_fiber, fib_mapId_inv_app]
  rw [hfib]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app]
  erw [Category.comp_id]

theorem eq_one_of_isScalarElt_one (M : A.Modules) (g : thetaGroup f L hc M)
    (hg : thetaGroup.IsScalarElt f L hc M g 1) : g = 1 := by
  obtain ⟨hpt, hσ⟩ := hg
  have hB := thetaGroup.base_eq_id_of_pt_eq_one f L hc M g hpt
  have hread : thetaGroup.unitReading M hB = 𝟙 M := eq_id_of_isConstScalar_one f hσ
  have hfib : g.1.1.hom.fiber =
      (Scheme.Modules.pullbackId A).inv.app M ≫ (Scheme.Modules.pullbackCongr hB).inv.app M := by
    have h2 : thetaGroup.unitReading M hB ≫ (Scheme.Modules.pullbackId A).inv.app M ≫
        (Scheme.Modules.pullbackCongr hB).inv.app M = g.1.1.hom.fiber := by
      simp only [thetaGroup.unitReading, Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
      erw [Category.comp_id]
    rw [← h2, hread, Category.id_comp]
  have h1 : g.1.1 = Iso.refl _ := Iso.ext (hom_eq_id M g.1.1.hom hB hfib)
  apply Subtype.ext
  exact Prod.ext h1 hpt

end const
end ScalSec

end

theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (M : A.Modules)
    (g : thetaGroup f L hc M) (h : thetaGroup.IsScalarElt f L hc M g 1) :
    g = 1 :=
  ScalSec.eq_one_of_isScalarElt_one f L hc M g h

end S_AlgebraicGeometry_RiemannForm_thetaGroup_eq_one_of_isScalarElt_one
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_thetaGroup_eq_one_of_isScalarElt_one (solution)
