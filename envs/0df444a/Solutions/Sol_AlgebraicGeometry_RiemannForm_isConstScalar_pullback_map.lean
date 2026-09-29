-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.isConstScalar_pullback_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/84c6b2f3-1dac-57b6-8b94-9a7919bf4baa

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm Opposite

namespace ConstPullback

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

theorem homothety_comm {M N : X.Modules} (φ : M ⟶ N) (r : Γ(X, ⊤)) :
    φ ≫ homothety N r = homothety M r ≫ φ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change (homothety N r).app U (φ.app U s) = φ.app U ((homothety M r).app U s)
  rw [homothety_app, homothety_app, Scheme.Modules.Hom.app_smul]

variable {Y : Scheme.{0}} (g : X ⟶ Y)

theorem app_res' (r : Γ(Y, ⊤)) (U : Y.Opens) : g.app U (res' r U) = res' (g.appTop r) (g ⁻¹ᵁ U) := by
  change (Y.presheaf.map (homOfLE (le_top (a := U))).op ≫ g.app U) r = (g.appTop ≫ X.presheaf.map _) r
  rw [Scheme.Hom.naturality]
  rfl

theorem pushforward_map_homothety (N : X.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pushforward g).map (homothety N (g.appTop r)) =
      homothety ((Scheme.Modules.pushforward g).obj N) r := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  rw [Scheme.Modules.pushforward_map_app]
  change res' (g.appTop r) (g ⁻¹ᵁ U) • (show Γ(N, g ⁻¹ᵁ U) from s) =
    (homothety ((Scheme.Modules.pushforward g).obj N) r).app U s
  rw [← app_res']
  rfl

theorem pullback_map_homothety (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback g).map (homothety M r) =
      homothety ((Scheme.Modules.pullback g).obj M) (g.appTop r) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction g
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, pushforward_map_homothety]
  have h1 := adj.unit.naturality (homothety M r)
  dsimp at h1 ⊢
  rw [← h1]
  exact (homothety_comm (adj.unit.app M) r).symm

end ConstPullback

open ConstPullback in
theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (g : A ⟶ A) (hg : g ≫ f = f) {M : A.Modules} {σ : M ⟶ M} {c : k} (hσ : IsConstScalar f σ c) :
    IsConstScalar f ((Scheme.Modules.pullback g).map σ) c := by
  set r : Γ(A, ⊤) := f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) with hr
  have hσeq : σ = homothety M r := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext s
    exact hσ U s
  have hgr : g.appTop r = r := by
    change (f.appTop ≫ g.appTop) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) = r
    rw [← Scheme.Hom.comp_appTop, hg]
  rw [hσeq, pullback_map_homothety, hgr]
  intro U s
  exact homothety_app _ r U s

end
end S_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map (solution)
