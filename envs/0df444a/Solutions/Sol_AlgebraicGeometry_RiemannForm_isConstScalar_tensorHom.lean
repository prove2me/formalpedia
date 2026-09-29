-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.isConstScalar_tensorHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/80ffbd87-9063-5518-83dd-02414e793bb7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry Opposite TensorProduct"
p2m_open "CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.map_smul Scheme.ΓSpecIso"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.hom_ext ringCatSheaf Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.comp_app Modules Opens Modules.map_smul PresheafOfModules ΓSpecIso Modules.sheafify Modules.tensorSections Modules.tensorSections_smul_left Modules.tensorSections_smul_right"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext presheaf Hom.comp_app Hom Hom.app map_smul tensor sheafify tensorIsoSheafify tensorSections tensorSections_smul_left tensorSections_smul_right"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace ConstTensor

abbrev adj (Z : Scheme.{u}) := SheafOfModules.sheafifyAdj Z.sheaf.obj Z.ringCatSheaf.property

abbrev ι (Z : Scheme.{u}) := SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property

def shUnit {Z : Scheme.{u}} (A : Z.PresheafOfModules) (W : Z.Opens) (a : A.obj (op W)) :
    Γ((Modules.sheafify Z).obj A, W) :=
  ((adj Z).unit.app A).app (op W) a

lemma sheafify_map_app_shUnit {Z : Scheme.{u}} {A A' : Z.PresheafOfModules} (g : A ⟶ A') (W : Z.Opens)
    (z : A.obj (op W)) :
    Scheme.Modules.Hom.app ((Modules.sheafify Z).map g) W (shUnit A W z) = shUnit A' W (g.app (op W) z) := by
  have h := (adj Z).unit.naturality g
  exact (congr($(h.symm).app (op W) z) :)

variable {Y : Scheme.{u}}

def cmpIso (L M : Y.Modules) : (Modules.sheafify Y).obj ((ι Y).obj L ⊗ (ι Y).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M)).symm ≪≫
    ((asIso (adj Y).counit).app L ⊗ᵢ (asIso (adj Y).counit).app M)

lemma cmpIso_hom (L M : Y.Modules) :
    (cmpIso L M).hom = δ (Modules.sheafify Y) ((ι Y).obj L) ((ι Y).obj M) ≫
      ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) := rfl

lemma tensorSections_eq (L M : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    Modules.tensorSections s t = Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))) := rfl

lemma cmpIso_hom_comp_tensorHom {L L' M M' : Y.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') :
    (cmpIso L M).hom ≫ (φ ⊗ₘ ψ) =
      (Modules.sheafify Y).map ((ι Y).map φ ⊗ₘ (ι Y).map ψ) ≫ (cmpIso L' M').hom := by
  have hφ := (adj Y).counit.naturality φ
  have hψ := (adj Y).counit.naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at hφ hψ
  have hε : ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) ≫ (φ ⊗ₘ ψ) =
      ((Modules.sheafify Y).map ((ι Y).map φ) ⊗ₘ (Modules.sheafify Y).map ((ι Y).map ψ)) ≫
        ((adj Y).counit.app L' ⊗ₘ (adj Y).counit.app M') := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
    erw [← hφ, ← hψ]
    rfl
  have hδ := Functor.OplaxMonoidal.δ_natural (Modules.sheafify Y) ((ι Y).map φ) ((ι Y).map ψ)
  rw [cmpIso_hom, cmpIso_hom, Category.assoc, hε, ← Category.assoc]
  erw [hδ]
  rw [Category.assoc]

lemma tensorHom_app_tensorSections {L L' M M' : Y.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') (V : Y.Opens)
    (s : Γ(L, V)) (t : Γ(M, V)) :
    Scheme.Modules.Hom.app (φ ⊗ₘ ψ) V (Modules.tensorSections s t) =
      Modules.tensorSections (Scheme.Modules.Hom.app φ V s) (Scheme.Modules.Hom.app ψ V t) := by
  have h := congr(Scheme.Modules.Hom.app $(cmpIso_hom_comp_tensorHom φ ψ) V
    (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h
  change Scheme.Modules.Hom.app (φ ⊗ₘ ψ) V (Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))) =
    Scheme.Modules.Hom.app (cmpIso L' M').hom V (Scheme.Modules.Hom.app
      ((Modules.sheafify Y).map ((ι Y).map φ ⊗ₘ (ι Y).map ψ)) V
      (shUnit ((ι Y).obj L ⊗ (ι Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))) at h
  rw [sheafify_map_app_shUnit] at h
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul] at h
  rw [tensorSections_eq, tensorSections_eq]
  exact h

theorem tensor_hom_ext {M P N : Y.Modules} {θ θ' : M ⊗ P ⟶ N}
    (h : ∀ (U : Y.Opens) (m : Γ(M, U)) (p : Γ(P, U)),
      Scheme.Modules.Hom.app θ U (Modules.tensorSections m p) =
        Scheme.Modules.Hom.app θ' U (Modules.tensorSections m p)) : θ = θ' := by
  rw [← cancel_epi (cmpIso M P).hom]
  apply ((adj Y).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m p
  have hV := h V.unop m p
  simp only [tensorSections_eq] at hV
  exact hV

variable {X : Scheme.{u}}

def res (r : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) := X.presheaf.map (homOfLE (le_top (a := U))).op r

lemma map_res (r : Γ(X, ⊤)) {U V : X.Opens} (i : V ⟶ U) : X.presheaf.map i.op (res r U) = res r V := by
  simp only [res, ← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

lemma res_mul (r r' : Γ(X, ⊤)) (U : X.Opens) : res (r * r') U = res r U * res r' U := by
  simp [res]

def smulHom (r : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom Γ(M, V.unop) (res r V.unop))
      naturality := fun {V W} i => by
        ext x
        have h := Scheme.Modules.map_smul M i.unop (res r V.unop) x
        rw [map_res] at h
        exact h.symm }
    (fun V a m => by
      have h : ∀ (b d : Γ(X, V.unop)) (y : Γ(M, V.unop)), b • (d • y) = d • (b • y) := fun b d y => by
        rw [← mul_smul, ← mul_smul, mul_comm]
      exact h (res r V.unop) a m)⟩

@[scoped simp] lemma smulHom_app (r : Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    Scheme.Modules.Hom.app (smulHom r M) U x = res r U • x := rfl

lemma smulHom_tensor (r r' : Γ(X, ⊤)) (M M' : X.Modules) :
    smulHom r M ⊗ₘ smulHom r' M' = smulHom (r * r') (M ⊗ M') := by
  apply tensor_hom_ext
  intro U m p
  rw [tensorHom_app_tensorSections, smulHom_app, smulHom_app, smulHom_app, Modules.tensorSections_smul_left,
    Modules.tensorSections_smul_right, ← mul_smul, res_mul]

end ConstTensor
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules.ConstTensor"

end AlgebraicGeometry.Scheme.Modules
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules.ConstTensor P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules.ConstTensor P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules.ConstTensor P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.map_smul Scheme.ΓSpecIso"
namespace RiemannForm
p2m_export "AlgebraicGeometry.RiemannForm" "IsConstScalar"
p2m_open "AlgebraicGeometry.RiemannForm AlgebraicGeometry"

open AlgebraicGeometry.Scheme.Modules.ConstTensor

namespace IsConstScalar

private lemma _root_.AlgebraicGeometry.RiemannForm.IsConstScalar.eq_smulHom {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M : A.Modules} {σ : M ⟶ M} {c : k} (h : IsConstScalar f σ c) :
    σ = smulHom (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) M := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  exact h U x

end IsConstScalar
p2m_export "AlgebraicGeometry.RiemannForm" "IsConstScalar.eq_smulHom"
end AlgebraicGeometry.RiemannForm
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules.ConstTensor P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules.ConstTensor P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules.ConstTensor P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.Scheme.Modules"

open AlgebraicGeometry.Scheme.Modules.ConstTensor _root_.AlgebraicGeometry.RiemannForm _root_.P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom.AlgebraicGeometry.RiemannForm in
theorem solution
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M M' : A.Modules} (σ : M ⟶ M) (τ : M' ⟶ M') (c c' : k)
    (hσ : IsConstScalar f σ c) (hτ : IsConstScalar f τ c') :
    IsConstScalar f (σ ⊗ₘ τ) (c * c') := by
  intro U x
  rw [hσ.eq_smulHom f, hτ.eq_smulHom f, smulHom_tensor, ← map_mul, ← map_mul]
  rfl

end S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_isConstScalar_tensorHom (solution)
