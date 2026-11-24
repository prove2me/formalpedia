-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Linear
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Linear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:05:41.266038+00:00
-- url     : https://prove2.me/theorems/c25b2e44-3386-47d6-aa18-2127965254ba
-- title:
--   Linear
-- statement:
--   Definitions and structural lemmas for Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Linear.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
universe w' w v u
section EndAction
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
noncomputable def H.endRingHom (G : Sheaf J AddCommGrpCat.{w}) (n : ℕ) :
    End G →+* AddMonoid.End (Sheaf.H.{w'} G n) where
  toFun f := Sheaf.H.map f n
  map_one' := by
    ext x
    exact Sheaf.H.map_id_apply x
  map_mul' f g := by
    ext x
    exact Sheaf.H.map_comp_apply g f x
  map_zero' := by
    ext x
    change Sheaf.H.map 0 n x = 0
    rw [Sheaf.H.map_apply, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  map_add' f g := by
    ext x
    exact Sheaf.H.map_add_apply f g x
end EndAction
section Scalar
variable {X : Scheme.{u}}
noncomputable abbrev restrictTop (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom
lemma restrictTop_restrict {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictTop V r) = restrictTop U r := by
  simp only [restrictTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl
noncomputable def smulHom (F : X.Modules) (r : Γ(X, ⊤)) : F ⟶ F :=
  ⟨PresheafOfModules.homMk
    { app := fun U => Scheme.Modules.smul (M := F) (U := U.unop) (restrictTop U.unop r)
      naturality := fun {U V} f => by
        induction U with | op U => ?_
        induction V with | op V => ?_
        ext x
        let x' : Γ(F, U) := x
        change restrictTop V r • F.presheaf.map f x' = F.presheaf.map f (restrictTop U r • x')
        rw [show f = f.unop.op from rfl, Scheme.Modules.map_smul, restrictTop_restrict] }
    (fun U s m => by
      induction U with | op U => ?_
      let m' : Γ(F, U) := m
      let s' : Γ(X, U) := s
      change restrictTop U r • (s' • m') = s' • (restrictTop U r • m')
      rw [smul_smul, smul_smul, mul_comm])⟩
lemma smulHom_app_apply (F : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) (x : Γ(F, U)) :
    (smulHom F r).app U x = restrictTop U r • x := rfl
lemma smulHom_comp {F G : X.Modules} (φ : F ⟶ G) (r : Γ(X, ⊤)) :
    smulHom F r ≫ φ = φ ≫ smulHom G r := by
  ext U x
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, smulHom_app_apply,
    Scheme.Modules.Hom.app_smul]
noncomputable def smulRingHom (F : X.Modules) : Γ(X, ⊤) →+* End F where
  toFun := smulHom F
  map_one' := by
    change smulHom F 1 = 𝟙 F
    ext U x
    simp [smulHom_app_apply]
  map_mul' r s := by
    change smulHom F (r * s) = smulHom F s ≫ smulHom F r
    ext U x
    simp only [smulHom_app_apply, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      map_mul, mul_smul]
  map_zero' := by
    change smulHom F 0 = 0
    ext U x
    simp [smulHom_app_apply]
  map_add' r s := by
    change smulHom F (r + s) = smulHom F r + smulHom F s
    ext U x
    simp [smulHom_app_apply, add_smul]
noncomputable def smulAbRingHom (F : X.Modules) : Γ(X, ⊤) →+* End (modulesAb F) where
  toFun r := (SheafOfModules.toSheaf X.ringCatSheaf).map (smulHom F r)
  map_one' := by
    rw [show smulHom F 1 = 𝟙 F from (smulRingHom F).map_one]
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_id F
  map_mul' r s := by
    rw [show smulHom F (r * s) = smulHom F s ≫ smulHom F r from (smulRingHom F).map_mul r s]
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_comp _ _
  map_zero' := by
    rw [show smulHom F 0 = 0 from (smulRingHom F).map_zero]
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_zero F F
  map_add' r s := by
    rw [show smulHom F (r + s) = smulHom F r + smulHom F s from (smulRingHom F).map_add r s]
    exact (SheafOfModules.toSheaf X.ringCatSheaf).map_add
noncomputable abbrev modulesAbMap {F G : X.Modules} (φ : F ⟶ G) : modulesAb F ⟶ modulesAb G :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map φ
lemma modulesAbMap_id (F : X.Modules) : modulesAbMap (𝟙 F) = 𝟙 (modulesAb F) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map_id F
lemma modulesAbMap_comp {F G K : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ K) :
    modulesAbMap (φ ≫ ψ) = modulesAbMap φ ≫ modulesAbMap ψ :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map_comp φ ψ
lemma smulAbRingHom_comp {F G : X.Modules} (φ : F ⟶ G) (r : Γ(X, ⊤)) :
    smulAbRingHom F r ≫ modulesAbMap φ = modulesAbMap φ ≫ smulAbRingHom G r := by
  change modulesAbMap (smulHom F r) ≫ modulesAbMap φ = modulesAbMap φ ≫ modulesAbMap (smulHom G r)
  rw [← modulesAbMap_comp, ← modulesAbMap_comp, smulHom_comp]
@[instance_reducible]
noncomputable def overAlgebra (A : CommRingCat.{u}) [X.Over (Spec A)] : Algebra A Γ(X, ⊤) :=
  ((X ↘ Spec A).appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom).toAlgebra
end Scalar
section Module
variable {X : Scheme.{u}} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]
  (A : Type*) [CommRing A] [Algebra A Γ(X, ⊤)]
noncomputable def H.actRingHom (F : X.Modules) (n : ℕ) :
    A →+* AddMonoid.End (Sheaf.H.{w'} (modulesAb F) n) :=
  ((H.endRingHom (modulesAb F) n).comp (smulAbRingHom F)).comp (algebraMap A Γ(X, ⊤))
noncomputable instance H.instModule (F : X.Modules) (n : ℕ) :
    Module A (Sheaf.H.{w'} (modulesAb F) n) :=
  Module.compHom _ (H.actRingHom A F n)
noncomputable def H.linearMap {F G : X.Modules} (φ : F ⟶ G) (n : ℕ) :
    Sheaf.H.{w'} (modulesAb F) n →ₗ[A] Sheaf.H.{w'} (modulesAb G) n where
  toFun := Sheaf.H.map.{w'} (modulesAbMap φ) n
  map_add' := map_add _
  map_smul' a x := by
    change Sheaf.H.map.{w'} _ n (Sheaf.H.map.{w'} _ n x) = Sheaf.H.map.{w'} _ n (Sheaf.H.map.{w'} _ n x)
    rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, smulAbRingHom_comp]
    rfl
noncomputable def H.moduleFunctor (n : ℕ) : X.Modules ⥤ ModuleCat.{w'} A where
  obj F := ModuleCat.of A (Sheaf.H.{w'} (modulesAb F) n)
  map φ := ModuleCat.ofHom (H.linearMap A φ n)
  map_id F := by
    ext x
    change Sheaf.H.map.{w'} (modulesAbMap (𝟙 F)) n x = x
    rw [modulesAbMap_id]
    exact Sheaf.H.map_id_apply x
  map_comp φ ψ := by
    ext x
    change Sheaf.H.map.{w'} (modulesAbMap (φ ≫ ψ)) n x = _
    rw [modulesAbMap_comp, Sheaf.H.map_comp_apply]
    rfl
end Module
end GroundTheory.Arith.SchemeCoh


