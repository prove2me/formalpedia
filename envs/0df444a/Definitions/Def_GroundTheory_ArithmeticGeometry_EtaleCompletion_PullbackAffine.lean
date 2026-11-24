-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
-- name    : GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:24.382974+00:00
-- url     : https://prove2.me/theorems/4397d7c8-2f0c-4b57-973e-88e815399bdc
-- title:
--   Pullback Affine
-- statement:
--   Definitions and structural lemmas for Pullback Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackComp_inv_pullbackSection
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackSection_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
noncomputable def sectionLinear {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P') :
    Γ(P, ⊤) →ₗ[Γ(X, ⊤)] Γ(P', ⊤) where
  toFun := θ.app ⊤
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul θ
@[simp] lemma sectionLinear_apply {X : Scheme.{u}} {P P' : X.Modules} (θ : P ⟶ P') (x : Γ(P, ⊤)) :
    sectionLinear θ x = θ.app ⊤ x := rfl
def IsBaseChangeSection {T U : Scheme.{u}} (g : T ⟶ U) (N : U.Modules) : Prop :=
  ∀ (Q : Type u) [AddCommGroup Q] [Module Γ(T, ⊤) Q] (ψ : Γ(N, ⊤) →+ Q),
    (∀ (a : Γ(U, ⊤)) (n : Γ(N, ⊤)), ψ (a • n) = g.appTop a • ψ n) →
    ∃! ψ' : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q,
      ∀ n, ψ' (pullbackSection g N n) = ψ n
lemma IsBaseChangeSection.comp {W T U : Scheme.{u}} {f : W ⟶ T} {g : T ⟶ U} {N : U.Modules}
    (hg : IsBaseChangeSection g N)
    (hf : IsBaseChangeSection f ((Scheme.Modules.pullback g).obj N)) :
    IsBaseChangeSection (f ≫ g) N := by
  intro Q _ _ ψ hψ
  let : Module Γ(T, ⊤) Q := Module.compHom Q f.appTop.hom
  have hsm : ∀ (t : Γ(T, ⊤)) (q : Q), t • q = f.appTop t • q := fun _ _ => rfl
  obtain ⟨ψ₁, hψ₁, u₁⟩ := hg Q ψ (fun a n => by
    rw [hψ, hsm, Scheme.Hom.comp_appTop]; rfl)
  obtain ⟨ψ₂, hψ₂, u₂⟩ := hf Q ψ₁.toAddMonoidHom (fun t x => ψ₁.map_smul t x)
  let c := (Scheme.Modules.pullbackComp f g).app N
  have hc : ∀ n, c.inv.app ⊤ (pullbackSection (f ≫ g) N n) =
      pullbackSection f _ (pullbackSection g N n) :=
    pullbackComp_inv_pullbackSection f g N
  have hchi : ∀ x, c.hom.app ⊤ (c.inv.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.inv_hom_id]; rfl
  have hchi' : ∀ x, c.inv.app ⊤ (c.hom.app ⊤ x) = x := fun x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, c.hom_inv_id]; rfl
  refine ⟨ψ₂ ∘ₗ sectionLinear c.inv, fun n => ?_, fun ψ'' hψ'' => ?_⟩
  · simp only [LinearMap.comp_apply, sectionLinear_apply, hc, hψ₂]
    exact hψ₁ n
  · let χ : Γ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N), ⊤) →ₗ[Γ(W, ⊤)] Q :=
      ψ'' ∘ₗ sectionLinear c.hom
    have hχ : ∀ n, χ (pullbackSection f _ (pullbackSection g N n)) = ψ n := fun n => by
      simp only [χ, LinearMap.comp_apply, sectionLinear_apply, ← hc, hchi, hψ'']
    let χ₁ : Γ((Scheme.Modules.pullback g).obj N, ⊤) →ₗ[Γ(T, ⊤)] Q :=
      { toFun := fun x => χ (pullbackSection f _ x)
        map_add' := fun x y => by simp
        map_smul' := fun t x => by
          simp only [RingHom.id_apply]
          rw [pullbackSection_smul, map_smul, hsm] }
    have h₁ : χ₁ = ψ₁ := u₁ χ₁ hχ
    have h₂ : χ = ψ₂ := u₂ χ (fun x => congrArg (fun l => l x) h₁)
    ext x
    simp only [LinearMap.comp_apply, sectionLinear_apply, ← h₂, χ, hchi]
noncomputable def pushforwardΓIso {A R : CommRingCat.{u}} (φ : A ⟶ R) :
    moduleSpecΓFunctor (R := R) ⋙ ModuleCat.restrictScalars φ.hom ≅
      Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := A) :=
  Iso.symm (Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)))
noncomputable def pullbackTildeIso {A R : CommRingCat.{u}} (φ : A ⟶ R) :
    tilde.functor A ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor R :=
  ((tilde.adjunction (R := A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := R))).ofNatIsoRight
      (pushforwardΓIso φ))
end GroundTheory.Arith.Etale


