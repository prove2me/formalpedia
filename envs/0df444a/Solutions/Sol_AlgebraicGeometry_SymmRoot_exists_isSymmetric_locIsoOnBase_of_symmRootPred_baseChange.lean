-- Prove2me | solution 1 for AlgebraicGeometry.SymmRoot.exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/dd126bad-d415-5310-be2d-3216aa5983c6

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SymmRootFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_hom
import Theorems.Thm_AlgebraicGeometry_Polarisation_isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SymmRoot_exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation AlgebraicGeometry.SymmRoot"

namespace Rebase

theorem mul_coe_congr {S : Type} [CommRing S] {A T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ Q₁ : SchemeHomOver t₁ f} {P₂ Q₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

theorem ofIso {S' : Type} [CommRing S'] {Q : Scheme.{0}} (q : Q ⟶ Spec (CommRingCat.of S')) {M M' : Q.Modules}
    (e : M ≅ M') : LocIsoOnBase q M M' := fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e⟩⟩

end Rebase

open Rebase in
theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f) (𝓛 : A.Modules)
    (R₀ : Type) [CommRing R₀] [Algebra S R₀] (B : Type) [CommRing B] [Algebra S B] [Algebra R₀ B] [IsScalarTower S R₀ B]
    (M₀ : (pullback (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ B))))).Modules)
    (hM₀ : Scheme.Modules.IsInvertible M₀)
    (h₀ : symmRootPred (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))).obj 𝓛) R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ B))) M₀) :
    ∃ M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules, Scheme.Modules.IsInvertible M ∧
      IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))))).obj 𝓛)
          (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M) := by
  classical
  obtain ⟨hsym, hsq⟩ := (symmRootPred_iff _ _ _ _ _).mp h₀

  let ι₀ : Spec (CommRingCat.of R₀) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S R₀))
  let ιB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom (algebraMap S B))
  let A₀ := pullback f ι₀
  let f₀ : A₀ ⟶ Spec (CommRingCat.of R₀) := pullback.snd f ι₀
  let L₀ : RelativeGroupLaw R₀ f₀ := L.baseChange ι₀
  let B' : Under (CommRingCat.of R₀) := Under.mk (CommRingCat.ofHom (algebraMap R₀ B))
  let t : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R₀) := SymmRoot.ι R₀ R₀ B'
  let AB := pullback f ιB
  let P := pullback f₀ t
  let p : P ⟶ A₀ := pullback.fst f₀ t
  let q : P ⟶ Spec (CommRingCat.of B) := pullback.snd f₀ t
  let LP : RelativeGroupLaw B q := L₀.baseChange t
  let LB : RelativeGroupLaw B (pullback.snd f ιB) := L.baseChange ιB
  have ht : t ≫ ι₀ = ιB := by
    change Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom (algebraMap S R₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap S B))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext s
    change ((algebraMap R₀ B).comp (algebraMap R₀ R₀)) (algebraMap S R₀ s) = algebraMap S B s
    rw [RingHom.comp_apply, Algebra.algebraMap_self, RingHom.id_apply, ← IsScalarTower.algebraMap_apply]
  have hidB : Spec.map (CommRingCat.ofHom (RingHom.id B)) = 𝟙 (Spec (CommRingCat.of B)) := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _

  let σ₀ : AB ⟶ A₀ := pullback.lift (pullback.fst f ιB) (pullback.snd f ιB ≫ t)
    (by rw [pullback.condition, Category.assoc, ht])
  have hσ₀₁ : σ₀ ≫ pullback.fst f ι₀ = pullback.fst f ιB := pullback.lift_fst _ _ _
  have hσ₀₂ : σ₀ ≫ f₀ = pullback.snd f ιB ≫ t := pullback.lift_snd _ _ _
  let σ : AB ⟶ P := pullback.lift σ₀ (pullback.snd f ιB) hσ₀₂
  have hσ₁ : σ ≫ p = σ₀ := pullback.lift_fst _ _ _
  have hσ₂ : σ ≫ q = pullback.snd f ιB := pullback.lift_snd _ _ _
  have hσf : (σ ≫ p) ≫ pullback.fst f ι₀ = pullback.fst f ιB := by rw [hσ₁, hσ₀₁]
  have hσf' : σ ≫ pullback.fst (RelativeGroupLaw.baseChangeStr ι₀ f) t ≫ pullback.fst f ι₀ = pullback.fst f ιB := by
    rw [← Category.assoc]; exact hσf
  have hv : σ ≫ q = pullback.snd f ιB ≫ Spec.map (CommRingCat.ofHom (RingHom.id B)) := by
    rw [hσ₂, hidB, Category.comp_id]

  have hom' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of B)) (P' Q' : SchemeHomOver t' (pullback.snd f ιB))
      (PP QP : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B))) q),
      PP.1 = P'.1 ≫ σ → QP.1 = Q'.1 ≫ σ →
      (LB.mul t' P' Q').1 ≫ σ = (LP.mul (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B))) PP QP).1 := by
    intro T t' P' Q' PP QP hPP hQP
    apply pullback.hom_ext
    ·
      have r1 := congrArg Subtype.val (L₀.baseChangePointToBase_mul t _ PP QP)
      rw [RelativeGroupLaw.baseChangePointToBase_coe] at r1
      rw [Category.assoc, hσ₁, r1]
      apply pullback.hom_ext
      · have l1 := congrArg Subtype.val (L.baseChangePointToBase_mul ιB t' P' Q')
        rw [RelativeGroupLaw.baseChangePointToBase_coe] at l1
        have r2 := congrArg Subtype.val
          (L.baseChangePointToBase_mul ι₀ _ (RelativeGroupLaw.baseChangePointToBase t PP)
            (RelativeGroupLaw.baseChangePointToBase t QP))
        rw [RelativeGroupLaw.baseChangePointToBase_coe] at r2
        rw [Category.assoc, hσ₀₁, l1, r2]
        apply mul_coe_congr L
        · rw [Category.assoc, ht, hidB, Category.comp_id]
        · simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hPP, hσf']
        · simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hQP, hσf']
      · rw [Category.assoc, hσ₀₂, ← Category.assoc, (LB.mul t' P' Q').2,
          (L₀.mul ((t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B))) ≫ t)
            (RelativeGroupLaw.baseChangePointToBase t PP) (RelativeGroupLaw.baseChangePointToBase t QP)).2,
          hidB, Category.comp_id]
    · rw [Category.assoc, hσ₂, (LB.mul t' P' Q').2,
        (LP.mul (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B))) PP QP).2, hidB, Category.comp_id]
  have hom : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of B)) (P' Q' : SchemeHomOver t' (pullback.snd f ιB)),
      (LB.mul t' P' Q').1 ≫ σ =
        (LP.mul (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B)))
          ⟨P'.1 ≫ σ, by rw [Category.assoc, hv, ← Category.assoc, P'.2]⟩
          ⟨Q'.1 ≫ σ, by rw [Category.assoc, hv, ← Category.assoc, Q'.2]⟩).1 :=
    fun T t' P' Q' => hom' T t' P' Q' _ _ rfl rfl

  have hneg : σ ≫ negMor q LP = negMor (pullback.snd f ιB) LB ≫ σ :=
    GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_hom (RingHom.id B) LP LB σ hv hom

  let M : AB.Modules := (Scheme.Modules.pullback σ).obj M₀
  have hM : Scheme.Modules.IsInvertible M := hM₀.pullback σ
  have EB := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence (pullback.snd f ιB)
  have base : ∀ {M₁ M₂ : P.Modules}, LocIsoOnBase q M₁ M₂ →
      LocIsoOnBase (pullback.snd f ιB) ((Scheme.Modules.pullback σ).obj M₁) ((Scheme.Modules.pullback σ).obj M₂) :=
    fun hh => AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq (pullback.snd f ιB) σ (𝟙 _)
      (by rw [hσ₂, Category.comp_id]) hh
  have eNeg : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback (negMor q LP)).obj M₀) ≅
      (Scheme.Modules.pullback (negMor (pullback.snd f ιB) LB)).obj M :=
    (Scheme.Modules.pullbackComp σ _).app M₀ ≪≫ (Scheme.Modules.pullbackCongr hneg).app M₀ ≪≫
      ((Scheme.Modules.pullbackComp _ σ).app M₀).symm
  have eL : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback p).obj
      ((Scheme.Modules.pullback (pullback.fst f ι₀)).obj 𝓛)) ≅
      (Scheme.Modules.pullback (pullback.fst f ιB)).obj 𝓛 :=
    (Scheme.Modules.pullbackComp σ p).app _ ≪≫ (Scheme.Modules.pullbackComp (σ ≫ p) _).app 𝓛 ≪≫
      (Scheme.Modules.pullbackCongr hσf).app 𝓛
  refine ⟨M, hM, EB.trans (ofIso _ eNeg.symm) (base hsym), ?_⟩
  exact EB.trans (EB.trans (ofIso _ eL.symm) (base hsq))
    (ofIso _ (Scheme.Modules.pullbackTensorObjIso σ _ _ ≪≫ whiskerLeftIso _ eNeg))

end S_AlgebraicGeometry_SymmRoot_exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange
end P2MW
export P2MW.S_AlgebraicGeometry_SymmRoot_exists_isSymmetric_locIsoOnBase_of_symmRootPred_baseChange (solution)
