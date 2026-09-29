-- Prove2me | solution 1 for AlgebraicGeometry.SymmRoot.exists_rigidified_symmRootPred_baseChange_of_isSymmetric_of_locIsoOnBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/b77e13f6-e9ed-5202-b9c0-8174f9e18376

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

namespace P2MW.S_AlgebraicGeometry_SymmRoot_exists_rigidified_symmRootPred_baseChange_of_isSymmetric_of_locIsoOnBase

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
    (M : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S B)))).Modules) (hM : Scheme.Modules.IsInvertible M)
    (h : IsSymmetric (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))) M ∧
        LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B))))
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S B))))).obj 𝓛)
          (M ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S B)))))).obj M)) :
    ∃ M₀ : RigidifiedLineBundle (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))).one (𝟙 _))
        (SymmRoot.ι R₀ R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ B)))),
      symmRootPred (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))).obj 𝓛) R₀ (Under.mk (CommRingCat.ofHom (algebraMap R₀ B))) M₀.L := by
  classical
  obtain ⟨hsym, hsq⟩ := h

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

  let ρ : P ⟶ AB := pullback.lift (p ≫ pullback.fst f ι₀) q (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, ht])
  have hρ₁ : ρ ≫ pullback.fst f ιB = p ≫ pullback.fst f ι₀ := pullback.lift_fst _ _ _
  have hρ₂ : ρ ≫ pullback.snd f ιB = q := pullback.lift_snd _ _ _
  have hidB : Spec.map (CommRingCat.ofHom (RingHom.id B)) = 𝟙 (Spec (CommRingCat.of B)) := by
    rw [CommRingCat.ofHom_id]; exact Spec.map_id _
  have hv : ρ ≫ pullback.snd f ιB = q ≫ Spec.map (CommRingCat.ofHom (RingHom.id B)) := by
    rw [hρ₂, hidB, Category.comp_id]

  have hom' : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of B)) (P' Q' : SchemeHomOver t' q)
      (PB QB : SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B))) (pullback.snd f ιB)),
      PB.1 = P'.1 ≫ ρ → QB.1 = Q'.1 ≫ ρ →
      (LP.mul t' P' Q').1 ≫ ρ = (LB.mul (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B))) PB QB).1 := by
    intro T t' P' Q' PB QB hPB hQB
    apply pullback.hom_ext
    ·
      rw [Category.assoc, hρ₁, ← Category.assoc]
      have h1 := congrArg Subtype.val (L₀.baseChangePointToBase_mul t t' P' Q')
      rw [RelativeGroupLaw.baseChangePointToBase_coe] at h1
      rw [h1]
      have h2 := congrArg Subtype.val
        (L.baseChangePointToBase_mul ι₀ (t' ≫ t) (RelativeGroupLaw.baseChangePointToBase t P')
          (RelativeGroupLaw.baseChangePointToBase t Q'))
      rw [RelativeGroupLaw.baseChangePointToBase_coe] at h2
      rw [h2]
      have h3 := congrArg Subtype.val
        (L.baseChangePointToBase_mul ιB (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B))) PB QB)
      rw [RelativeGroupLaw.baseChangePointToBase_coe] at h3
      rw [h3]
      apply mul_coe_congr L
      · rw [Category.assoc, ht, hidB, Category.comp_id]
      · simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hPB, hρ₁]; rfl
      · simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hQB, hρ₁]; rfl
    · have eq1 : ((LP.mul t' P' Q').1 ≫ ρ) ≫ pullback.snd f ιB = t' := by
        rw [Category.assoc, hρ₂]; exact (LP.mul t' P' Q').2
      rw [eq1, (LB.mul (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B))) PB QB).2, hidB, Category.comp_id]
  have hom : ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of B)) (P' Q' : SchemeHomOver t' q),
      (LP.mul t' P' Q').1 ≫ ρ =
        (LB.mul (t' ≫ Spec.map (CommRingCat.ofHom (RingHom.id B)))
          ⟨P'.1 ≫ ρ, by rw [Category.assoc, hv, ← Category.assoc, P'.2]⟩
          ⟨Q'.1 ≫ ρ, by rw [Category.assoc, hv, ← Category.assoc, Q'.2]⟩).1 :=
    fun T t' P' Q' => hom' T t' P' Q' _ _ rfl rfl

  have hneg : ρ ≫ negMor (pullback.snd f ιB) LB = negMor q LP ≫ ρ :=
    GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_hom (RingHom.id B) LB LP ρ hv hom

  let N : P.Modules := (Scheme.Modules.pullback ρ).obj M
  have hN : Scheme.Modules.IsInvertible N := hM.pullback ρ
  have EQ := AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence q
  have base : ∀ {M₁ M₂ : AB.Modules}, LocIsoOnBase (pullback.snd f ιB) M₁ M₂ →
      LocIsoOnBase q ((Scheme.Modules.pullback ρ).obj M₁) ((Scheme.Modules.pullback ρ).obj M₂) :=
    fun hh => AlgebraicGeometry.Polarisation.LocIsoOnBase.pullback_of_comp_eq q ρ (𝟙 _)
      (by rw [hρ₂, Category.comp_id]) hh
  have eNeg : (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (negMor (pullback.snd f ιB) LB)).obj M) ≅
      (Scheme.Modules.pullback (negMor q LP)).obj N :=
    (Scheme.Modules.pullbackComp ρ _).app M ≪≫ (Scheme.Modules.pullbackCongr hneg).app M ≪≫
      ((Scheme.Modules.pullbackComp _ ρ).app M).symm
  have hsymN : IsSymmetric q LP N := EQ.trans (ofIso q eNeg.symm) (base hsym)
  have eL : (Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback (pullback.fst f ιB)).obj 𝓛) ≅
      (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback (pullback.fst f ι₀)).obj 𝓛) :=
    (Scheme.Modules.pullbackComp ρ _).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hρ₁).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp p _).app 𝓛).symm
  have hsqN : LocIsoOnBase q ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback (pullback.fst f ι₀)).obj 𝓛))
      (N ⊗ (Scheme.Modules.pullback (negMor q LP)).obj N) :=
    EQ.trans (EQ.trans (ofIso q eL.symm) (base hsq))
      (ofIso q (Scheme.Modules.pullbackTensorObjIso ρ _ _ ≪≫ whiskerLeftIso _ eNeg))

  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R₀))) f₀ := L₀.one (𝟙 _)
  let εt : Spec (CommRingCat.of B) ⟶ P := rigSection f₀ t ε
  have hεt : εt ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hεN := hN.pullback εt
  obtain ⟨hD, ⟨eD⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hεN
  let D : (Spec (CommRingCat.of B)).Modules := Scheme.Modules.dual ((Scheme.Modules.pullback εt).obj N)
  let M₀ : RigidifiedLineBundle f₀ ε t :=
    { L := N ⊗ (Scheme.Modules.pullback q).obj D
      isInvertible := Scheme.Modules.IsInvertible.tensor_monoidalV2 hN (hD.pullback q)
      rigidified := ⟨Scheme.Modules.pullbackTensorObjIso εt _ _ ≪≫
        whiskerLeftIso _ ((Scheme.Modules.pullbackComp εt q).app D ≪≫ (Scheme.Modules.pullbackCongr hεt).app D ≪≫
          (Scheme.Modules.pullbackId _).app D) ≪≫ eD⟩ }
  refine ⟨M₀, ?_⟩
  exact AlgebraicGeometry.Polarisation.isSymmetric_locIsoOnBase_tensor_pullback_of_isInvertible LP _ N D hD hsymN hsqN

end S_AlgebraicGeometry_SymmRoot_exists_rigidified_symmRootPred_baseChange_of_isSymmetric_of_locIsoOnBase
end P2MW
export P2MW.S_AlgebraicGeometry_SymmRoot_exists_rigidified_symmRootPred_baseChange_of_isSymmetric_of_locIsoOnBase (solution)
