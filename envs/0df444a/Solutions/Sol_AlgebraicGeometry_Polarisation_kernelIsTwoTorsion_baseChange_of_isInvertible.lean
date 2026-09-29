-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_baseChange_of_isInvertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/117d4532-ed9a-5850-9a52-6e3928d6f1cd

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_baseChange_of_isInvertible

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace K2TBC

theorem locIsoOnBase_unit_pullback {S' : Type u} [CommRing S'] {X X' : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of S')) (θ : X' ⟶ X) (M : X.Modules)
    (h : LocIsoOnBase g M (𝟙_ X.Modules)) :
    LocIsoOnBase (θ ≫ g) ((Scheme.Modules.pullback θ).obj M) (𝟙_ X'.Modules) := by
  intro s
  obtain ⟨U, hs, ⟨e⟩⟩ := h s
  refine ⟨U, hs, ⟨?_⟩⟩
  have hle : (θ ≫ g) ⁻¹ᵁ U ≤ θ ⁻¹ᵁ (g ⁻¹ᵁ U) := le_of_eq (Scheme.Hom.comp_preimage θ g U)
  have hρ := Scheme.Hom.resLE_comp_ι θ hle
  exact (Scheme.Modules.pullbackComp ((θ ≫ g) ⁻¹ᵁ U).ι θ).app M ≪≫
    (Scheme.Modules.pullbackCongr hρ.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (θ.resLE (g ⁻¹ᵁ U) ((θ ≫ g) ⁻¹ᵁ U) hle) (g ⁻¹ᵁ U).ι).app M).symm ≪≫
    (Scheme.Modules.pullback (θ.resLE (g ⁻¹ᵁ U) ((θ ≫ g) ⁻¹ᵁ U) hle)).mapIso e ≪≫
    (Scheme.Modules.pullback (θ.resLE (g ⁻¹ᵁ U) ((θ ≫ g) ⁻¹ᵁ U) hle)).mapIso
      (Scheme.Modules.pullbackTensorUnitObjIso (g ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (θ.resLE (g ⁻¹ᵁ U) ((θ ≫ g) ⁻¹ᵁ U) hle) ≪≫
    (Scheme.Modules.pullbackTensorUnitObjIso ((θ ≫ g) ⁻¹ᵁ U).ι).symm

theorem locIsoOnBase_unit_of_iso {S' : Type u} [CommRing S'] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of S')) {M N : X.Modules} (e : M ≅ N)
    (h : LocIsoOnBase g M (𝟙_ X.Modules)) : LocIsoOnBase g N (𝟙_ X.Modules) := by
  intro s
  obtain ⟨U, hs, ⟨e'⟩⟩ := h s
  exact ⟨U, hs, ⟨(Scheme.Modules.pullback _).mapIso e.symm ≪≫ e'⟩⟩

theorem mul_coe_congr {S : Type u} [CommRing S] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (ht : t₁ = t₂)
    {P₁ Q₁ : SchemeHomOver t₁ f} {P₂ Q₂ : SchemeHomOver t₂ f} (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst ht
  rw [Subtype.ext hP, Subtype.ext hQ]

noncomputable def pullbackTensor₃ {X Y : Scheme.{u}} (φ : X ⟶ Y) (A B C : Y.Modules) :
    (Scheme.Modules.pullback φ).obj (A ⊗ (B ⊗ C)) ≅
      (Scheme.Modules.pullback φ).obj A ⊗ ((Scheme.Modules.pullback φ).obj B ⊗ (Scheme.Modules.pullback φ).obj C) :=
  Scheme.Modules.pullbackTensorObjIso φ A (B ⊗ C) ≪≫
    whiskerLeftIso _ (Scheme.Modules.pullbackTensorObjIso φ B C)

noncomputable def pbComp {X Y Z : Scheme.{u}} (ψ : X ⟶ Y) (φ : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pullback φ).obj M) ≅ (Scheme.Modules.pullback (ψ ≫ φ)).obj M :=
  (Scheme.Modules.pullbackComp ψ φ).app M

end K2TBC

open K2TBC

theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] (ι : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (h : KernelIsTwoTorsion f L 𝓛) :
    KernelIsTwoTorsion (pullback.snd f ι) (L.baseChange ι)
      ((Scheme.Modules.pullback (pullback.fst f ι)).obj 𝓛) := by
  intro R _ t' x'

  let x : SchemeHomOver (t' ≫ ι) f := RelativeGroupLaw.baseChangePointToBase ι x'
  have hx : x.1 = x'.1 ≫ pullback.fst f ι := rfl

  let θ : pullback (pullback.snd f ι) t' ⟶ pullback f (t' ≫ ι) :=
    pullback.lift (pullback.fst (pullback.snd f ι) t' ≫ pullback.fst f ι) (pullback.snd (pullback.snd f ι) t')
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc])
  let θ' : pullback f (t' ≫ ι) ⟶ pullback (pullback.snd f ι) t' :=
    pullback.lift
      (pullback.lift (pullback.fst f (t' ≫ ι)) (pullback.snd f (t' ≫ ι) ≫ t')
        (by rw [pullback.condition, Category.assoc]))
      (pullback.snd f (t' ≫ ι)) (by rw [pullback.lift_snd])
  have hθ : θ ≫ pullback.snd f (t' ≫ ι) = pullback.snd (pullback.snd f ι) t' := pullback.lift_snd _ _ _
  have hθ' : θ' ≫ pullback.snd (pullback.snd f ι) t' = pullback.snd f (t' ≫ ι) := pullback.lift_snd _ _ _
  have hθ'θ : θ' ≫ θ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

  have hpt : (L.baseChange ι).mul t' x' x' = (L.baseChange ι).one t' ↔ L.mul (t' ≫ ι) x x = L.one (t' ≫ ι) := by
    constructor
    · intro h2
      have := congrArg (RelativeGroupLaw.baseChangePointToBase ι) h2
      simpa [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChange_one] using this
    · intro h2
      rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChange_one]
      exact congrArg _ h2

  obtain ⟨edual⟩ := h𝓛.pullback_dual_monoidalV2 (pullback.fst f ι)

  have E2 : (sliceAt (pullback.snd f ι) x' ≫ pullback.fst (pullback.snd f ι) (pullback.snd f ι)) ≫ pullback.fst f ι =
      (θ ≫ sliceAt f x) ≫ pullback.fst f f := by
    simp only [sliceAt, θ, Category.assoc, pullback.lift_fst]
  have E3 : (sliceAt (pullback.snd f ι) x' ≫ pullback.snd (pullback.snd f ι) (pullback.snd f ι)) ≫ pullback.fst f ι =
      (θ ≫ sliceAt f x) ≫ pullback.snd f f := by
    simp only [sliceAt, θ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hx]
  have E1 : (sliceAt (pullback.snd f ι) x' ≫ addMor (pullback.snd f ι) (L.baseChange ι)) ≫ pullback.fst f ι =
      (θ ≫ sliceAt f x) ≫ addMor f L := by

    have lhs : (sliceAt (pullback.snd f ι) x' ≫ addMor (pullback.snd f ι) (L.baseChange ι)) ≫ pullback.fst f ι =
        (L.mul (sliceAt (pullback.snd f ι) x' ≫ ((pullback.fst (pullback.snd f ι) (pullback.snd f ι) ≫ pullback.snd f ι) ≫ ι))
          (GoodReductionJacobian.schemeHomOverComp (sliceAt (pullback.snd f ι) x') rfl
            (RelativeGroupLaw.baseChangePointToBase ι ⟨pullback.fst (pullback.snd f ι) (pullback.snd f ι), rfl⟩))
          (GoodReductionJacobian.schemeHomOverComp (sliceAt (pullback.snd f ι) x') rfl
            (RelativeGroupLaw.baseChangePointToBase ι
              ⟨pullback.snd (pullback.snd f ι) (pullback.snd f ι), pullback.condition.symm⟩))).1 := by
      rw [← L.mul_natural]
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, addMor, RelativeGroupLaw.baseChange_mul,
        RelativeGroupLaw.baseChangePointOfBase_coe, Category.assoc, pullback.lift_fst]
    have rhs : (θ ≫ sliceAt f x) ≫ addMor f L =
        (L.mul ((θ ≫ sliceAt f x) ≫ (pullback.fst f f ≫ f))
          (GoodReductionJacobian.schemeHomOverComp (θ ≫ sliceAt f x) rfl ⟨pullback.fst f f, rfl⟩)
          (GoodReductionJacobian.schemeHomOverComp (θ ≫ sliceAt f x) rfl ⟨pullback.snd f f, pullback.condition.symm⟩)).1 := by
      rw [← L.mul_natural]
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, addMor]
    rw [lhs, rhs]
    apply mul_coe_congr L
    ·
      simp only [sliceAt, θ, Category.assoc, pullback.lift_fst_assoc]
      rw [pullback.condition]
    · simpa only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc] using E2
    · simpa only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc] using E3

  have Φ : (Scheme.Modules.pullback (sliceAt (pullback.snd f ι) x')).obj
        (mumfordBundle (pullback.snd f ι) (L.baseChange ι) ((Scheme.Modules.pullback (pullback.fst f ι)).obj 𝓛)) ≅
      (Scheme.Modules.pullback θ).obj ((Scheme.Modules.pullback (sliceAt f x)).obj (mumfordBundle f L 𝓛)) := by
    refine pullbackTensor₃ _ _ _ _ ≪≫ ?_ ≪≫ ((Scheme.Modules.pullback θ).mapIso (pullbackTensor₃ _ _ _ _) ≪≫ pullbackTensor₃ _ _ _ _).symm
    refine tensorIso ?_ (tensorIso ?_ ?_)
    · exact pbComp _ _ _ ≪≫ pbComp _ _ _ ≪≫ (Scheme.Modules.pullbackCongr E1).app 𝓛 ≪≫ (pbComp _ _ _).symm ≪≫ (pbComp _ _ _).symm
    · exact (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback _).mapIso edual.symm) ≪≫
        pbComp _ _ _ ≪≫ pbComp _ _ _ ≪≫ (Scheme.Modules.pullbackCongr E2).app _ ≪≫ (pbComp _ _ _).symm ≪≫ (pbComp _ _ _).symm
    · exact (Scheme.Modules.pullback _).mapIso ((Scheme.Modules.pullback _).mapIso edual.symm) ≪≫
        pbComp _ _ _ ≪≫ pbComp _ _ _ ≪≫ (Scheme.Modules.pullbackCongr E3).app _ ≪≫ (pbComp _ _ _).symm ≪≫ (pbComp _ _ _).symm

  rw [hpt, ← h R (t' ≫ ι) x]
  constructor
  · intro hloc

    have h1 := locIsoOnBase_unit_pullback (pullback.snd (pullback.snd f ι) t') θ' _ hloc
    rw [hθ'] at h1
    refine locIsoOnBase_unit_of_iso _ ?_ h1
    exact (Scheme.Modules.pullback θ').mapIso Φ ≪≫ pbComp θ' θ _ ≪≫
      (Scheme.Modules.pullbackCongr hθ'θ).app _ ≪≫ (Scheme.Modules.pullbackId _).app _
  · intro hloc
    have h1 := locIsoOnBase_unit_pullback (pullback.snd f (t' ≫ ι)) θ _ hloc
    rw [hθ] at h1
    exact locIsoOnBase_unit_of_iso _ Φ.symm h1

end S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_baseChange_of_isInvertible
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_baseChange_of_isInvertible (solution)
