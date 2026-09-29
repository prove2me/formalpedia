-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f46a1a3b-d08f-5b25-a216-d52cf0fe8c37

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SplitTorus

namespace S1C
namespace TorsorTriv

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem inv_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t a) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a) := by
  letI := G.pointGroup t'
  have h : G.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t a))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ a) = G.one t' := by
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  exact eq_inv_of_mul_eq_one_left h

end S1C.TorsorTriv

open S1C.TorsorTriv in
theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L)))
    (hν₁mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul t a b) ν₁ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).mul t
            (NeronModelInfra.schemeHomOverComp a ν₁) (NeronModelInfra.schemeHomOverComp b ν₁))
    (hν₂mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a b : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD).mul t a b) ν₂ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).mul t
            (NeronModelInfra.schemeHomOverComp a ν₂) (NeronModelInfra.schemeHomOverComp b ν₂))
    (τ : SchemeHomOver (torusStr k (s - 1)) D.toBase) (hτ : IsClosedImmersion τ.1)
    (hτker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        (NeronModelInfra.schemeHomOverComp a ν₁ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁).one t ∧
          NeronModelInfra.schemeHomOverComp a ν₂ =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂).one t) ↔
        ∃ y : SchemeHomOver t (torusStr k (s - 1)), NeronModelInfra.schemeHomOverComp y τ = a)
    (U : (pullback D₁.toBase D₂.toBase).Opens) (σ : (U : Scheme.{u}) ⟶ D.P)
    (hσ : σ ≫ pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) = U.ι) :
    ∃ e : ((pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm)) ⁻¹ᵁ U : Scheme.{u}) ≅
        pullback (U.ι ≫ pullback.fst D₁.toBase D₂.toBase ≫ D₁.toBase) (torusStr k (s - 1)),
      e.hom ≫ pullback.fst (U.ι ≫ pullback.fst D₁.toBase D₂.toBase ≫ D₁.toBase) (torusStr k (s - 1)) =
        (pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm)) ∣_ U := by

  set π : D.P ⟶ pullback D₁.toBase D₂.toBase := pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) with hπdef
  have hπ₁ : π ≫ pullback.fst _ _ = ν₁.1 := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ pullback.snd _ _ = ν₂.1 := pullback.lift_snd _ _ _
  set L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut x ε) hD with hLdef
  set L₁ := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₁ ε₁) hD₁ with hL₁def
  set L₂ := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c₂ ε₂) hD₂ with hL₂def
  have hLc : L.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative _
  haveI : Mono τ.1 := inferInstance
  set u : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := U.ι ≫ pullback.fst D₁.toBase D₂.toBase ≫ D₁.toBase
    with hudef

  have hσu : σ ≫ D.toBase = u := by
    rw [hudef, ← ν₁.2, ← hπ₁, Category.assoc, reassoc_of% hσ]

  have hVu : (π ∣_ U) ≫ u = (π ⁻¹ᵁ U).ι ≫ D.toBase := by
    rw [hudef, ← Category.assoc, morphismRestrict_ι, Category.assoc, ← ν₁.2, ← hπ₁, Category.assoc]

  set Q := pullback u (torusStr k (s - 1)) with hQdef
  set tQ : Q ⟶ Spec (CommRingCat.of k) := pullback.fst u (torusStr k (s - 1)) ≫ u with htQdef
  let aQ : SchemeHomOver tQ D.toBase := ⟨pullback.fst u (torusStr k (s - 1)) ≫ σ, by rw [Category.assoc, hσu]⟩
  let yQ : SchemeHomOver tQ (torusStr k (s - 1)) := ⟨pullback.snd u (torusStr k (s - 1)), pullback.condition.symm⟩
  let cQ : SchemeHomOver tQ D.toBase := NeronModelInfra.schemeHomOverComp yQ τ
  let mQ : SchemeHomOver tQ D.toBase := L.mul tQ aQ cQ
  have hcQ₁ : NeronModelInfra.schemeHomOverComp cQ ν₁ = L₁.one tQ := ((hτker tQ cQ).mpr ⟨yQ, rfl⟩).1
  have hcQ₂ : NeronModelInfra.schemeHomOverComp cQ ν₂ = L₂.one tQ := ((hτker tQ cQ).mpr ⟨yQ, rfl⟩).2
  have hmπ : mQ.1 ≫ π = pullback.fst u (torusStr k (s - 1)) ≫ U.ι := by
    apply pullback.hom_ext
    · have h := congrArg Subtype.val (hν₁mul tQ aQ cQ)
      rw [hcQ₁, L₁.mul_one] at h
      simp only [NeronModelInfra.schemeHomOverComp_coe] at h
      rw [Category.assoc, hπ₁, h, Category.assoc, Category.assoc, ← hπ₁, reassoc_of% hσ]
    · have h := congrArg Subtype.val (hν₂mul tQ aQ cQ)
      rw [hcQ₂, L₂.mul_one] at h
      simp only [NeronModelInfra.schemeHomOverComp_coe] at h
      rw [Category.assoc, hπ₂, h, Category.assoc, Category.assoc, ← hπ₂, reassoc_of% hσ]
  let Φ : Q ⟶ (π ⁻¹ᵁ U : Scheme.{u}) :=
    pullback.lift mQ.1 (pullback.fst u (torusStr k (s - 1))) hmπ ≫ (pullbackRestrictIsoRestrict π U).hom
  have hΦι : Φ ≫ (π ⁻¹ᵁ U).ι = mQ.1 := by
    simp only [Φ, Category.assoc, pullbackRestrictIsoRestrict_hom_ι, pullback.lift_fst]
  have hΦres : Φ ≫ (π ∣_ U) = pullback.fst u (torusStr k (s - 1)) := by
    simp only [Φ, Category.assoc, pullbackRestrictIsoRestrict_hom_morphismRestrict, pullback.lift_snd]
  have hΦt : Φ ≫ ((π ⁻¹ᵁ U).ι ≫ D.toBase) = tQ := by rw [← Category.assoc, hΦι, mQ.2]

  set tV : (π ⁻¹ᵁ U : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := (π ⁻¹ᵁ U).ι ≫ D.toBase with htVdef
  let dV : SchemeHomOver tV D.toBase := ⟨(π ⁻¹ᵁ U).ι, rfl⟩
  let sV : SchemeHomOver tV D.toBase := ⟨(π ∣_ U) ≫ σ, by rw [Category.assoc, hσu, hVu]⟩
  let kV : SchemeHomOver tV D.toBase := L.mul tV dV (L.inv tV sV)

  have hsd₁ : NeronModelInfra.schemeHomOverComp sV ν₁ = NeronModelInfra.schemeHomOverComp dV ν₁ := by
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, sV, dV, Category.assoc]
    rw [← hπ₁]
    simp only [Category.assoc, morphismRestrict_ι_assoc, reassoc_of% hσ]
  have hsd₂ : NeronModelInfra.schemeHomOverComp sV ν₂ = NeronModelInfra.schemeHomOverComp dV ν₂ := by
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, sV, dV, Category.assoc]
    rw [← hπ₂]
    simp only [Category.assoc, morphismRestrict_ι_assoc, reassoc_of% hσ]

  have hk : NeronModelInfra.schemeHomOverComp kV ν₁ = L₁.one tV ∧
      NeronModelInfra.schemeHomOverComp kV ν₂ = L₂.one tV := by
    letI := L.pointGroup tV; letI := L₁.pointGroup tV; letI := L₂.pointGroup tV
    let φ₁ : SchemeHomOver tV D.toBase →* SchemeHomOver tV D₁.toBase :=
      MonoidHom.mk' (fun a => NeronModelInfra.schemeHomOverComp a ν₁) (hν₁mul tV)
    let φ₂ : SchemeHomOver tV D.toBase →* SchemeHomOver tV D₂.toBase :=
      MonoidHom.mk' (fun a => NeronModelInfra.schemeHomOverComp a ν₂) (hν₂mul tV)
    constructor
    · change φ₁ (dV * sV⁻¹) = 1
      rw [map_mul, map_inv]
      change NeronModelInfra.schemeHomOverComp dV ν₁ * (NeronModelInfra.schemeHomOverComp sV ν₁)⁻¹ = 1
      rw [hsd₁, mul_inv_cancel]
    · change φ₂ (dV * sV⁻¹) = 1
      rw [map_mul, map_inv]
      change NeronModelInfra.schemeHomOverComp dV ν₂ * (NeronModelInfra.schemeHomOverComp sV ν₂)⁻¹ = 1
      rw [hsd₂, mul_inv_cancel]
  obtain ⟨yV, hyV⟩ := (hτker tV kV).mp hk
  let Ψ : (π ⁻¹ᵁ U : Scheme.{u}) ⟶ Q := pullback.lift (π ∣_ U) yV.1 (by rw [hVu, yV.2])
  have hΨfst : Ψ ≫ pullback.fst u (torusStr k (s - 1)) = π ∣_ U := pullback.lift_fst _ _ _
  have hΨsnd : Ψ ≫ pullback.snd u (torusStr k (s - 1)) = yV.1 := pullback.lift_snd _ _ _
  have hΨt : Ψ ≫ tQ = tV := by rw [htQdef, ← Category.assoc, hΨfst, hVu]

  have hΦd : GoodReductionJacobian.schemeHomOverComp Φ hΦt dV = mQ := Subtype.ext hΦι
  have hΦs : GoodReductionJacobian.schemeHomOverComp Φ hΦt sV = aQ := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, sV, aQ]
    rw [← Category.assoc, hΦres]
  have hΨa : GoodReductionJacobian.schemeHomOverComp Ψ hΨt aQ = sV := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, sV, aQ]
    rw [← Category.assoc, hΨfst]
  have hΨc : GoodReductionJacobian.schemeHomOverComp Ψ hΨt cQ = kV := by
    rw [← hyV]
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, cQ, yQ]
    rw [← Category.assoc, hΨsnd]

  have hΨΦ : Ψ ≫ Φ = 𝟙 _ := by
    rw [← cancel_mono (π ⁻¹ᵁ U).ι, Category.assoc, hΦι, Category.id_comp]
    have h : GoodReductionJacobian.schemeHomOverComp Ψ hΨt mQ = L.mul tV sV kV := by
      rw [← hΨa, ← hΨc]
      exact L.mul_natural tQ tV Ψ hΨt aQ cQ
    have h' := congrArg Subtype.val h
    simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h'
    rw [h']
    show (L.mul tV sV (L.mul tV dV (L.inv tV sV))).1 = dV.1
    rw [hLc.mul_comm tV dV, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul]

  have hΦΨ : Φ ≫ Ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΨfst, hΦres, Category.id_comp]
    · rw [Category.assoc, hΨsnd, Category.id_comp, ← cancel_mono τ.1, Category.assoc,
        show yV.1 ≫ τ.1 = kV.1 from congrArg Subtype.val hyV]
      have h : GoodReductionJacobian.schemeHomOverComp Φ hΦt kV = L.mul tQ mQ (L.inv tQ aQ) := by
        have h₀ := L.mul_natural tV tQ Φ hΦt dV (L.inv tV sV)
        rw [inv_natural L tV tQ Φ hΦt sV, hΦd, hΦs] at h₀
        exact h₀
      have h' := congrArg Subtype.val h
      simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h'
      rw [h']
      show (L.mul tQ (L.mul tQ aQ cQ) (L.inv tQ aQ)).1 = cQ.1
      rw [hLc.mul_comm tQ aQ cQ, L.mul_assoc, L.mul_inv_cancel, L.mul_one]
  exact ⟨⟨Ψ, Φ, hΨΦ, hΦΨ⟩, hΨfst⟩

end S_AlgebraicGeometry_RelPicard_exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_iso_preimage_restrictPair_pullback_torus_of_section_of_twoGluedSmoothCurves (solution)
