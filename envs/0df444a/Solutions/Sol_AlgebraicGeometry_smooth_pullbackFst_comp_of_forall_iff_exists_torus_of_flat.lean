-- Prove2me | solution 1 for AlgebraicGeometry.smooth_pullbackFst_comp_of_forall_iff_exists_torus_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/81acc52c-e462-5299-b20b-ba5cf285ec70

import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_SplitTorus_smoothOfRelativeDimension_torusStr
import Theorems.Thm_AlgebraicGeometry_Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_smooth_pullbackFst_comp_of_forall_iff_exists_torus_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus

namespace R3x1

set_option backward.isDefEq.respectTransparency false

section Main

variable {κ : Type u} [Field κ] {G B : Scheme.{u}} (sG : G ⟶ Spec (CommRingCat.of κ)) (sB : B ⟶ Spec (CommRingCat.of κ))
  (LG : RelativeGroupLaw κ sG) (LB : RelativeGroupLaw κ sB)
  (abq : Fin 2 → SchemeHomOver sG sB)
  (habq : ∀ (i : Fin 2) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a b : SchemeHomOver t sG),
    NeronModelInfra.schemeHomOverComp (LG.mul t a b) (abq i) =
      LB.mul t (NeronModelInfra.schemeHomOverComp a (abq i)) (NeronModelInfra.schemeHomOverComp b (abq i)))

noncomputable abbrev q : G ⟶ pullback sB sB := pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)

noncomputable abbrev e : Spec (CommRingCat.of κ) ⟶ B := (LB.one (𝟙 _)).1

theorem one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) : (LB.one t).1 = t ≫ e sB LB := by
  have := LB.one_natural (𝟙 _) t t (Category.comp_id _)
  exact (congrArg Subtype.val this).symm

include habq in

theorem comp_inv (i : Fin 2) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t sG) :
    NeronModelInfra.schemeHomOverComp (LG.inv t a) (abq i) = LB.inv t (NeronModelInfra.schemeHomOverComp a (abq i)) := by
  letI := LG.pointGroup t
  letI := LB.pointGroup t
  let φ : SchemeHomOver t sG →* SchemeHomOver t sB :=
    MonoidHom.mk' (fun a => NeronModelInfra.schemeHomOverComp a (abq i)) (habq i t)
  exact map_inv φ a

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (t' : T' ⟶ Spec (CommRingCat.of κ))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t sG) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x) = LG.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := LG.pointGroup t'
  have h : LG.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (LG.inv t x)) (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      LG.one t' := by
    rw [← LG.mul_natural, LG.inv_mul_cancel, LG.one_natural]
  exact (inv_eq_of_mul_eq_one_left (G := SchemeHomOver t' sG) h).symm

end Main

end R3x1

open R3x1 in
theorem solution
    {κ : Type u} [Field κ] [IsAlgClosed κ]
    {G B : Scheme.{u}} (sG : G ⟶ Spec (CommRingCat.of κ)) (sB : B ⟶ Spec (CommRingCat.of κ))
    (LG : RelativeGroupLaw κ sG) (LB : RelativeGroupLaw κ sB) (hsm : Smooth sG)
    (abq : Fin 2 → SchemeHomOver sG sB)

    (habq : ∀ (i : Fin 2) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a b : SchemeHomOver t sG),
      NeronModelInfra.schemeHomOverComp (LG.mul t a b) (abq i) =
        LB.mul t (NeronModelInfra.schemeHomOverComp a (abq i)) (NeronModelInfra.schemeHomOverComp b (abq i)))

    (hflat : Flat (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)))
    (hsurj : Surjective (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)))
    (hqc : QuasiCompact (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)))

    (r : ℕ) (τ : SchemeHomOver (torusStr κ r) sG) (hτ : IsClosedImmersion τ.1)
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t sG),
      (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) = LB.one t) ↔
        ∃ y : SchemeHomOver t (torusStr κ r), NeronModelInfra.schemeHomOverComp y τ = a) :
    Smooth (pullback.fst (abq 1).1 (LB.one (𝟙 _)).1 ≫ (abq 0).1) := by
  classical
  haveI : Mono τ.1 := by haveI := hτ; infer_instance

  let eB : Spec (CommRingCat.of κ) ⟶ B := (LB.one (𝟙 _)).1
  have heB : eB ≫ sB = 𝟙 _ := (LB.one (𝟙 _)).2
  let k₁ := pullback.fst (abq 1).1 eB
  let kS := pullback.snd (abq 1).1 eB
  have hcond : k₁ ≫ (abq 1).1 = kS ≫ eB := pullback.condition
  have hk : k₁ ≫ sG = kS := by
    have h : k₁ ≫ ((abq 1).1 ≫ sB) = kS := by rw [← Category.assoc, hcond, Category.assoc, heB, Category.comp_id]
    rwa [(abq 1).2] at h
  let φ : pullback (abq 1).1 eB ⟶ B := k₁ ≫ (abq 0).1
  have hφS : φ ≫ sB = kS := by
    show (k₁ ≫ (abq 0).1) ≫ sB = kS
    rw [Category.assoc, (abq 0).2, hk]
  change Smooth φ

  let j : B ⟶ pullback sB sB := pullback.lift (𝟙 B) (sB ≫ eB) (by rw [Category.id_comp, Category.assoc, heB, Category.comp_id])
  have hj1 : j ≫ pullback.fst sB sB = 𝟙 B := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd sB sB = sB ≫ eB := pullback.lift_snd _ _ _
  have hq2 : q sG sB abq ≫ pullback.snd sB sB = (abq 1).1 := pullback.lift_snd _ _ _
  have hq1 : q sG sB abq ≫ pullback.fst sB sB = (abq 0).1 := pullback.lift_fst _ _ _
  have hsq1 : IsPullback φ k₁ j (q sG sB abq) := by
    refine IsPullback.of_right (h₁₂ := sB) (v₁₃ := eB) (h₂₂ := pullback.snd sB sB) ?_ ?_ ?_
    · rw [hφS, hq2]
      exact (IsPullback.of_hasPullback (abq 1).1 eB).flip
    · apply pullback.hom_ext
      · rw [Category.assoc, hj1, Category.comp_id, Category.assoc, hq1]
      · rw [Category.assoc, hj2, ← Category.assoc, hφS, Category.assoc, hq2, hcond]
    · refine IsPullback.of_bot (v₂₁ := pullback.fst sB sB) (v₂₂ := sB) (h₃₁ := sB) ?_ hj2.symm
        (IsPullback.of_hasPullback sB sB).flip
      rw [hj1, heB]
      exact IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
  have hφsurj : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) hsq1.flip hsurj
  have hφflat : Flat φ := MorphismProperty.of_isPullback (P := @Flat) hsq1.flip hflat
  have hφqc : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact) hsq1.flip hqc
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) φ := ⟨⟨hφsurj, hφflat⟩, hφqc⟩

  let p₁ := pullback.fst φ φ
  let p₂ := pullback.snd φ φ
  have hp : p₁ ≫ φ = p₂ ≫ φ := pullback.condition
  let t : pullback φ φ ⟶ Spec (CommRingCat.of κ) := p₂ ≫ kS
  have ht1 : p₁ ≫ kS = t := by
    show p₁ ≫ kS = p₂ ≫ kS
    rw [← hφS, ← Category.assoc, hp, Category.assoc]
  let X : SchemeHomOver t sG := ⟨p₁ ≫ k₁, by rw [Category.assoc, hk, ht1]⟩
  let Y : SchemeHomOver t sG := ⟨p₂ ≫ k₁, by rw [Category.assoc, hk]⟩
  have hX1 : NeronModelInfra.schemeHomOverComp X (abq 1) = LB.one t := by
    apply Subtype.ext
    rw [one_coe sB LB t]
    show (p₁ ≫ k₁) ≫ (abq 1).1 = t ≫ eB
    rw [Category.assoc, hcond, ← Category.assoc, ht1]
  have hY1 : NeronModelInfra.schemeHomOverComp Y (abq 1) = LB.one t := by
    apply Subtype.ext
    rw [one_coe sB LB t]
    show (p₂ ≫ k₁) ≫ (abq 1).1 = (p₂ ≫ kS) ≫ eB
    rw [Category.assoc, hcond, Category.assoc]
  have hXY0 : NeronModelInfra.schemeHomOverComp X (abq 0) = NeronModelInfra.schemeHomOverComp Y (abq 0) := by
    apply Subtype.ext
    show (p₁ ≫ k₁) ≫ (abq 0).1 = (p₂ ≫ k₁) ≫ (abq 0).1
    rw [Category.assoc, Category.assoc]
    exact hp

  let n : SchemeHomOver t sG := LG.mul t X (LG.inv t Y)
  have hn : ∀ i, NeronModelInfra.schemeHomOverComp n (abq i) = LB.one t := by
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · show NeronModelInfra.schemeHomOverComp (LG.mul t X (LG.inv t Y)) (abq 0) = LB.one t
      rw [habq, comp_inv sG sB LG LB abq habq, hXY0, LB.mul_inv_cancel]
    · show NeronModelInfra.schemeHomOverComp (LG.mul t X (LG.inv t Y)) (abq 1) = LB.one t
      rw [habq, comp_inv sG sB LG LB abq habq, hX1, hY1, LB.mul_inv_cancel]
  obtain ⟨y, hy⟩ := (hker t n).mp hn
  have hy1 : y.1 ≫ τ.1 = n.1 := congrArg Subtype.val hy
  let Sh : pullback φ φ ⟶ pullback (torusStr κ r) kS := pullback.lift y.1 p₂ y.2
  have hSh1 : Sh ≫ pullback.fst (torusStr κ r) kS = y.1 := pullback.lift_fst _ _ _
  have hSh2 : Sh ≫ pullback.snd (torusStr κ r) kS = p₂ := pullback.lift_snd _ _ _

  let s₁ := pullback.fst (torusStr κ r) kS
  let s₂ := pullback.snd (torusStr κ r) kS
  let t' : pullback (torusStr κ r) kS ⟶ Spec (CommRingCat.of κ) := s₂ ≫ kS
  have hs : s₁ ≫ torusStr κ r = t' := pullback.condition
  let sT : SchemeHomOver t' (torusStr κ r) := ⟨s₁, hs⟩
  let Y' : SchemeHomOver t' sG := ⟨s₂ ≫ k₁, by rw [Category.assoc, hk]⟩
  have hY'1 : NeronModelInfra.schemeHomOverComp Y' (abq 1) = LB.one t' := by
    apply Subtype.ext
    rw [one_coe sB LB t']
    show (s₂ ≫ k₁) ≫ (abq 1).1 = (s₂ ≫ kS) ≫ eB
    rw [Category.assoc, hcond, Category.assoc]
  have hτs : ∀ i, NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp sT τ) (abq i) = LB.one t' :=
    (hker t' (NeronModelInfra.schemeHomOverComp sT τ)).mpr ⟨sT, rfl⟩
  let m : SchemeHomOver t' sG := LG.mul t' (NeronModelInfra.schemeHomOverComp sT τ) Y'
  have hm1 : NeronModelInfra.schemeHomOverComp m (abq 1) = LB.one t' := by
    show NeronModelInfra.schemeHomOverComp (LG.mul t' (NeronModelInfra.schemeHomOverComp sT τ) Y') (abq 1) = LB.one t'
    rw [habq, hτs 1, LB.one_mul, hY'1]
  have hm0 : NeronModelInfra.schemeHomOverComp m (abq 0) = NeronModelInfra.schemeHomOverComp Y' (abq 0) := by
    show NeronModelInfra.schemeHomOverComp (LG.mul t' (NeronModelInfra.schemeHomOverComp sT τ) Y') (abq 0) = _
    rw [habq, hτs 0, LB.one_mul]
  have hm1' : m.1 ≫ (abq 1).1 = t' ≫ eB := by
    have h := congrArg Subtype.val hm1
    rw [NeronModelInfra.schemeHomOverComp_coe, one_coe sB LB t'] at h
    exact h
  let mK : pullback (torusStr κ r) kS ⟶ pullback (abq 1).1 eB := pullback.lift m.1 t' hm1'
  have hmK1 : mK ≫ k₁ = m.1 := pullback.lift_fst _ _ _
  have hmK2 : mK ≫ kS = t' := pullback.lift_snd _ _ _
  have hmKφ : mK ≫ φ = s₂ ≫ φ := by
    show mK ≫ k₁ ≫ (abq 0).1 = s₂ ≫ k₁ ≫ (abq 0).1
    rw [← Category.assoc, hmK1]
    have h := congrArg Subtype.val hm0
    rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe] at h
    rw [h, Category.assoc]
  let Shinv : pullback (torusStr κ r) kS ⟶ pullback φ φ := pullback.lift mK s₂ hmKφ
  have hShinv1 : Shinv ≫ p₁ = mK := pullback.lift_fst _ _ _
  have hShinv2 : Shinv ≫ p₂ = s₂ := pullback.lift_snd _ _ _

  have hSht : Sh ≫ t' = t := by
    show Sh ≫ s₂ ≫ kS = p₂ ≫ kS
    rw [← Category.assoc, hSh2]
  have hI : Sh ≫ Shinv = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hShinv1, Category.id_comp]

      apply pullback.hom_ext
      · rw [Category.assoc, hmK1]

        have hnat := LG.mul_natural t' t Sh hSht (NeronModelInfra.schemeHomOverComp sT τ) Y'
        have e1 : GoodReductionJacobian.schemeHomOverComp Sh hSht (NeronModelInfra.schemeHomOverComp sT τ) = n := by
          apply Subtype.ext
          show Sh ≫ s₁ ≫ τ.1 = n.1
          rw [← Category.assoc, hSh1, hy1]
        have e2 : GoodReductionJacobian.schemeHomOverComp Sh hSht Y' = Y := by
          apply Subtype.ext
          show Sh ≫ s₂ ≫ k₁ = p₂ ≫ k₁
          rw [← Category.assoc, hSh2]
        rw [e1, e2] at hnat
        have e3 : LG.mul t n Y = X := by
          show LG.mul t (LG.mul t X (LG.inv t Y)) Y = X
          rw [LG.mul_assoc, LG.inv_mul_cancel, LG.mul_one]
        rw [e3] at hnat
        exact congrArg Subtype.val hnat
      · rw [Category.assoc, hmK2, hSht, ht1]
    · rw [Category.assoc, hShinv2, hSh2, Category.id_comp]

  have hShinvt : Shinv ≫ t = t' := by
    show Shinv ≫ p₂ ≫ kS = s₂ ≫ kS
    rw [← Category.assoc, hShinv2]
  have hII : Shinv ≫ Sh = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hSh1, Category.id_comp, ← cancel_mono τ.1, Category.assoc, hy1]

      have hnat := LG.mul_natural t t' Shinv hShinvt X (LG.inv t Y)
      have e1 : GoodReductionJacobian.schemeHomOverComp Shinv hShinvt X = m := by
        apply Subtype.ext
        show Shinv ≫ p₁ ≫ k₁ = m.1
        rw [← Category.assoc, hShinv1, hmK1]
      have e2 : GoodReductionJacobian.schemeHomOverComp Shinv hShinvt Y = Y' := by
        apply Subtype.ext
        show Shinv ≫ p₂ ≫ k₁ = s₂ ≫ k₁
        rw [← Category.assoc, hShinv2]
      rw [e1, inv_natural sG LG, e2] at hnat
      have e3 : LG.mul t' m (LG.inv t' Y') = NeronModelInfra.schemeHomOverComp sT τ := by
        show LG.mul t' (LG.mul t' (NeronModelInfra.schemeHomOverComp sT τ) Y') (LG.inv t' Y') = _
        rw [LG.mul_assoc, LG.mul_inv_cancel, LG.mul_one]
      rw [e3] at hnat
      exact congrArg Subtype.val hnat
    · rw [Category.assoc, hSh2, hShinv2, Category.id_comp]
  haveI : IsIso Sh := ⟨Shinv, hI, hII⟩

  haveI : SmoothOfRelativeDimension r (torusStr κ r) := (AlgebraicGeometry.SplitTorus.smoothOfRelativeDimension_torusStr κ r).2
  haveI : Smooth (torusStr κ r) := SmoothOfRelativeDimension.smooth r (torusStr κ r)
  have hsm2 : Smooth (pullback.snd φ φ) := by
    rw [show pullback.snd φ φ = Sh ≫ pullback.snd (torusStr κ r) kS from hSh2.symm]
    infer_instance

  haveI := AlgebraicGeometry.Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth) (f := φ) (g := φ) hQ hsm2

end S_AlgebraicGeometry_smooth_pullbackFst_comp_of_forall_iff_exists_torus_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_smooth_pullbackFst_comp_of_forall_iff_exists_torus_of_flat (solution)
