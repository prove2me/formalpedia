-- Prove2me | solution 1 for AlgebraicGeometry.exists_tableScheme_of_represents_homScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/8eac04a6-80a3-5981-96b7-4765c261b848

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_QuaternionAlgebra_Order
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_fibrePower_represents_tuples
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_isClosed_iInf_preimage_and_quasiCompact
import Theorems.Thm_AlgebraicGeometry_exists_equalizerLocus_isClosedImmersion_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isHomOnPoints_baseChange_comp
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_liftComp_baseChange_and_isHomOnPoints
import Theorems.Thm_AlgebraicGeometry_exists_hom_fibrePower_homScheme_of_naturalOperation
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_prod_zpow_baseChange_and_isHomOnPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_tableScheme_of_represents_homScheme

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u v

theorem solution
    {R : Type} [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f) (hc : L.IsCommutative)
    (c : Fin (2 * 2) → Fin (2 * 2) → Fin (2 * 2) → ℤ) (u : Fin (2 * 2) → ℤ)
    (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
        (φ : pullback f s ⟶ A), φ ≫ f = pullback.snd f s ≫ s → SchemeHomOver s πH)
    (hHnat : (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of R))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1))
    (hHsurj : (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) ∧
          pt S' s φ hφ = x))
    (hHinj : (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
          (φ φ' : pullback f s ⟶ A) (hφ : φ ≫ f = pullback.snd f s ≫ s) (hφ' : φ' ≫ f = pullback.snd f s ≫ s),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ' =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ'))
    (hHsep : IsSeparated πH) (hHlft : LocallyOfFiniteType πH) (hHlfp : LocallyOfFinitePresentation πH) :
    ∃ (E : Scheme.{0}) (πE : E ⟶ Spec (CommRingCat.of R)) (p : Fin (2 * 2) → (E ⟶ H)),
      (∀ j, p j ≫ πH = πE) ∧ IsSeparated πE ∧ LocallyOfFiniteType πE ∧ LocallyOfFinitePresentation πE ∧
      (∀ U : Fin (2 * 2) → H.Opens, (∀ j, IsClosed ((U j : Set H))) → (∀ j, QuasiCompact ((U j).ι ≫ πH)) →
        IsClosed ((⨅ j, (p j) ⁻¹ᵁ (U j) : E.Opens) : Set E) ∧ QuasiCompact ((⨅ j, (p j) ⁻¹ᵁ (U j)).ι ≫ πE)) ∧
      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)) (z z' : SchemeHomOver s πE),
        (∀ j, z.1 ≫ p j = z'.1 ≫ p j) → z = z') ∧
      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R))
          (φ : Fin (2 * 2) → (pullback f s ⟶ A)) (hφ : ∀ j, φ j ≫ f = pullback.snd f s ≫ s),
        (∀ j, (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ φ j =
              (L.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ j, by rw [Category.assoc, hφ j, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ j, by rw [Category.assoc, hφ j, ← Category.assoc, pullback.lift_snd]⟩).1)) →
        ((∃ z : SchemeHomOver s πE, ∀ j, z.1 ≫ p j = (pt S' s (φ j) (hφ j)).1) ↔
          (letI := L.pointCommGroup hc (pullback.snd f s ≫ s)
           (∀ j k : Fin (2 * 2),
              (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (c j k l)) =
                ⟨pullback.lift (φ k) (pullback.snd f s) (hφ k) ≫ φ j, by rw [Category.assoc, hφ j, ← Category.assoc, pullback.lift_snd]⟩) ∧
           (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (u l)) = ⟨pullback.fst f s, pullback.condition⟩))) := by
  classical

  obtain ⟨P, πP, q, hq, hPuniv, hPsep, hPlft, hPlfp, hPpieces⟩ :=
    AlgebraicGeometry.Scheme.exists_fibrePower_represents_tuples πH (2 * 2)

  have hA := fun jk : Fin (2 * 2) × Fin (2 * 2) =>
    AlgebraicGeometry.exists_hom_fibrePower_homScheme_of_naturalOperation f L H πH pt hHnat hHsurj hHinj (GoodReductionJacobian.RelativeGroupLaw.isHomOnPoints_baseChange_comp L) (2 * 2) P πP q hq hPuniv
      (fun S' _ s φ hφ => (letI := L.pointCommGroup hc (pullback.snd f s ≫ s); (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (c jk.1 jk.2 l))).1)
      (fun S' _ s φ hφ => (letI := L.pointCommGroup hc (pullback.snd f s ≫ s); (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (c jk.1 jk.2 l))).2)
      ((GoodReductionJacobian.RelativeGroupLaw.prod_zpow_baseChange_and_isHomOnPoints L hc (2 * 2) (c jk.1 jk.2)).1)
  choose opA hopA hopAsem using hA
  have hB := fun jk : Fin (2 * 2) × Fin (2 * 2) =>
    AlgebraicGeometry.exists_hom_fibrePower_homScheme_of_naturalOperation f L H πH pt hHnat hHsurj hHinj (GoodReductionJacobian.RelativeGroupLaw.isHomOnPoints_baseChange_comp L) (2 * 2) P πP q hq hPuniv
      (fun S' _ s φ hφ => pullback.lift (φ jk.2) (pullback.snd f s) (hφ jk.2) ≫ φ jk.1)
      (fun S' _ s φ hφ => by rw [Category.assoc, hφ jk.1, ← Category.assoc, pullback.lift_snd])
      (fun S' S'' _ _ ψ s s'' hs φ hφ => (GoodReductionJacobian.RelativeGroupLaw.liftComp_baseChange_and_isHomOnPoints L).1 S' S'' ψ s s'' hs (φ jk.1) (φ jk.2) (hφ jk.1) (hφ jk.2))
  choose opB hopB hopBsem using hB
  obtain ⟨opU, hopU, hopUsem⟩ :=
    AlgebraicGeometry.exists_hom_fibrePower_homScheme_of_naturalOperation f L H πH pt hHnat hHsurj hHinj (GoodReductionJacobian.RelativeGroupLaw.isHomOnPoints_baseChange_comp L) (2 * 2) P πP q hq hPuniv
      (fun S' _ s φ hφ => (letI := L.pointCommGroup hc (pullback.snd f s ≫ s); (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (u l))).1)
      (fun S' _ s φ hφ => (letI := L.pointCommGroup hc (pullback.snd f s ≫ s); (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (u l))).2)
      ((GoodReductionJacobian.RelativeGroupLaw.prod_zpow_baseChange_and_isHomOnPoints L hc (2 * 2) u).1)
  obtain ⟨opI, hopI, hopIsem⟩ :=
    AlgebraicGeometry.exists_hom_fibrePower_homScheme_of_naturalOperation f L H πH pt hHnat hHsurj hHinj (GoodReductionJacobian.RelativeGroupLaw.isHomOnPoints_baseChange_comp L) (2 * 2) P πP q hq hPuniv
      (fun S' _ s φ hφ => pullback.fst f s)
      (fun S' _ s φ hφ => pullback.condition)
      (fun S' S'' _ _ ψ s s'' hs φ hφ => (pullback.lift_fst _ _ _).symm)

  obtain ⟨E, m, hmci, hmeq, hEuniv, hmlfp⟩ :=
    AlgebraicGeometry.exists_equalizerLocus_isClosedImmersion_of_isSeparated πP πH hHsep
      (ι := Option (Fin (2 * 2) × Fin (2 * 2)))
      (fun o => Option.elim o opU opA) (fun o => Option.elim o opI opB)
      (fun o => by cases o with | none => exact hopU | some jk => exact hopA jk)
      (fun o => by cases o with | none => exact hopI | some jk => exact hopB jk)
  haveI := hmci

  refine ⟨E, m ≫ πP, fun j => m ≫ q j, fun j => by rw [Category.assoc, hq], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI := hPsep hHsep; infer_instance
  · haveI := hPlft hHlft; infer_instance
  · haveI := hPlfp hHlfp
    haveI := hmlfp (by haveI := hHlft; exact AlgebraicGeometry.locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType πH)
    infer_instance
  ·
    intro U hUc hUq
    exact AlgebraicGeometry.IsClosedImmersion.isClosed_iInf_preimage_and_quasiCompact m hmci πP (fun j => (q j) ⁻¹ᵁ (U j)) (hPpieces U hUc hUq).1 (hPpieces U hUc hUq).2
  ·
    intro S' _ s z z' hzz'
    apply Subtype.ext
    rw [← cancel_mono m]
    refine (hPuniv (Spec (CommRingCat.of S')) s (fun l => z.1 ≫ m ≫ q l)
      (fun l => by rw [Category.assoc, Category.assoc, hq]; exact z.2)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [Category.assoc]; exact z.2
    · intro l; rw [Category.assoc]
    · rw [Category.assoc]; exact z'.2
    · intro l; rw [Category.assoc]; exact (hzz' l).symm
  ·
    intro S' _ s φ hφ hhom
    have ptcongr : ∀ (a b : pullback f s ⟶ A) (ha : a ≫ f = pullback.snd f s ≫ s)
        (hb : b ≫ f = pullback.snd f s ≫ s), a = b → pt S' s a ha = pt S' s b hb := by
      rintro a b ha hb rfl; rfl
    have homI : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
          pullback.lift (L.mul (t' ≫ s) P Q).1 t' (L.mul (t' ≫ s) P Q).2 ≫ pullback.fst f s =
            (L.mul (t' ≫ s)
              ⟨pullback.lift P.1 t' P.2 ≫ pullback.fst f s, by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.lift_snd]⟩
              ⟨pullback.lift Q.1 t' Q.2 ≫ pullback.fst f s, by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.lift_snd]⟩).1) := by
      intro T t' P Q
      simp only [pullback.lift_fst, Subtype.coe_eta]
    constructor
    · rintro ⟨z, hz⟩
      have hzP : (z.1 ≫ m) ≫ πP = s := by rw [Category.assoc]; exact z.2
      have hw : ∀ l, (⟨z.1 ≫ m, hzP⟩ : SchemeHomOver s πP).1 ≫ q l = (pt S' s (φ l) (hφ l)).1 :=
        fun l => by rw [Category.assoc]; exact hz l
      refine ⟨fun j k => ?_, ?_⟩
      · have h1 : (z.1 ≫ m) ≫ opA (j, k) = _ := hopAsem (j, k) S' s φ hφ hhom ⟨z.1 ≫ m, hzP⟩ hw
        have h2 : (z.1 ≫ m) ≫ opB (j, k) = _ := hopBsem (j, k) S' s φ hφ hhom ⟨z.1 ≫ m, hzP⟩ hw
        have h3 : m ≫ opA (j, k) = m ≫ opB (j, k) := hmeq (some (j, k))
        have h4 : (z.1 ≫ m) ≫ opA (j, k) = (z.1 ≫ m) ≫ opB (j, k) := by
          rw [Category.assoc, h3, ← Category.assoc]
        rw [h1, h2] at h4
        have homW := (GoodReductionJacobian.RelativeGroupLaw.prod_zpow_baseChange_and_isHomOnPoints L hc (2 * 2) (c j k)).2 S' s φ hφ hhom (letI := L.pointCommGroup hc (pullback.snd f s ≫ s); (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (c j k l))).1 (letI := L.pointCommGroup hc (pullback.snd f s ≫ s); (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (c j k l))).2 rfl
        have homC := (GoodReductionJacobian.RelativeGroupLaw.liftComp_baseChange_and_isHomOnPoints L).2 S' s (φ j) (φ k) (hφ j) (hφ k) (hhom j) (hhom k)
          (pullback.lift (φ k) (pullback.snd f s) (hφ k) ≫ φ j) (by rw [Category.assoc, hφ j, ← Category.assoc, pullback.lift_snd]) rfl
        exact Subtype.ext (hHinj S' s _ _ _ _ homW homC (Subtype.ext h4))
      · have h1 : (z.1 ≫ m) ≫ opU = _ := hopUsem S' s φ hφ hhom ⟨z.1 ≫ m, hzP⟩ hw
        have h2 : (z.1 ≫ m) ≫ opI = _ := hopIsem S' s φ hφ hhom ⟨z.1 ≫ m, hzP⟩ hw
        have h3 : m ≫ opU = m ≫ opI := hmeq none
        have h4 : (z.1 ≫ m) ≫ opU = (z.1 ≫ m) ≫ opI := by
          rw [Category.assoc, h3, ← Category.assoc]
        rw [h1, h2] at h4
        have homW := (GoodReductionJacobian.RelativeGroupLaw.prod_zpow_baseChange_and_isHomOnPoints L hc (2 * 2) u).2 S' s φ hφ hhom (letI := L.pointCommGroup hc (pullback.snd f s ≫ s); (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (u l))).1 (letI := L.pointCommGroup hc (pullback.snd f s ≫ s); (∏ l, (⟨φ l, hφ l⟩ : SchemeHomOver (pullback.snd f s ≫ s) f) ^ (u l))).2 rfl
        exact Subtype.ext (hHinj S' s _ _ _ _ homW homI (Subtype.ext h4))
    · rintro ⟨htab, huni⟩
      obtain ⟨w, hwP, hwq⟩ := (hPuniv (Spec (CommRingCat.of S')) s (fun l => (pt S' s (φ l) (hφ l)).1)
        (fun l => (pt S' s (φ l) (hφ l)).2)).exists
      have heq : ∀ o : Option (Fin (2 * 2) × Fin (2 * 2)),
          w ≫ Option.elim o opU opA = w ≫ Option.elim o opI opB := by
        rintro (_ | ⟨j, k⟩)
        · show w ≫ opU = w ≫ opI
          have h1 : w ≫ opU = _ := hopUsem S' s φ hφ hhom ⟨w, hwP⟩ hwq
          have h2 : w ≫ opI = _ := hopIsem S' s φ hφ hhom ⟨w, hwP⟩ hwq
          rw [h1, h2]
          exact congrArg Subtype.val (ptcongr _ _ _ _ (congrArg Subtype.val huni))
        · show w ≫ opA (j, k) = w ≫ opB (j, k)
          have h1 : w ≫ opA (j, k) = _ := hopAsem (j, k) S' s φ hφ hhom ⟨w, hwP⟩ hwq
          have h2 : w ≫ opB (j, k) = _ := hopBsem (j, k) S' s φ hφ hhom ⟨w, hwP⟩ hwq
          rw [h1, h2]
          exact congrArg Subtype.val (ptcongr _ _ _ _ (congrArg Subtype.val (htab j k)))
      obtain ⟨g', hg'⟩ := (hEuniv (Spec (CommRingCat.of S')) w heq).exists
      refine ⟨⟨g', ?_⟩, fun j => ?_⟩
      · show g' ≫ m ≫ πP = s
        rw [← Category.assoc, hg', hwP]
      · show g' ≫ m ≫ q j = (pt S' s (φ j) (hφ j)).1
        rw [← Category.assoc, hg', hwq j]

#print axioms solution

end S_AlgebraicGeometry_exists_tableScheme_of_represents_homScheme
end P2MW
export P2MW.S_AlgebraicGeometry_exists_tableScheme_of_represents_homScheme (solution)
