-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.unitPullback_sub_unitPullback_mem_of_d_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7633b409-62a7-5cd3-9d22-afef2633243f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_HSucc_equiv_unitPullback_id_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_d_eq_zero
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace P2mLambdaIndep

variable {X : Scheme.{u}}

noncomputable def dbl (𝒲 : X.OrderedAffineCover) : X.OrderedAffineCover where
  ι := 𝒲.ι ×ₗ Bool
  U p := 𝒲.U (ofLex p).1
  isAffineOpen p := 𝒲.isAffineOpen _
  iSup_eq_top := by
    refine le_antisymm le_top ?_
    rw [← 𝒲.iSup_eq_top]
    exact iSup_le fun i => le_iSup_of_le (toLex (i, false)) le_rfl

theorem dbl_U (𝒲 : X.OrderedAffineCover) (p : (dbl 𝒲).ι) : (dbl 𝒲).U p = 𝒲.U (ofLex p).1 := rfl

def sec (𝒲 : X.OrderedAffineCover) (b : Bool) : 𝒲.ι → (dbl 𝒲).ι := fun w => toLex (w, b)

def col (𝒲 : X.OrderedAffineCover) : (dbl 𝒲).ι → 𝒲.ι := fun p => (ofLex p).1

theorem sec_le (𝒲 : X.OrderedAffineCover) (b : Bool) (w : 𝒲.ι) : 𝒲.U w ≤ (𝟙 X) ⁻¹ᵁ (dbl 𝒲).U (sec 𝒲 b w) := le_rfl

theorem col_le (𝒲 : X.OrderedAffineCover) (p : (dbl 𝒲).ι) : (dbl 𝒲).U p ≤ (𝟙 X) ⁻¹ᵁ 𝒲.U (col 𝒲 p) := le_rfl

def mrg (𝒲 : X.OrderedAffineCover) {κ : Type u} (lam lam' : 𝒲.ι → κ) : (dbl 𝒲).ι → κ :=
  fun p => match (ofLex p).2 with
    | false => lam (ofLex p).1
    | true => lam' (ofLex p).1

end P2mLambdaIndep

open P2mLambdaIndep in

theorem P2mLambdaIndep.unitPullback_sub {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (a b : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (a - b) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n a -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n b := by
  classical
  funext s
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [Pi.sub_apply, OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
      OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj,
      OModulePresheaf.unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
    erw [map_sub, map_sub, smul_sub]
    rfl
  · simp only [Pi.sub_apply, OModulePresheaf.unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj, sub_zero]

open P2mLambdaIndep in
theorem P2mLambdaIndep.unitPullback_zero {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (0 : (OModulePresheaf.unit πY).cochain 𝒦 n) = 0 := by
  have := P2mLambdaIndep.unitPullback_sub πX πY h 𝒲 𝒦 lam hlam n 0 0
  simpa using this

open P2mLambdaIndep in
theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) [IsSeparated πX] (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam' w))
    (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) (hz : (OModulePresheaf.unit πY).d 𝒦 n z = 0) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' n z
      ∈ (show Submodule R' ((OModulePresheaf.unit πX).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m)) := by
  classical
  have hΛ : ∀ p, (dbl 𝒲).U p ≤ h ⁻¹ᵁ 𝒦.U (mrg 𝒲 lam lam' p) := by
    intro p
    show 𝒲.U (ofLex p).1 ≤ h ⁻¹ᵁ 𝒦.U (mrg 𝒲 lam lam' p)
    unfold mrg
    cases (ofLex p).2 with
    | false => exact hlam _
    | true => exact hlam' _

  set w := OModulePresheaf.unitPullback (πX := πX) h (dbl 𝒲) 𝒦 (mrg 𝒲 lam lam') hΛ n z with hw
  have hwz : (OModulePresheaf.unit πX).d (dbl 𝒲) n w = 0 := by
    rw [hw, OModulePresheaf.d_unitPullback, hz, P2mLambdaIndep.unitPullback_zero]

  obtain ⟨e₀, e, he₀, he⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_HSucc_equiv_unitPullback_id_of_isSeparated πX 𝒲 (dbl 𝒲) (col 𝒲) (col_le 𝒲)
  cases n with
  | zero =>
    change _ ∈ (⊥ : Submodule R' _)
    rw [Submodule.mem_bot]

    have hAf : OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 false) (sec_le 𝒲 false) 0 w -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam 0 z = 0 := by
      have := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πY (𝟙 X) h h
        (by simp) 𝒲 (dbl 𝒲) 𝒦 (sec 𝒲 false) (mrg 𝒲 lam lam') lam (funext fun _ => rfl) (sec_le 𝒲 false) hΛ hlam
        0 z hz
      rw [← hw] at this
      exact (Submodule.mem_bot R').1 this
    have hAt : OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 true) (sec_le 𝒲 true) 0 w -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' 0 z = 0 := by
      have := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πY (𝟙 X) h h
        (by simp) 𝒲 (dbl 𝒲) 𝒦 (sec 𝒲 true) (mrg 𝒲 lam lam') lam' (funext fun _ => rfl) (sec_le 𝒲 true) hΛ hlam'
        0 z hz
      rw [← hw] at this
      exact (Submodule.mem_bot R').1 this

    have hw0 : w ∈ (OModulePresheaf.unit πX).H0 (dbl 𝒲) := LinearMap.mem_ker.2 hwz
    obtain ⟨u, hu⟩ := e₀.surjective ⟨w, hw0⟩
    have huw : OModulePresheaf.unitPullback (πX := πX) (𝟙 X) (dbl 𝒲) 𝒲 (col 𝒲) (col_le 𝒲) 0 u.1 = w := by
      rw [← he₀ u, hu]

    have hD : ∀ b : Bool,
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 b) (sec_le 𝒲 b) 0
            (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) (dbl 𝒲) 𝒲 (col 𝒲) (col_le 𝒲) 0 u.1) -
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 𝒲 id (fun w => le_rfl) 0 u.1 = 0 := by
      intro b
      have := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX (𝟙 X) (𝟙 X)
        (𝟙 X) (by simp) 𝒲 (dbl 𝒲) 𝒲 (sec 𝒲 b) (col 𝒲) id (funext fun _ => rfl) (sec_le 𝒲 b) (col_le 𝒲)
        (fun w => le_rfl) 0 u.1 (LinearMap.mem_ker.1 u.2)
      exact (Submodule.mem_bot R').1 this
    have hDf := hD false
    have hDt := hD true
    rw [huw, sub_eq_zero] at hDf hDt
    rw [sub_eq_zero] at hAf hAt
    rw [← hAf, ← hAt, hDf, hDt, sub_self]
  | succ m =>
    change _ ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m)

    have hAf : OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 false) (sec_le 𝒲 false) (m + 1) w -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam (m + 1) z ∈
      LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m) := by
      have := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πY (𝟙 X) h h
        (by simp) 𝒲 (dbl 𝒲) 𝒦 (sec 𝒲 false) (mrg 𝒲 lam lam') lam (funext fun _ => rfl) (sec_le 𝒲 false) hΛ hlam
        (m + 1) z hz
      rw [← hw] at this
      exact this
    have hAt : OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 true) (sec_le 𝒲 true) (m + 1) w -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' (m + 1) z ∈
      LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m) := by
      have := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πY (𝟙 X) h h
        (by simp) 𝒲 (dbl 𝒲) 𝒦 (sec 𝒲 true) (mrg 𝒲 lam lam') lam' (funext fun _ => rfl) (sec_le 𝒲 true) hΛ hlam'
        (m + 1) z hz
      rw [← hw] at this
      exact this

    have hwk : w ∈ LinearMap.ker ((OModulePresheaf.unit πX).d (dbl 𝒲) (m + 1)) := LinearMap.mem_ker.2 hwz
    obtain ⟨q, hq⟩ := (e m).surjective (Submodule.Quotient.mk ⟨w, hwk⟩)
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨hu', heu⟩ := he m u
    rw [heu] at hq
    have hcu : OModulePresheaf.unitPullback (πX := πX) (𝟙 X) (dbl 𝒲) 𝒲 (col 𝒲) (col_le 𝒲) (m + 1) u.1 - w ∈
        LinearMap.range ((OModulePresheaf.unit πX).d (dbl 𝒲) m) := by
      have := (Submodule.Quotient.eq _).1 hq
      simpa using this
    obtain ⟨β, hβ⟩ := hcu

    have hD : ∀ b : Bool,
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 b) (sec_le 𝒲 b) (m + 1)
            (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) (dbl 𝒲) 𝒲 (col 𝒲) (col_le 𝒲) (m + 1) u.1) -
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 𝒲 id (fun w => le_rfl) (m + 1) u.1 ∈
        LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 m) := by
      intro b
      exact AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero πX πX πX (𝟙 X) (𝟙 X)
        (𝟙 X) (by simp) 𝒲 (dbl 𝒲) 𝒲 (sec 𝒲 b) (col 𝒲) id (funext fun _ => rfl) (sec_le 𝒲 b) (col_le 𝒲)
        (fun w => le_rfl) (m + 1) u.1 (LinearMap.mem_ker.1 u.2)
    have hDf := hD false
    have hDt := hD true

    have hsplit : ∀ b : Bool,
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 b) (sec_le 𝒲 b) (m + 1) w =
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 b) (sec_le 𝒲 b) (m + 1)
              (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) (dbl 𝒲) 𝒲 (col 𝒲) (col_le 𝒲) (m + 1) u.1) -
            (OModulePresheaf.unit πX).d 𝒲 m
              (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 b) (sec_le 𝒲 b) m β) := by
      intro b
      rw [OModulePresheaf.d_unitPullback, hβ, ← P2mLambdaIndep.unitPullback_sub, sub_sub_cancel]
    have key : OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam (m + 1) z -
        OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' (m + 1) z =
      -(OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 false) (sec_le 𝒲 false) (m + 1) w -
          OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam (m + 1) z) +
      (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 true) (sec_le 𝒲 true) (m + 1) w -
          OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam' hlam' (m + 1) z) +
      ((OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 false) (sec_le 𝒲 false) (m + 1)
              (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) (dbl 𝒲) 𝒲 (col 𝒲) (col_le 𝒲) (m + 1) u.1) -
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 𝒲 id (fun w => le_rfl) (m + 1) u.1) -
        (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 true) (sec_le 𝒲 true) (m + 1)
              (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) (dbl 𝒲) 𝒲 (col 𝒲) (col_le 𝒲) (m + 1) u.1) -
          OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 𝒲 id (fun w => le_rfl) (m + 1) u.1)) -
      ((OModulePresheaf.unit πX).d 𝒲 m
          (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 false) (sec_le 𝒲 false) m β) -
        (OModulePresheaf.unit πX).d 𝒲 m
          (OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒲 (dbl 𝒲) (sec 𝒲 true) (sec_le 𝒲 true) m β)) := by
      rw [hsplit false, hsplit true]; abel
    rw [key]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ hAf) hAt)
      (Submodule.sub_mem _ hDf hDt)) (Submodule.sub_mem _ (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _))

end S_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_d_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_d_eq_zero (solution)
