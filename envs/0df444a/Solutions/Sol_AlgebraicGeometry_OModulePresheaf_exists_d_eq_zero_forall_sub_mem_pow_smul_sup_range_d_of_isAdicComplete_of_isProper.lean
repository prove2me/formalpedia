-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2afcec4c-45b9-593b-b46a-babb31e66998

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_IsAdicComplete_of_module_finite
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (t : ℕ → F.cochain K (i + 1))
    (hd : ∀ n : ℕ, F.d K (i + 1) (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 2))))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈
      I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i)) :
    ∃ a : F.cochain K (i + 1), F.d K (i + 1) a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1))) ⊔ LinearMap.range (F.d K i) := by
  classical

  set d1 := F.d K (i + 1) with hd1
  set d0 := F.d K i with hd0
  let Z : Submodule A (F.cochain K (i + 1)) := LinearMap.ker d1
  let B : Submodule A (F.cochain K (i + 1)) := LinearMap.range d0
  let S : ℕ → Submodule A (F.cochain K (i + 1)) := fun n => I ^ (n + 1) • ⊤ ⊔ B
  have hBZ : B ≤ Z := by
    rintro _ ⟨c, rfl⟩
    show d1 (d0 c) = 0
    have := LinearMap.congr_fun (AlgebraicGeometry.OModulePresheaf.d_comp_d F K i) c
    rw [hd1, hd0]
    simpa using this
  have hSanti : ∀ {n m : ℕ}, n ≤ m → S m ≤ S n := fun {n m} h =>
    sup_le_sup_right (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) _

  have htt : ∀ (n m : ℕ), n ≤ m → t m - t n ∈ S n := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => rw [sub_self]; exact zero_mem _
    | succ m hnm ih =>
      have h1 : t (m + 1) - t m ∈ S n := hSanti hnm (ht m)
      have : t (m + 1) - t n = (t (m + 1) - t m) + (t m - t n) := by abel
      rw [this]; exact add_mem h1 ih

  have hG1 : ∀ n : ℕ, ∃ z : F.cochain K (i + 1), d1 z = 0 ∧ z - t n ∈ S n := by
    intro n
    obtain ⟨c₁, hc₁⟩ := AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
      I q F hc hqc K i (n + 1)
    have hdt : F.d K (i + 1) (t (n + c₁)) ∈ I ^ (n + 1 + c₁) • (⊤ : Submodule A (F.cochain K (i + 2))) := by
      have := hd (n + c₁); rwa [show n + c₁ + 1 = n + 1 + c₁ by omega] at this
    obtain ⟨a, ha, hta⟩ := hc₁ (t (n + c₁)) hdt
    refine ⟨a, by rw [hd1]; exact ha, ?_⟩
    have h1 : a - t (n + c₁) ∈ S n := by
      refine Submodule.mem_sup_left ?_
      rw [← neg_sub]; exact Submodule.neg_mem _ hta
    have h2 : t (n + c₁) - t n ∈ S n := htt n (n + c₁) (Nat.le_add_right n c₁)
    have : a - t n = (a - t (n + c₁)) + (t (n + c₁) - t n) := by abel
    rw [this]; exact add_mem h1 h2
  choose z hz hzt using hG1
  have hzz : ∀ (n m : ℕ), n ≤ m → z m - z n ∈ S n := by
    intro n m hnm
    have : z m - z n = (z m - t m) + (t m - t n) - (z n - t n) := by abel
    rw [this]
    exact sub_mem (add_mem (hSanti hnm (hzt m)) (htt n m hnm)) (hzt n)

  have hG3 := fun k : ℕ =>
    AlgebraicGeometry.OModulePresheaf.exists_ker_d_inf_pow_smul_le_pow_smul_ker_sup_range_of_isProper I q F hc hqc K i k
  choose c₃ hc₃ using hG3
  let cm : ℕ → ℕ := fun k => Nat.rec (c₃ 0) (fun k ih => max ih (c₃ (k + 1))) k
  have hcm0 : cm 0 = c₃ 0 := rfl
  have hcms : ∀ k, cm (k + 1) = max (cm k) (c₃ (k + 1)) := fun k => rfl
  have hcm_ge : ∀ k, c₃ k ≤ cm k := by
    intro k; cases k with
    | zero => rw [hcm0]
    | succ k => rw [hcms]; exact le_max_right _ _
  have hcm_mono : ∀ k, cm k ≤ cm (k + 1) := fun k => by rw [hcms]; exact le_max_left _ _
  let Mx : ℕ → ℕ := fun k => k + cm k
  have hMmono : ∀ k, Mx k ≤ Mx (k + 1) := fun k => by
    show k + cm k ≤ k + 1 + cm (k + 1); have := hcm_mono k; omega
  have hMge : ∀ k, k ≤ Mx k := fun k => Nat.le_add_right k _
  have hG3' : ∀ (k : ℕ) (y : F.cochain K (i + 1)), d1 y = 0 →
      y ∈ (I ^ (k + cm k) • ⊤ : Submodule A (F.cochain K (i + 1))) →
      y ∈ I ^ k • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by
    intro k y hy hmem
    apply hc₃ k
    refine ⟨by rw [← hd1]; exact hy, ?_⟩
    exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by have := hcm_ge k; omega))) hmem

  let w : ℕ → F.cochain K (i + 1) := fun k => z (Mx k)
  have hwz : ∀ k, d1 (w k) = 0 := fun k => hz (Mx k)
  have hw : ∀ k, w (k + 1) - w k ∈ I ^ k • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by
    intro k
    have hy : w (k + 1) - w k ∈ S (Mx k) := hzz (Mx k) (Mx (k + 1)) (hMmono k)
    obtain ⟨v, hv, b, hb, hvb⟩ := Submodule.mem_sup.mp hy
    have hb0 : d1 b = 0 := hBZ hb
    have hvZ : d1 v = 0 := by
      have hv' : v = (w (k + 1) - w k) - b := by rw [← hvb]; abel
      rw [hv', map_sub, map_sub, hb0, sub_zero, hwz, hwz, sub_self]
    have hvmem : v ∈ (I ^ (k + cm k) • ⊤ : Submodule A (F.cochain K (i + 1))) :=
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by change k + cm k ≤ k + cm k + 1; omega))) hv
    rw [← hvb]
    exact add_mem (hG3' k v hvZ hvmem) (Submodule.mem_sup_right hb)

  let Z : Submodule A (F.cochain K (i + 1)) := LinearMap.ker (F.d K (i + 1))
  let B' : Submodule A Z := (LinearMap.range (F.d K i)).comap Z.subtype
  have hZsmul : ∀ k : ℕ, I ^ k • LinearMap.ker (F.d K (i + 1)) =
      Submodule.map Z.subtype (I ^ k • (⊤ : Submodule A Z)) := fun k => by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  have hHsmul : ∀ k : ℕ, (I ^ k • (⊤ : Submodule A (F.HSucc K i))) =
      Submodule.map (Submodule.mkQ B') (I ^ k • (⊤ : Submodule A Z)) := fun k => by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

  have T1 : ∀ (k : ℕ) (x : Z), (x : F.cochain K (i + 1)) ∈
      I ^ k • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) →
      (Submodule.mkQ B' x : F.HSucc K i) ∈ I ^ k • (⊤ : Submodule A (F.HSucc K i)) := by
    intro k x hx
    obtain ⟨v, hv, b, hb, hvb⟩ := Submodule.mem_sup.mp hx
    rw [hZsmul] at hv
    obtain ⟨v', hv', rfl⟩ := hv
    have hxv : x - v' ∈ B' := by
      show Z.subtype (x - v') ∈ LinearMap.range (F.d K i)
      have : Z.subtype (x - v') = b := by
        rw [map_sub]
        simp only [Submodule.coe_subtype]
        rw [← hvb]
        simp
      rw [this]; exact hb
    have hx' : Submodule.mkQ B' x = Submodule.mkQ B' v' := by
      rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hxv
    rw [hx', hHsmul]
    exact ⟨v', hv', rfl⟩

  have T2 : ∀ (k : ℕ) (x : Z), (Submodule.mkQ B' x : F.HSucc K i) ∈ I ^ k • (⊤ : Submodule A (F.HSucc K i)) →
      (x : F.cochain K (i + 1)) ∈ I ^ k • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) := by
    intro k x hx
    rw [hHsmul] at hx
    obtain ⟨v', hv', hvx⟩ := hx
    have hxv : x - v' ∈ B' := by
      rw [← Submodule.Quotient.eq]
      exact hvx.symm
    have hb : (Z.subtype x) - (Z.subtype v') ∈ LinearMap.range (F.d K i) := by
      rw [← map_sub]; exact hxv
    have hv : (Z.subtype v') ∈ I ^ k • LinearMap.ker (F.d K (i + 1)) := by
      rw [hZsmul]; exact ⟨v', hv', rfl⟩
    have : (x : F.cochain K (i + 1)) = Z.subtype v' + (Z.subtype x - Z.subtype v') := by simp
    rw [this]
    exact add_mem (Submodule.mem_sup_left hv) (Submodule.mem_sup_right hb)
  haveI hfin : Module.Finite A (F.HSucc K i) :=
    (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper F hc hqc K).2 i
  have hcomplete : IsAdicComplete I (F.HSucc K i) := IsAdicComplete.of_module_finite I (F.HSucc K i)

  let ζ : ℕ → Z := fun k => ⟨w k, LinearMap.mem_ker.mpr (by rw [← hd1]; exact hwz k)⟩
  let g : ℕ → F.HSucc K i := fun k => Submodule.mkQ B' (ζ k)
  have hg : ∀ k, g k ≡ g (k + 1) [SMOD (I ^ k • ⊤ : Submodule A (F.HSucc K i))] := by
    intro k
    rw [SModEq.sub_mem]
    show Submodule.mkQ B' (ζ k) - Submodule.mkQ B' (ζ (k + 1)) ∈ _
    rw [← map_sub]
    apply T1
    have : ((ζ k - ζ (k + 1) : Z) : F.cochain K (i + 1)) = -(w (k + 1) - w k) := by
      simp [ζ]
    rw [this]
    exact Submodule.neg_mem _ (hw k)
  have hcau : AdicCompletion.IsAdicCauchy I (F.HSucc K i) g := (AdicCompletion.isAdicCauchy_iff I _ g).mpr hg
  obtain ⟨L, hL⟩ := hcomplete.toIsPrecomplete.prec hcau
  obtain ⟨ζL, hζL⟩ := Submodule.Quotient.mk_surjective B' L

  refine ⟨(ζL : F.cochain K (i + 1)), ζL.2, fun n => ?_⟩
  have h1 : (w (n + 1) - (ζL : F.cochain K (i + 1))) ∈ S n := by
    have hmem : (Submodule.mkQ B' (ζ (n + 1) - ζL) : F.HSucc K i) ∈
        I ^ (n + 1) • (⊤ : Submodule A (F.HSucc K i)) := by
      rw [map_sub]
      have := (SModEq.sub_mem).mp (hL (n + 1))
      rw [← hζL] at this
      exact this
    have h := T2 (n + 1) (ζ (n + 1) - ζL) hmem
    have hcoe : ((ζ (n + 1) - ζL : Z) : F.cochain K (i + 1)) = w (n + 1) - (ζL : F.cochain K (i + 1)) := by
      simp [ζ]
    rw [hcoe] at h
    have hle : I ^ (n + 1) • LinearMap.ker (F.d K (i + 1)) ⊔ LinearMap.range (F.d K i) ≤ S n :=
      sup_le_sup_right (smul_mono_right _ le_top) _
    exact hle h
  have h2 : w (n + 1) - t n ∈ S n := by
    have : w (n + 1) - t n = (z (Mx (n + 1)) - t (Mx (n + 1))) + (t (Mx (n + 1)) - t n) := by
      show z (Mx (n + 1)) - t n = _; abel
    rw [this]
    have hle : n ≤ Mx (n + 1) := by have := hMge (n + 1); omega
    exact add_mem (hSanti hle (hzt _)) (htt n _ hle)
  have : (ζL : F.cochain K (i + 1)) - t n = -(w (n + 1) - (ζL : F.cochain K (i + 1))) + (w (n + 1) - t n) := by
    abel
  rw [this]
  exact add_mem (Submodule.neg_mem _ h1) h2

end S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper (solution)
