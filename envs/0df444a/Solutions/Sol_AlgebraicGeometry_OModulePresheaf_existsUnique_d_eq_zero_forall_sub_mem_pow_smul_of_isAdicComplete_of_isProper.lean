-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/6626bd6b-960c-5cae-8f22-59b79e5851d8

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper
import Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry"

namespace FF0LimAux

section Algebra

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

theorem coe_mem_smul_iff (J : Ideal A) (p : Submodule A M) (x : p) :
    (x : M) ∈ J • p ↔ x ∈ J • (⊤ : Submodule A p) := by
  have hmap : (J • (⊤ : Submodule A p)).map p.subtype = J • p := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  constructor
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext (by simpa using hyx)
    exact this ▸ hy
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, rfl⟩

theorem pow_smul_le_pow_smul (I : Ideal A) (N : Submodule A M) {m n : ℕ} (h : m ≤ n) :
    I ^ n • N ≤ I ^ m • N :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

def env (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => c 0
  | n + 1 => max (env c n) (n + 1 + c (n + 1))

theorem add_le_env (c : ℕ → ℕ) : ∀ n, n + c n ≤ env c n
  | 0 => by simp [env]
  | n + 1 => by
    show n + 1 + c (n + 1) ≤ max (env c n) (n + 1 + c (n + 1))
    exact le_max_right _ _

theorem env_mono (c : ℕ → ℕ) : Monotone (env c) :=
  monotone_nat_of_le_succ fun n => by
    show env c n ≤ max (env c n) (n + 1 + c (n + 1))
    exact le_max_left _ _

theorem le_env (c : ℕ → ℕ) (n : ℕ) : n ≤ env c n :=
  (Nat.le_add_right n (c n)).trans (add_le_env c n)

end Algebra

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
  (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
  (K : P.OrderedAffineCover)

theorem sub_mem_of_le (t : ℕ → F.cochain K 0)
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)))
    {n m : ℕ} (h : n ≤ m) :
    t m - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) := by
  induction h with
  | refl => simp
  | @step m hnm ih =>
    have h1 : t (m + 1) - t m ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) :=
      pow_smul_le_pow_smul I ⊤ (Nat.succ_le_succ hnm) (ht m)
    have : t (m + 1) - t n = (t (m + 1) - t m) + (t m - t n) := by abel
    rw [this]
    exact Submodule.add_mem _ h1 ih

theorem sub_mem_of_le_of_le (t : ℕ → F.cochain K 0)
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)))
    {n k l : ℕ} (hk : n ≤ k) (hl : n ≤ l) :
    t k - t l ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) := by
  have : t k - t l = (t k - t n) - (t l - t n) := by abel
  rw [this]
  exact Submodule.sub_mem _ (sub_mem_of_le I q F K t ht hk) (sub_mem_of_le I q F K t ht hl)

include hc hqc in

theorem main (t : ℕ → F.cochain K 0)
    (hd : ∀ n : ℕ, F.d K 0 (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 1)))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0))) :
    ∃! a : F.cochain K 0, F.d K 0 a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) := by
  classical

  let J : ℕ → Submodule A (F.cochain K 0) := fun n => I ^ n • ⊤
  have hJ : ∀ {m n : ℕ}, m ≤ n → J n ≤ J m := fun h => pow_smul_le_pow_smul I ⊤ h

  haveI hfin : Module.Finite A (F.H0 K) :=
    (AlgebraicGeometry.OModulePresheaf.cechFinite_of_isProper F hc hqc K).1
  haveI hcomplete : IsAdicComplete I (F.H0 K) :=
    IsAdicComplete.of_finite_of_isNoetherianRing I (F.H0 K)

  have step1 : ∀ n : ℕ, ∃ a : F.cochain K 0, F.d K 0 a = 0 ∧ ∃ k : ℕ, n ≤ k ∧ t k - a ∈ J n := by
    intro n
    obtain ⟨c, hcn⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
        I q F hc hqc K n
    have hdt : F.d K 0 (t (n + c)) ∈ I ^ (n + c) • (⊤ : Submodule A (F.cochain K 1)) :=
      pow_smul_le_pow_smul I ⊤ (Nat.le_succ (n + c)) (hd (n + c))
    obtain ⟨a, hda, hta⟩ := hcn (t (n + c)) hdt
    exact ⟨a, hda, n + c, Nat.le_add_right n c, hta⟩
  choose a hda k hnk hka using step1

  have step2 : ∀ n : ℕ, ∃ c : ℕ, ∀ x : F.cochain K 0, x ∈ F.H0 K → x ∈ J (n + c) → x ∈ I ^ n • F.H0 K := by
    intro n
    obtain ⟨c, hcle⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_H0_inf_pow_smul_le_pow_smul_H0_of_isProper I q F hc hqc K n
    exact ⟨c, fun x hxH hxJ => hcle (Submodule.mem_inf.mpr ⟨hxH, hxJ⟩)⟩
  choose c₂ hc₂ using step2

  have hamem : ∀ n, a n ∈ F.H0 K := fun n => LinearMap.mem_ker.mpr (hda n)
  have hasub : ∀ {n m : ℕ}, n ≤ m → a m - a n ∈ J n := by
    intro n m hnm
    have h1 : a m - t (k m) ∈ J n := by
      have : a m - t (k m) = -(t (k m) - a m) := by abel
      rw [this]; exact Submodule.neg_mem _ (hJ hnm (hka m))
    have h2 : t (k m) - t (k n) ∈ J n :=
      hJ (Nat.le_succ n) (sub_mem_of_le_of_le I q F K t ht (hnm.trans (hnk m)) (hnk n))
    have h3 : t (k n) - a n ∈ J n := hka n
    have : a m - a n = (a m - t (k m)) + (t (k m) - t (k n)) + (t (k n) - a n) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3

  let e : ℕ → ℕ := env c₂
  let b : ℕ → F.H0 K := fun n => ⟨a (e n), hamem (e n)⟩
  have hb : ∀ {n m : ℕ}, n ≤ m → b m - b n ∈ I ^ n • (⊤ : Submodule A (F.H0 K)) := by
    intro n m hnm
    rw [← coe_mem_smul_iff]
    have hdiff : ((b m - b n : F.H0 K) : F.cochain K 0) = a (e m) - a (e n) := rfl
    rw [hdiff]
    refine hc₂ n _ (Submodule.sub_mem _ (hamem _) (hamem _)) ?_
    exact hJ (add_le_env c₂ n) (hasub (env_mono c₂ hnm))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hcomplete.toIsPrecomplete (f := b) fun {m n} hmn => by
    rw [SModEq.sub_mem]
    have : b m - b n = -(b n - b m) := by abel
    rw [this]
    exact Submodule.neg_mem _ (hb hmn)

  have hLb : ∀ n, (L : F.cochain K 0) - a (e n) ∈ J n := by
    intro n
    have h := (SModEq.sub_mem.mp (hL n))

    have h' : ((b n - L : F.H0 K) : F.cochain K 0) ∈ I ^ n • F.H0 K := (coe_mem_smul_iff _ _ _).mpr h
    have h'' : a (e n) - (L : F.cochain K 0) ∈ J n := Submodule.smul_mono le_rfl le_top h'
    have : (L : F.cochain K 0) - a (e n) = -(a (e n) - (L : F.cochain K 0)) := by abel
    rw [this]; exact Submodule.neg_mem _ h''

  refine ⟨(L : F.cochain K 0), ⟨LinearMap.mem_ker.mp L.2, fun n => ?_⟩, ?_⟩
  · have h1 : (L : F.cochain K 0) - a (e (n + 1)) ∈ J (n + 1) := hLb (n + 1)
    have h2 : a (e (n + 1)) - t (k (e (n + 1))) ∈ J (n + 1) := by
      have : a (e (n + 1)) - t (k (e (n + 1))) = -(t (k (e (n + 1))) - a (e (n + 1))) := by abel
      rw [this]
      exact Submodule.neg_mem _ (hJ (le_env c₂ (n + 1)) (hka (e (n + 1))))
    have h3 : t (k (e (n + 1))) - t n ∈ J (n + 1) :=
      sub_mem_of_le I q F K t ht ((Nat.le_succ n).trans ((le_env c₂ (n + 1)).trans (hnk _)))
    have : (L : F.cochain K 0) - t n
        = ((L : F.cochain K 0) - a (e (n + 1))) + (a (e (n + 1)) - t (k (e (n + 1))))
          + (t (k (e (n + 1))) - t n) := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3

  · rintro a' ⟨hda', hta'⟩
    have hδH : a' - (L : F.cochain K 0) ∈ F.H0 K :=
      Submodule.sub_mem _ (LinearMap.mem_ker.mpr hda') L.2
    have hδJ : ∀ m, a' - (L : F.cochain K 0) ∈ J m := by
      intro m
      have h1 : a' - t m ∈ J m := hJ (Nat.le_succ m) (hta' m)
      have h2 : (L : F.cochain K 0) - t m ∈ J m := by
        have h1' : (L : F.cochain K 0) - a (e (m + 1)) ∈ J m := hJ (Nat.le_succ m) (hLb (m + 1))
        have h2' : a (e (m + 1)) - t (k (e (m + 1))) ∈ J m := by
          have : a (e (m + 1)) - t (k (e (m + 1))) = -(t (k (e (m + 1))) - a (e (m + 1))) := by abel
          rw [this]
          exact Submodule.neg_mem _
            (hJ ((Nat.le_succ m).trans (le_env c₂ (m + 1))) (hka (e (m + 1))))
        have h3' : t (k (e (m + 1))) - t m ∈ J m :=
          hJ (Nat.le_succ m)
            (sub_mem_of_le I q F K t ht ((Nat.le_succ m).trans ((le_env c₂ (m + 1)).trans (hnk _))))
        have : (L : F.cochain K 0) - t m
            = ((L : F.cochain K 0) - a (e (m + 1))) + (a (e (m + 1)) - t (k (e (m + 1))))
              + (t (k (e (m + 1))) - t m) := by abel
        rw [this]
        exact Submodule.add_mem _ (Submodule.add_mem _ h1' h2') h3'
      have : a' - (L : F.cochain K 0) = (a' - t m) - ((L : F.cochain K 0) - t m) := by abel
      rw [this]
      exact Submodule.sub_mem _ h1 h2

    let δ : F.H0 K := ⟨a' - (L : F.cochain K 0), hδH⟩
    have hδ0 : δ = 0 := by
      refine IsHausdorff.haus hcomplete.toIsHausdorff δ fun n => ?_
      rw [SModEq.sub_mem, sub_zero, ← coe_mem_smul_iff]
      exact hc₂ n _ hδH (hδJ (n + c₂ n))
    have : a' - (L : F.cochain K 0) = 0 := congrArg Subtype.val hδ0
    exact sub_eq_zero.mp this

end Main

end FF0LimAux

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (t : ℕ → F.cochain K 0)
    (hd : ∀ n : ℕ, F.d K 0 (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 1)))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0))) :
    ∃! a : F.cochain K 0, F.d K 0 a = 0 ∧
      ∀ n : ℕ, a - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K 0)) :=
  FF0LimAux.main I q F hc hqc K t hd ht

end S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_existsUnique_d_eq_zero_forall_sub_mem_pow_smul_of_isAdicComplete_of_isProper (solution)
