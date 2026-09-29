-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d7ec9cf9-bb46-5de8-a2fb-52a047e9cb5b

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace D1sAux

def env (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => c 0
  | n + 1 => max (env c n) (c (n + 1))

theorem le_env (c : ℕ → ℕ) : ∀ n, c n ≤ env c n
  | 0 => le_rfl
  | _ + 1 => le_max_right _ _

theorem env_mono (c : ℕ → ℕ) : Monotone (env c) :=
  monotone_nat_of_le_succ fun n => show env c n ≤ max (env c n) (c (n + 1)) from le_max_left _ _

end D1sAux

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (K : P.OrderedAffineCover) (i : ℕ) (t : ℕ → F.cochain K (i + 1))
    (hd : ∀ n : ℕ, F.d K (i + 1) (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 2))))
    (ht : ∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1)))) :
    ∃ (a : F.cochain K (i + 1)) (Y : ℕ → F.cochain K i), F.d K (i + 1) a = 0 ∧
      (∀ n : ℕ, t n - a - F.d K i (Y n) ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K (i + 1)))) ∧
      (∀ n : ℕ, Y (n + 1) - Y n ∈ I ^ (n + 1) • (⊤ : Submodule A (F.cochain K i))) := by
  classical

  let J : ℕ → Submodule A (F.cochain K (i + 1)) := fun n => I ^ n • ⊤
  have hJ : ∀ {m n : ℕ}, m ≤ n → J n ≤ J m := fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  let J₀ : ℕ → Submodule A (F.cochain K i) := fun n => I ^ n • ⊤
  have hJ₀ : ∀ {m n : ℕ}, m ≤ n → J₀ n ≤ J₀ m := fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

  have htele : ∀ {n m : ℕ}, n ≤ m → t m - t n ∈ J (n + 1) := by
    intro n m h
    induction h with
    | refl => simp
    | @step m hnm ih =>
      have : t (m + 1) - t n = (t (m + 1) - t m) + (t m - t n) := by abel
      rw [this]
      exact Submodule.add_mem _ (hJ (Nat.succ_le_succ hnm) (ht m)) ih

  have hML : ∀ n : ℕ, ∃ c : ℕ, ∀ w : (F.cochain K i), F.d K i w ∈ J (n + c) →
      ∃ z : (F.cochain K i), F.d K i z = 0 ∧ w - z ∈ J₀ n := by
    intro n
    cases i with
    | zero =>
      exact AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_sub_mem_pow_of_d_mem_pow_of_isProper I q F hc hqc K n
    | succ j =>
      exact AlgebraicGeometry.OModulePresheaf.exists_d_succ_eq_zero_sub_mem_pow_of_d_succ_mem_pow_of_isProper I q F hc hqc K j n
  choose c hc' using hML

  obtain ⟨a, hda, ha⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_d_eq_zero_forall_sub_mem_pow_smul_sup_range_d_of_isAdicComplete_of_isProper
      I q F hc hqc K i t hd (fun n => Submodule.mem_sup_left (ht n))
  have hy : ∀ n, ∃ y : (F.cochain K i), t n - a - F.d K i y ∈ J (n + 1) := by
    intro n
    obtain ⟨e, he, b, ⟨y, rfl⟩, heb⟩ := Submodule.mem_sup.mp (ha n)
    refine ⟨-y, ?_⟩
    have : t n - a - F.d K i (-y) = -(a - t n - F.d K i y) := by rw [map_neg]; abel
    rw [this]
    refine Submodule.neg_mem _ ?_
    have : a - t n - F.d K i y = e := by rw [← heb]; abel
    rw [this]; exact he
  choose y hy' using hy

  let m : ℕ → ℕ := D1sAux.env fun n => n + 1 + c (n + 1)
  have hm : ∀ n, n + 1 + c (n + 1) ≤ m n := fun n => D1sAux.le_env (fun k => k + 1 + c (k + 1)) n
  have hmn : ∀ n, n ≤ m n := fun n => le_trans (by omega) (hm n)
  have hmmono : Monotone m := D1sAux.env_mono (fun k => k + 1 + c (k + 1))

  have hz : ∀ n, ∃ z : (F.cochain K i), F.d K i z = 0 ∧ (y (m (n + 1)) - y (m n)) - z ∈ J₀ (n + 1) := by
    intro n
    refine hc' (n + 1) _ ?_
    have h1 : F.d K i (y (m (n + 1)) - y (m n)) =
        (t (m (n + 1)) - t (m n)) - (t (m (n + 1)) - a - F.d K i (y (m (n + 1)))) + (t (m n) - a - F.d K i (y (m n))) := by
      rw [map_sub]; abel
    rw [h1]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
    · exact hJ (by have := hm n; omega) (htele (hmmono (Nat.le_add_right n 1)))
    · exact hJ (by have := hm n; have := hmmono (Nat.le_add_right n 1); omega) (hy' (m (n + 1)))
    · exact hJ (by have := hm n; omega) (hy' (m n))
  choose z hdz hz' using hz

  refine ⟨a, fun n => y (m n) - ∑ k ∈ Finset.range n, z k, hda, fun n => ?_, fun n => ?_⟩
  · have hdsum : F.d K i (∑ k ∈ Finset.range n, z k) = 0 := by
      rw [map_sum]; exact Finset.sum_eq_zero fun k _ => hdz k
    have : t n - a - F.d K i (y (m n) - ∑ k ∈ Finset.range n, z k)
        = (t n - t (m n)) + (t (m n) - a - F.d K i (y (m n))) := by
      rw [map_sub, hdsum]; abel
    rw [this]
    refine Submodule.add_mem _ ?_ (hJ (Nat.succ_le_succ (hmn n)) (hy' (m n)))
    have : t n - t (m n) = -(t (m n) - t n) := by abel
    rw [this]; exact Submodule.neg_mem _ (htele (hmn n))
  · have : (y (m (n + 1)) - ∑ k ∈ Finset.range (n + 1), z k) - (y (m n) - ∑ k ∈ Finset.range n, z k)
        = (y (m (n + 1)) - y (m n)) - z n := by
      rw [Finset.sum_range_succ]; abel
    rw [this]; exact hz' n

end S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper (solution)
