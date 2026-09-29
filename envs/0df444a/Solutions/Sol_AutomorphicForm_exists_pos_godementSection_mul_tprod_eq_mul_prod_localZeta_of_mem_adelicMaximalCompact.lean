-- Prove2me | solution 1 for AutomorphicForm.exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4aff274b-84fa-5fc1-9e88-bbe65d8c2e26

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Theorems.Thm_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal ENNReal

namespace R4G1E
namespace EulerBookkeeping

open Finsupp Filter Topology

variable {ι : Type*}

def mono (a : ι → ℂ) (k : ι →₀ ℕ) : ℂ := k.prod fun i n => a i ^ n

theorem mono_zero (a : ι → ℂ) : mono a 0 = 1 := Finsupp.prod_zero_index

theorem mono_add (a : ι → ℂ) (k l : ι →₀ ℕ) : mono a (k + l) = mono a k * mono a l :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem mono_single (a : ι → ℂ) (i : ι) (n : ℕ) : mono a (single i n) = a i ^ n :=
  Finsupp.prod_single_index (pow_zero _)

theorem norm_mono (a : ι → ℂ) (k : ι →₀ ℕ) : ‖mono a k‖ = k.prod fun i n => ‖a i‖ ^ n := by
  unfold mono Finsupp.prod
  rw [norm_prod]
  exact Finset.prod_congr rfl fun i _ => norm_pow _ _

section Restricted

variable (a : ι → ℂ) [DecidableEq ι]

def sigmaT (T : Finset ι) : ℂ := ∑' k : ι →₀ ℕ, if ∀ i ∈ T, k i = 0 then mono a k else 0

variable {a}

omit [DecidableEq ι] in
theorem sigmaT_empty : sigmaT a ∅ = ∑' k, mono a k := by
  unfold sigmaT
  exact tsum_congr fun k => by simp

omit [DecidableEq ι] in
theorem summable_restrict (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) (p : (ι →₀ ℕ) → Prop)
    [DecidablePred p] : Summable fun k : ι →₀ ℕ => if p k then mono a k else 0 :=
  Summable.of_norm_bounded hF fun k => by
    split_ifs
    · exact le_rfl
    · simp

omit [DecidableEq ι] in
theorem summable_norm_of_summable_mono (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) :
    Summable fun i => ‖a i‖ := by
  have h := hF.comp_injective (Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0))
  refine h.congr fun i => ?_
  show ‖mono a (single i 1)‖ = ‖a i‖
  rw [mono_single, pow_one]

theorem sigmaT_insert (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) {T : Finset ι} {i : ι} (hi : i ∉ T) :
    sigmaT a (insert i T) = (1 - a i) * sigmaT a T := by
  set FT : (ι →₀ ℕ) → ℂ := fun k => if ∀ j ∈ T, k j = 0 then mono a k else 0 with hFT
  set G1 : (ι →₀ ℕ) → ℂ := fun k => if (∀ j ∈ T, k j = 0) ∧ k i = 0 then mono a k else 0 with hG1
  set G2 : (ι →₀ ℕ) → ℂ := fun k => if (∀ j ∈ T, k j = 0) ∧ k i ≠ 0 then mono a k else 0 with hG2
  have hsplit : ∀ k, FT k = G1 k + G2 k := by
    intro k
    simp only [hFT, hG1, hG2]
    by_cases h1 : ∀ j ∈ T, k j = 0
    · by_cases h2 : k i = 0
      · rw [if_pos h1, if_pos ⟨h1, h2⟩, if_neg (fun h => h.2 h2), add_zero]
      · rw [if_pos h1, if_neg (fun h => h2 h.2), if_pos ⟨h1, h2⟩, zero_add]
    · rw [if_neg h1, if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1), add_zero]
  have hins : sigmaT a (insert i T) = ∑' k, G1 k := by
    unfold sigmaT
    refine tsum_congr fun k => ?_
    simp only [hG1, Finset.forall_mem_insert, and_comm]
  have hG1s : Summable G1 := by
    simpa [hG1] using summable_restrict hF (fun k => (∀ j ∈ T, k j = 0) ∧ k i = 0)
  have hG2s : Summable G2 := by
    simpa [hG2] using summable_restrict hF (fun k => (∀ j ∈ T, k j = 0) ∧ k i ≠ 0)
  set φ : (ι →₀ ℕ) → (ι →₀ ℕ) := fun k => k + single i 1 with hφ
  have hφinj : Function.Injective φ := add_left_injective (single i 1)
  have hsupp : Function.support G2 ⊆ Set.range φ := by
    intro k hk
    have hki : k i ≠ 0 := by
      by_contra h0
      apply hk
      simp [hG2, h0]
    refine ⟨k - single i 1, ?_⟩
    show k - single i 1 + single i 1 = k
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hki))
  have hcomp : ∀ k, G2 (φ k) = FT k * a i := by
    intro k
    have hTi : (∀ j ∈ T, ((k + single i 1 : ι →₀ ℕ)) j = 0) ↔ ∀ j ∈ T, k j = 0 := by
      refine forall₂_congr fun j hj => ?_
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hji, add_zero]
    have hii : ((k + single i 1 : ι →₀ ℕ)) i ≠ 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_same]; exact Nat.succ_ne_zero _
    simp only [hG2, hFT, hφ, hTi, hii, ne_eq, not_false_eq_true, and_true]
    split_ifs
    · rw [mono_add, mono_single, pow_one]
    · rw [zero_mul]
  have hG2sum : ∑' k, G2 k = sigmaT a T * a i := by
    rw [← hφinj.tsum_eq hsupp]
    simp only [hcomp]
    rw [tsum_mul_right]
    rfl
  have hT : sigmaT a T = ∑' k, G1 k + ∑' k, G2 k := by
    rw [← (hG1s.hasSum.add hG2s.hasSum).tsum_eq]
    unfold sigmaT
    exact tsum_congr fun k => hsplit k
  rw [hins]
  have := hT
  rw [hG2sum] at this
  linear_combination -this

theorem sigmaT_eq_prod_mul (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) (T : Finset ι) :
    sigmaT a T = (∏ i ∈ T, (1 - a i)) * ∑' k, mono a k := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, one_mul, sigmaT_empty]
  | insert i T hi ih => rw [sigmaT_insert hF hi, ih, Finset.prod_insert hi, mul_assoc]

theorem norm_sigmaT_sub_one_le (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) (T : Finset ι) :
    ‖sigmaT a T - 1‖ ≤ (∑' i, if i ∈ T then 0 else ‖a i‖) * ∑' k, ‖mono a k‖ := by
  set R : (ι →₀ ℕ) → ℂ := fun k => if (∀ j ∈ T, k j = 0) ∧ k ≠ 0 then mono a k else 0 with hR
  have hRs : Summable R := by simpa [hR] using summable_restrict hF (fun k => (∀ j ∈ T, k j = 0) ∧ k ≠ 0)
  have hRn : Summable fun k => ‖R k‖ := by
    refine Summable.of_norm_bounded hF fun k => ?_
    simp only [hR, norm_norm]
    split_ifs
    · exact le_rfl
    · simp
  have hsub : sigmaT a T - 1 = ∑' k, R k := by
    have h0 : ∀ k : ι →₀ ℕ, (if ∀ j ∈ T, k j = 0 then mono a k else 0)
        = (if k = 0 then (1 : ℂ) else 0) + R k := by
      intro k
      by_cases hk : k = 0
      · subst hk
        simp [hR, mono_zero]
      · simp only [hR, hk, if_false, zero_add, ne_eq, not_false_eq_true, and_true]
    unfold sigmaT
    rw [tsum_congr h0, ((hasSum_ite_eq (0 : ι →₀ ℕ) (1 : ℂ)).add hRs.hasSum).tsum_eq]
    ring
  rw [hsub]
  refine (norm_tsum_le_tsum_norm hRn).trans ?_
  set A : Set (ι →₀ ℕ) := {k | (∀ j ∈ T, k j = 0) ∧ k ≠ 0} with hA
  have hRA : ∀ k, ‖R k‖ = A.indicator (fun k => ‖mono a k‖) k := by
    intro k
    simp only [hR, hA, Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs <;> simp
  rw [tsum_congr hRA, ← tsum_subtype]
  have hne : ∀ k : A, (k.1).support.Nonempty := fun k => Finsupp.support_nonempty_iff.mpr k.2.2
  set j : A → ι := fun k => (hne k).choose with hj
  have hjmem : ∀ k : A, j k ∈ (k.1).support := fun k => (hne k).choose_spec
  have hjpos : ∀ k : A, 1 ≤ k.1 (j k) := fun k =>
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (hjmem k))
  have hjT : ∀ k : A, j k ∉ T := by
    intro k hkT
    exact (Finsupp.mem_support_iff.mp (hjmem k)) (k.2.1 (j k) hkT)
  set e : A → ι × (ι →₀ ℕ) := fun k => (j k, k.1 - single (j k) 1) with he
  have hdecomp : ∀ k : A, k.1 - single (j k) 1 + single (j k) 1 = k.1 := fun k =>
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (hjpos k))
  have heinj : Function.Injective e := by
    intro k k' h
    simp only [he, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext
    rw [← hdecomp k, ← hdecomp k', h2, h1]
  set g : ι × (ι →₀ ℕ) → ℝ := fun p => (if p.1 ∈ T then 0 else ‖a p.1‖) * ‖mono a p.2‖ with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => mul_nonneg (by split_ifs <;> simp) (norm_nonneg _)
  have hcT : Summable fun i => if i ∈ T then (0 : ℝ) else ‖a i‖ := by
    refine Summable.of_norm_bounded (summable_norm_of_summable_mono hF) fun i => ?_
    split_ifs <;> simp
  have hcTn : Summable fun i => ‖if i ∈ T then (0 : ℝ) else ‖a i‖‖ := by
    refine hcT.norm.congr fun i => ?_
    rfl
  have hFn : Summable fun k : ι →₀ ℕ => ‖‖mono a k‖‖ := by simpa using hF
  have hgs : Summable g := by
    simpa [hg] using summable_mul_of_summable_norm hcTn hFn
  have hle : ∀ k : A, ‖mono a k.1‖ ≤ g (e k) := by
    intro k
    simp only [hg, he, hjT k, if_false]
    conv_lhs => rw [← hdecomp k, mono_add, norm_mul, mono_single, pow_one, mul_comm]
  calc ∑' k : A, ‖mono a k.1‖
      ≤ ∑' p, g p := Summable.tsum_le_tsum_of_inj e heinj (fun p _ => hg0 p) hle (hF.subtype A) hgs
    _ = (∑' i, if i ∈ T then (0 : ℝ) else ‖a i‖) * ∑' k, ‖mono a k‖ := by
        rw [tsum_mul_tsum_of_summable_norm hcTn hFn]

theorem tendsto_sigmaT (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) :
    Tendsto (fun T : Finset ι => sigmaT a T) atTop (𝓝 1) := by
  have htail : Tendsto (fun T : Finset ι => ∑' i, if i ∈ T then (0 : ℝ) else ‖a i‖) atTop (𝓝 0) := by
    have h := tendsto_tsum_compl_atTop_zero fun i => ‖a i‖
    refine h.congr fun T => ?_
    refine (tsum_subtype ({x | x ∉ T} : Set ι) (fun i => ‖a i‖)).trans ?_
    refine tsum_congr fun i => ?_
    by_cases hi : i ∈ T
    · rw [if_pos hi, Set.indicator_of_notMem (by simpa using hi)]
    · rw [if_neg hi, Set.indicator_of_mem (by simpa using hi)]
  have hbound := htail.mul_const (∑' k, ‖mono a k‖)
  rw [zero_mul] at hbound
  have h0 : Tendsto (fun T : Finset ι => sigmaT a T - 1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => norm_sigmaT_sub_one_le hF T) hbound
  have := h0.add_const 1
  simpa using this

end Restricted

section Main

variable {a : ι → ℂ}

theorem tsum_mono_mul_tprod_one_sub (hF : Summable fun k : ι →₀ ℕ => ‖mono a k‖) :
    (∑' k, mono a k) * ∏' i, (1 - a i) = 1 := by
  classical
  have ha := summable_norm_of_summable_mono hF
  have hmult : Multipliable fun i => 1 - a i := by
    have h := multipliable_one_add_of_summable (f := fun i => -a i) (by simpa using ha)
    simpa [sub_eq_add_neg] using h
  have hprod : Tendsto (fun T : Finset ι => ∏ i ∈ T, (1 - a i)) atTop (𝓝 (∏' i, (1 - a i))) := by
    have h := hmult.hasProd
    rw [HasProd] at h
    simpa using h
  have h1 : Tendsto (fun T : Finset ι => sigmaT a T) atTop (𝓝 ((∏' i, (1 - a i)) * ∑' k, mono a k)) := by
    have h := hprod.mul_const (∑' k, mono a k)
    refine h.congr fun T => ?_
    rw [sigmaT_eq_prod_mul hF T]
  have h2 := tendsto_sigmaT hF
  have heq := tendsto_nhds_unique h1 h2
  rw [mul_comm] at heq
  exact heq

def monoN (a : ι → ℂ) (k : ι →₀ ℕ) : ℝ := k.prod fun i n => ‖a i‖ ^ n

theorem monoN_eq_norm_mono (k : ι →₀ ℕ) : monoN a k = ‖mono a k‖ := (norm_mono a k).symm

theorem monoN_nonneg (k : ι →₀ ℕ) : 0 ≤ monoN a k := by
  rw [monoN_eq_norm_mono]; exact norm_nonneg _

theorem monoN_add (k l : ι →₀ ℕ) : monoN a (k + l) = monoN a k * monoN a l :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem monoN_single (i : ι) (n : ℕ) : monoN a (single i n) = ‖a i‖ ^ n :=
  Finsupp.prod_single_index (pow_zero _)

theorem monoN_zero : monoN a 0 = 1 := Finsupp.prod_zero_index

theorem sum_monoN_le_prod [DecidableEq ι] (h1 : ∀ i, ‖a i‖ < 1) (T : Finset ι) :
    ∀ u : Finset (ι →₀ ℕ), (∀ k ∈ u, k.support ⊆ T) → ∑ k ∈ u, monoN a k ≤ ∏ i ∈ T, (1 - ‖a i‖)⁻¹ := by
  induction T using Finset.induction_on with
  | empty =>
      intro u hu
      have hu0 : u ⊆ {0} := by
        intro k hk
        rw [Finset.mem_singleton, ← Finsupp.support_eq_empty]
        exact Finset.subset_empty.mp (hu k hk)
      calc ∑ k ∈ u, monoN a k ≤ ∑ k ∈ ({0} : Finset (ι →₀ ℕ)), monoN a k :=
            Finset.sum_le_sum_of_subset_of_nonneg hu0 fun k _ _ => monoN_nonneg k
        _ = 1 := by rw [Finset.sum_singleton, monoN_zero]
        _ = ∏ i ∈ (∅ : Finset ι), (1 - ‖a i‖)⁻¹ := (Finset.prod_empty).symm
  | insert i T hi ih =>
      intro u hu
      set φ : (ι →₀ ℕ) → ℕ × (ι →₀ ℕ) := fun k => (k i, k.erase i) with hφ
      have hφinj : Set.InjOn φ u := by
        intro k _ k' _ h
        simp only [hφ, Prod.mk.injEq] at h
        rw [← Finsupp.single_add_erase i k, ← Finsupp.single_add_erase i k', h.1, h.2]
      have hterm : ∀ k, monoN a k = ‖a i‖ ^ (φ k).1 * monoN a (φ k).2 := by
        intro k
        conv_lhs => rw [← Finsupp.single_add_erase i k, monoN_add, monoN_single]
      set N : Finset ℕ := u.image fun k => k i with hN
      set U : Finset (ι →₀ ℕ) := u.image fun k => k.erase i with hU
      have hUT : ∀ k' ∈ U, k'.support ⊆ T := by
        intro k' hk'
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hk'
        rw [Finsupp.support_erase]
        intro j hj
        have hj' := Finset.mem_erase.mp hj
        have := hu k hk hj'.2
        rcases Finset.mem_insert.mp this with h | h
        · exact (hj'.1 h).elim
        · exact h
      have himg : u.image φ ⊆ N ×ˢ U := by
        intro p hp
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hk, Finset.mem_image_of_mem _ hk⟩
      have hgeom : ∑ n ∈ N, ‖a i‖ ^ n ≤ (1 - ‖a i‖)⁻¹ := by
        rw [← tsum_geometric_of_lt_one (norm_nonneg _) (h1 i)]
        exact (summable_geometric_of_lt_one (norm_nonneg _) (h1 i)).sum_le_tsum N
          fun n _ => pow_nonneg (norm_nonneg _) n
      have hpos : ∀ j, 0 ≤ (1 - ‖a j‖)⁻¹ := fun j => inv_nonneg.mpr (sub_nonneg.mpr (h1 j).le)
      calc ∑ k ∈ u, monoN a k
          = ∑ k ∈ u, ‖a i‖ ^ (φ k).1 * monoN a (φ k).2 := Finset.sum_congr rfl fun k _ => hterm k
        _ = ∑ p ∈ u.image φ, ‖a i‖ ^ p.1 * monoN a p.2 :=
            (Finset.sum_image (f := fun p : ℕ × (ι →₀ ℕ) => ‖a i‖ ^ p.1 * monoN a p.2) hφinj).symm
        _ ≤ ∑ p ∈ N ×ˢ U, ‖a i‖ ^ p.1 * monoN a p.2 :=
            Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ =>
              mul_nonneg (pow_nonneg (norm_nonneg _) _) (monoN_nonneg _)
        _ = (∑ n ∈ N, ‖a i‖ ^ n) * ∑ k' ∈ U, monoN a k' := by
            rw [Finset.sum_product, Finset.sum_mul_sum]
        _ ≤ (1 - ‖a i‖)⁻¹ * ∏ j ∈ T, (1 - ‖a j‖)⁻¹ :=
            mul_le_mul hgeom (ih U hUT) (Finset.sum_nonneg fun k _ => monoN_nonneg k) (hpos i)
        _ = ∏ j ∈ insert i T, (1 - ‖a j‖)⁻¹ := by rw [Finset.prod_insert hi]

theorem summable_norm_div_one_sub (ha : Summable fun i => ‖a i‖) (h1 : ∀ i, ‖a i‖ < 1) :
    Summable fun i => ‖a i‖ / (1 - ‖a i‖) := by
  have hsub : ∀ i, 0 < 1 - ‖a i‖ := fun i => sub_pos.mpr (h1 i)
  have hev : ∀ᶠ i in cofinite, ‖a i‖ < 1 / 2 := ha.tendsto_cofinite_zero (eventually_lt_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually (ha.mul_left 2) ?_
  filter_upwards [hev] with i hi
  have hx : 0 ≤ ‖a i‖ / (1 - ‖a i‖) := div_nonneg (norm_nonneg _) (hsub i).le
  rw [Real.norm_eq_abs, abs_of_nonneg hx, div_le_iff₀ (hsub i)]
  nlinarith [norm_nonneg (a i)]

theorem summable_norm_mono (ha : Summable fun i => ‖a i‖) (h1 : ∀ i, ‖a i‖ < 1) :
    Summable fun k : ι →₀ ℕ => ‖mono a k‖ := by
  classical
  have hsub : ∀ i, 0 < 1 - ‖a i‖ := fun i => sub_pos.mpr (h1 i)
  set c : ι → ℝ := fun i => ‖a i‖ / (1 - ‖a i‖) with hc
  have hcs : Summable c := summable_norm_div_one_sub ha h1
  have hc0 : ∀ i, 0 ≤ c i := fun i => div_nonneg (norm_nonneg _) (hsub i).le
  have hfac : ∀ i, (1 - ‖a i‖)⁻¹ ≤ Real.exp (c i) := by
    intro i
    have heq : (1 - ‖a i‖)⁻¹ = c i + 1 := by
      simp only [hc]
      field_simp [(hsub i).ne']
      ring
    rw [heq]
    exact Real.add_one_le_exp (c i)
  refine (summable_of_sum_le (f := fun k : ι →₀ ℕ => monoN a k) (c := Real.exp (∑' i, c i))
    (fun k => monoN_nonneg k) fun u => ?_).congr fun k => monoN_eq_norm_mono k
  set T : Finset ι := u.biUnion fun k => k.support with hT
  have hu : ∀ k ∈ u, k.support ⊆ T := fun k hk => Finset.subset_biUnion_of_mem (fun k => k.support) hk
  calc ∑ k ∈ u, monoN a k ≤ ∏ i ∈ T, (1 - ‖a i‖)⁻¹ := sum_monoN_le_prod h1 T u hu
    _ ≤ ∏ i ∈ T, Real.exp (c i) :=
        Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (hsub i).le) fun i _ => hfac i
    _ = Real.exp (∑ i ∈ T, c i) := (Real.exp_sum T c).symm
    _ ≤ Real.exp (∑' i, c i) := Real.exp_le_exp.mpr (hcs.sum_le_tsum T fun i _ => hc0 i)

theorem multipliable_one_sub (ha : Summable fun i => ‖a i‖) : Multipliable fun i => 1 - a i := by
  have h := multipliable_one_add_of_summable (f := fun i => -a i) (by simpa using ha)
  simpa [sub_eq_add_neg] using h

theorem tprod_one_sub_ne_zero (ha : Summable fun i => ‖a i‖) (h1 : ∀ i, ‖a i‖ < 1) :
    (∏' i, (1 - a i)) ≠ 0 := by
  intro h0
  have h := tsum_mono_mul_tprod_one_sub (summable_norm_mono ha h1)
  rw [h0, mul_zero] at h
  exact zero_ne_one h

end Main

end R4G1E.EulerBookkeeping

namespace R4G1E

variable (F : Type) [Field F] [NumberField F]

theorem summable_absNorm_rpow_neg {t : ℝ} (ht : 1 < t) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-t) := by
  have hlt := NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top F ht

  set G : (HeightOneSpectrum (𝓞 F) →₀ ℕ) → ℝ≥0∞ := fun k =>
    (((k.prod fun v n => Ideal.absNorm v.asIdeal ^ n : ℕ) : ℝ≥0∞) ^ (-t)) with hG
  have hinj : Function.Injective fun v : HeightOneSpectrum (𝓞 F) => Finsupp.single v (1 : ℕ) :=
    Finsupp.single_left_injective one_ne_zero
  have hle : (∑' v : HeightOneSpectrum (𝓞 F), G (Finsupp.single v 1)) ≤ ∑' k, G k :=
    ENNReal.tsum_comp_le_tsum_of_injective hinj G
  have hfin : (∑' v : HeightOneSpectrum (𝓞 F), G (Finsupp.single v 1)) ≠ ⊤ := ne_top_of_le_ne_top hlt.ne hle
  have hN0 : ∀ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0) ≠ 0 := by
    intro v
    have h1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    have : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hGv : ∀ v : HeightOneSpectrum (𝓞 F),
      G (Finsupp.single v 1) = ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0) ^ (-t) : ℝ≥0) : ℝ≥0∞) := by
    intro v
    simp only [hG]
    rw [Finsupp.prod_single_index (by simp), pow_one, ENNReal.coe_rpow_of_ne_zero (hN0 v)]
    rfl
  rw [tsum_congr hGv] at hfin
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) =>
      (((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0) ^ (-t) : ℝ≥0) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hfin
  have hsumR := NNReal.summable_coe.mpr hsum
  refine hsumR.congr fun v => ?_
  rw [NNReal.coe_rpow]
  rfl

theorem continuous_units_of_continuous_val (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (h : Continuous fun x => ((χ x : ℂˣ) : ℂ)) : Continuous χ := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  simp_rw [Units.val_inv_eq_inv_val]
  exact h.inv₀ fun x => (χ x).ne_zero

theorem continuous_mul_inv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμk : Continuous fun x => ((μ x : ℂˣ) : ℂ)) (hνk : Continuous fun x => ((ν x : ℂˣ) : ℂ)) :
    Continuous (μ * ν⁻¹) := by
  have h1 := continuous_units_of_continuous_val F μ hμk
  have h2 := continuous_units_of_continuous_val F ν hνk
  show Continuous fun x => (μ * ν⁻¹) x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  exact h1.mul h2.inv

theorem isUnitaryChar_mul_inv (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμ : IsUnitaryChar (𝓞 F) F μ) (hν : IsUnitaryChar (𝓞 F) F ν) : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := by
  intro x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
    hμ x, hν x, inv_one, mul_one]

variable {F}

theorem archComponent_glArch_coe (w : InfinitePlace F) (k : AdelicGL2 (𝓞 F) F) :
    (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion)
      = ((archEval F w).comp (adeleArch (𝓞 F) F)).mapMatrix (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j; rfl

theorem finComponent_glFin_coe (v : HeightOneSpectrum (𝓞 F)) (k : AdelicGL2 (𝓞 F) F) :
    (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)).mapMatrix
          (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
  ext i j; rfl

theorem det_fst_apply (w : InfinitePlace F) (k : AdelicGL2 (𝓞 F) F) :
    ((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, archComponent_glArch_coe, ← RingHom.map_det]
  rfl

theorem det_snd_apply (v : HeightOneSpectrum (𝓞 F)) (k : AdelicGL2 (𝓞 F) F) :
    ((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      = (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, finComponent_glFin_coe, ← RingHom.map_det]
  rfl

theorem norm_eq_one_of_valued_eq_one (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (h : Valued.v x = 1) : ‖x‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, h, map_one]; rfl

theorem distribHaarChar_det_eq_one (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F) :
    distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det k) = 1 := by
  have h := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F
    (Matrix.GeneralLinearGroup.det k)
  have harch : ∀ w : InfinitePlace F,
      ‖((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ = 1 := by
    intro w
    rw [det_fst_apply]
    exact (hk.2 w).1
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    intro v
    rw [det_snd_apply]
    exact norm_eq_one_of_valued_eq_one v _ (valued_det_finComponent_eq_one hk v)
  simp only [harch, one_pow, Finset.prod_const_one, hfin, finprod_one, mul_one] at h
  exact_mod_cast h

theorem exists_valued_bottomRow_eq_one (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ i : Fin 2, Valued.v ((finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i) = 1 := by
  set g := (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) with hg
  have hle : ∀ i j, Valued.v (g i j) ≤ 1 := fun i j => (valued_finComponent_apply_le_one hk v i j).1
  have hdet : Valued.v g.det = 1 := valued_det_finComponent_eq_one hk v
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i : Fin 2, Valued.v (g 1 i) < 1 := fun i => lt_of_le_of_ne (hle 1 i) (hcon i)
  have h1 : Valued.v (g 0 0 * g 1 1) < 1 := by
    rw [Valuation.map_mul]
    calc Valued.v (g 0 0) * Valued.v (g 1 1) ≤ 1 * Valued.v (g 1 1) := mul_le_mul_left (hle 0 0) _
      _ = Valued.v (g 1 1) := one_mul _
      _ < 1 := hlt 1
  have h2 : Valued.v (g 0 1 * g 1 0) < 1 := by
    rw [Valuation.map_mul]
    calc Valued.v (g 0 1) * Valued.v (g 1 0) ≤ 1 * Valued.v (g 1 0) := mul_le_mul_left (hle 0 1) _
      _ = Valued.v (g 1 0) := one_mul _
      _ < 1 := hlt 0
  have : Valued.v g.det < 1 := by
    rw [Matrix.det_fin_two]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 h2)
  rw [hdet] at this
  exact lt_irrefl _ this

theorem isFactorizableStandardOutside_slice (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
    (Φa : (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
    (Φf : (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ)
    (hΦ0 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
      (∃ v ∉ S, ∃ i, (x i).2 v ∉ v.adicCompletionIntegers F) → Φ x = 0)
    (hΦ1 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
      (∀ v ∉ S, ∀ i, (x i).2 v ∈ v.adicCompletionIntegers F) →
        Φ x = (∏ w, Φa w (fun i => (x i).1 w)) * ∏ v ∈ S, Φf v (fun i => (x i).2 v))
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F) :
    IsFactorizableStandardOutside (fun t => Φ (bottomRowVec F k t)) S
      (fun w t => Φa w (fun i => t
        * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
      (fun v t => Φf v (fun i => t
        * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i)) := by
  intro x
  have hkint : ∀ (v : HeightOneSpectrum (𝓞 F)) (i : Fin 2),
      ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 i).2 v ∈ v.adicCompletionIntegers F := by
    intro v i
    have h := (mem_finiteIntegralGL2_iff.1 hk.1).1 1 i
    exact h v
  by_cases hx : x ∈ integralOutside S
  · rw [Set.indicator_of_mem hx]
    have hx' : ∀ v ∉ S, (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := hx
    have hrow : ∀ v ∉ S, ∀ i, (bottomRowVec F k x i).2 v ∈ v.adicCompletionIntegers F := by
      intro v hv i
      show (x * (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 i).2 v ∈ v.adicCompletionIntegers F
      exact mul_mem (hx' v hv) (hkint v i)
    show Φ (bottomRowVec F k x) = _
    rw [hΦ1 _ hrow]
    rfl
  · rw [Set.indicator_of_notMem hx]
    show Φ (bottomRowVec F k x) = 0
    have hx' : ∃ v ∉ S, (x.2 : FiniteAdeleRing (𝓞 F) F) v ∉ v.adicCompletionIntegers F := by
      by_contra hcon
      push Not at hcon
      exact hx hcon
    obtain ⟨v, hvS, hv⟩ := hx'
    obtain ⟨i, hi⟩ := exists_valued_bottomRow_eq_one k hk v
    apply hΦ0
    refine ⟨v, hvS, i, ?_⟩
    show (x * (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 i).2 v ∉ v.adicCompletionIntegers F
    intro hmem
    apply hv
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hmem ⊢
    have hi' : Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 i).2 v) = 1 := hi
    have : Valued.v ((x * (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 i).2 v)
        = Valued.v ((x.2 : FiniteAdeleRing (𝓞 F) F) v) := by
      show Valued.v ((x.2 : FiniteAdeleRing (𝓞 F) F) v * ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 i).2 v)
        = _
      rw [Valuation.map_mul, hi', mul_one]
    rwa [this] at hmem

variable (F)

theorem main
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace w.Completion] [∀ w : InfinitePlace F, BorelSpace w.Completion]
    (μa : (w : InfinitePlace F) → Measure w.Completion) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧
      ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
        (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
        (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
        (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
        (_hS : ∀ v ∉ S, IsUnramifiedCharAt (μ * ν⁻¹) v)
        (s : ℂ) (_hs : 0 < s.re),
        Multipliable (fun v : {v // v ∉ S} =>
            1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ∧
        (∏' v : {v // v ∉ S},
            (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) ≠ 0 ∧
        ∀ (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
          (Φa : (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
          (Φf : (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ)
          (_hΦ0 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∃ v ∉ S, ∃ i, (x i).2 v ∉ v.adicCompletionIntegers F) → Φ x = 0)
          (_hΦ1 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∀ v ∉ S, ∀ i, (x i).2 v ∈ v.adicCompletionIntegers F) →
              Φ x = (∏ w, Φa w (fun i => (x i).1 w)) * ∏ v ∈ S, Φf v (fun i => (x i).2 v))
          (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ adelicMaximalCompact F),
          godementSection F ν₀ μ ν α hα Φ s k
              * ∏' v : {v // v ∉ S},
                  (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
            = c * ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
                * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                    (fun t => Φa w (fun i => t
                      * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                    (archLocalChar (μ * ν⁻¹) w) (2 * s + 1))
                * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                    (fun t => Φf v (fun i => t
                      * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
                          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i))
                    (localChar (μ * ν⁻¹) v) (2 * s + 1) := by
  intro α hα
  obtain ⟨c, hc, H⟩ := NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq F ν₀ S μf μa ϖ hϖ
  refine ⟨c, hc, ?_⟩
  intro μ ν hμ hν hμc hνc hS s hs
  have hχc : Continuous (μ * ν⁻¹) := continuous_mul_inv F μ ν hμc hνc
  have hχu : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := isUnitaryChar_mul_inv F μ ν hμ hν
  have hz : 1 < (2 * s + 1).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      Complex.one_re]
    linarith

  have hEul : (Multipliable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
        * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ∧
      (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) ≠ 0 := by
    set a : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} → ℂ := fun v =>
      ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
        * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)) with ha_def
    have hN1 : ∀ v : HeightOneSpectrum (𝓞 F), 1 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := fun v => by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hnorm : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        ‖a v‖ = ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re + 1)) := by
      intro v
      rw [ha_def]
      dsimp only
      rw [norm_mul, localChar_apply, hχu, one_mul,
        Complex.norm_natCast_cpow_of_pos (by have := hN1 v.1; exact_mod_cast (zero_lt_one.trans this))]
      congr 1
      simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
        sub_zero, Complex.one_re]
    have hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => ‖a v‖ := by
      have ht : 1 < 2 * s.re + 1 := by linarith
      have h := (summable_absNorm_rpow_neg F ht).subtype fun v => v ∉ S
      refine h.congr fun v => ?_
      rw [hnorm]
      rfl
    have hlt1 : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, ‖a v‖ < 1 := by
      intro v
      rw [hnorm]
      exact Real.rpow_lt_one_of_one_lt_of_neg (hN1 v.1) (by linarith)
    exact ⟨EulerBookkeeping.multipliable_one_sub hsum, EulerBookkeeping.tprod_one_sub_ne_zero hsum hlt1⟩
  refine ⟨hEul.1, hEul.2, ?_⟩
  · intro Φ Φa Φf hΦ0 hΦ1 k hk

    have hcp : ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) = 1 := by
      rw [cpowChar_apply_val]
      have : ((α (Matrix.GeneralLinearGroup.det k) : ℝˣ) : ℝ) = 1 := by
        show ((distribHaarChar (AdeleRing (𝓞 F) F) (Matrix.GeneralLinearGroup.det k) : ℝ≥0) : ℝ) = 1
        rw [distribHaarChar_det_eq_one k hk]
        rfl
      rw [this, Complex.ofReal_one, Complex.one_cpow]

    have hfac := isFactorizableStandardOutside_slice S Φ Φa Φf hΦ0 hΦ1 k hk
    have hZ := H _ _ _ hfac (μ * ν⁻¹) hχc hχu hS (2 * s + 1) hz
    show ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
        * ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
        * zetaIntegral ν₀ (fun t => Φ (bottomRowVec F k t)) (μ * ν⁻¹) (2 * s + 1)
        * _ = _
    rw [hcp, mul_one, mul_assoc, hZ]
    ring

end R4G1E

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace w.Completion] [∀ w : InfinitePlace F, BorelSpace w.Completion]
    (μa : (w : InfinitePlace F) → Measure w.Completion) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)),
    ∃ c : ℝ, 0 < c ∧
      ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
        (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
        (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
        (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
        (_hS : ∀ v ∉ S, IsUnramifiedCharAt (μ * ν⁻¹) v)
        (s : ℂ) (_hs : 0 < s.re),
        Multipliable (fun v : {v // v ∉ S} =>
            1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ∧
        (∏' v : {v // v ∉ S},
            (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) ≠ 0 ∧
        ∀ (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ)
          (Φa : (w : InfinitePlace F) → (Fin 2 → w.Completion) → ℂ)
          (Φf : (v : HeightOneSpectrum (𝓞 F)) → (Fin 2 → v.adicCompletion F) → ℂ)
          (_hΦ0 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∃ v ∉ S, ∃ i, (x i).2 v ∉ v.adicCompletionIntegers F) → Φ x = 0)
          (_hΦ1 : ∀ x : Fin 2 → AdeleRing (𝓞 F) F,
            (∀ v ∉ S, ∀ i, (x i).2 v ∈ v.adicCompletionIntegers F) →
              Φ x = (∏ w, Φa w (fun i => (x i).1 w)) * ∏ v ∈ S, Φf v (fun i => (x i).2 v))
          (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ adelicMaximalCompact F),
          godementSection F ν₀ μ ν α hα Φ s k
              * ∏' v : {v // v ∉ S},
                  (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
            = c * ((μ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
                * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w)
                    (fun t => Φa w (fun i => t
                      * (archComponent F w (glArch (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                    (archLocalChar (μ * ν⁻¹) w) (2 * s + 1))
                * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v)
                    (fun t => Φf v (fun i => t
                      * (finComponent (𝓞 F) F v (glFin (𝓞 F) F k) :
                          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 i))
                    (localChar (μ * ν⁻¹) v) (2 * s + 1) :=
  R4G1E.main F ν₀ S μf μa ϖ _hϖ

end

end S_AutomorphicForm_exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_godementSection_mul_tprod_eq_mul_prod_localZeta_of_mem_adelicMaximalCompact (solution)
