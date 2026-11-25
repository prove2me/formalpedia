-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
-- name    : GroundTheory_PAdicHodge_UntiltPerfectoid
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:08.540308+00:00
-- url     : https://prove2.me/theorems/a9f8c349-471d-4558-899d-a9e114943877
-- title:
--   Untilt Perfectoid
-- statement:
--   Definitions and structural lemmas for Untilt Perfectoid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltPerfectoid.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltDegree
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_exists_mk_untilt_eq
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_norm_sub_pow_le
import Theorems.Thm_GroundTheory_PAdicHodge_coe_mem_untiltField
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_mem_Ioc
import Theorems.Thm_GroundTheory_PAdicHodge_mul_norm_le_norm_sum_smul_tiltSharp
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_algebra
import Theorems.Thm_GroundTheory_PAdicHodge_norm_untilt_sum_sub_le
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
import Theorems.Thm_GroundTheory_PAdicHodge_untilt_mem_untiltInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p
theorem exists_norm_sub_pow_le_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    ∃ πK : K, ‖πK‖ < 1 ∧ ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
      ∃ q ∈ untiltField K C p N, ‖q‖ ≤ 1 ∧ ‖y - q ^ p‖ ≤ ‖πK‖ ^ p := by
  classical
  obtain ⟨w, t, r, ρ, ht0, ht1, hr0, hr1, hρ0, hρ1, hp, hwN, hnorm, -, horth, -, -, hsub⟩ :=
    exists_untiltField_basis (K := K) (C := C) (p := p) N
  set ρ' := (1 + ρ) / 2 with hρ'
  have hρρ' : ρ < ρ' := by rw [hρ']; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  have hρ'0 : 0 < ρ' := hρ0.trans hρρ'
  have htr : 0 < t * r := mul_pos ht0 hr0
  have hp' : ‖(p : K)‖ ≤ t * r * ρ' := hp.trans (by gcongr)
  have hpstrict : ‖(p : K)‖ < t * r * ρ' :=
    hp.trans_lt (mul_lt_mul_of_pos_left hρρ' htr)
  have hest := fun l i => mul_norm_le_norm_sum_smul_tiltSharp (K := K) (C := C) (p := p) horth
    (fun i => (hnorm i).1) (fun i => (hnorm i).2) ht0 hr0.le hρ'0 hρ'1 hp' l i
  set b := t * r * ρ' with hbdef
  have hb0 : 0 < b := mul_pos htr hρ'0
  have hb1 : b ≤ 1 := by
    have : t * r ≤ 1 := by nlinarith
    calc b = t * r * ρ' := rfl
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1

  obtain ⟨ε, hε1, hε2⟩ := exists_norm_mem_Ioc (K := K♭) p
    (lt_max_of_lt_right (half_pos hb0)) (max_lt hpstrict (half_lt_self hb0))
  obtain ⟨γ, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 (hε2.trans hb1)
  rw [norm_algebraMap_preTilt] at hε1 hε2
  have hpγ : ‖(p : K)‖ < ‖γ‖ := (le_max_left _ _).trans_lt hε1
  set γ' := (frobeniusEquiv 𝒪K♭ p).symm γ
  set e : K := ((PreTilt.untilt γ : normInteger K) : K) with he
  set e' : K := ((PreTilt.untilt γ' : normInteger K) : K) with he'
  have hee' : e' ^ p = e := by
    rw [he', he, ← SubmonoidClass.coe_pow, ← map_pow, frobeniusEquiv_symm_pow_p]
  have hen : ‖e‖ = ‖γ‖ := (preTilt_norm_def γ).symm
  have he0 : 0 < ‖e‖ := hen ▸ (norm_nonneg _).trans_lt hpγ
  have he'0 : e' ≠ 0 := by
    intro h; rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at hee'
    rw [← hee', norm_zero] at he0; exact lt_irrefl _ he0
  set base := ‖(p : K)‖ / ‖e‖ with hbase
  have hbase0 : 0 ≤ base := div_nonneg (norm_nonneg _) he0.le
  have hbase1 : base < 1 := by rw [hbase, div_lt_one he0, hen]; exact hpγ
  have hpn : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set r0 := base ^ ((p : ℝ)⁻¹) with hr0def
  have hr01 : r0 < 1 := Real.rpow_lt_one hbase0 hbase1 (inv_pos.2 (by positivity))
  obtain ⟨πK, hπ1, hπ2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r0 hr01
  refine ⟨πK, hπ2, fun y hyF hy1 => ?_⟩
  have hbaseπ : base ≤ ‖πK‖ ^ p := by
    have h1 : r0 ^ p = base := Real.rpow_inv_natCast_pow hbase0 (Fact.out : p.Prime).ne_zero
    rw [← h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hbase0 _) hπ1.le p

  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsub y hyF)
  have hlb : ∀ i, ‖e * l i‖ ≤ 1 := by
    intro i
    have h1 := hest l i
    rw [hl] at h1
    rw [norm_mul, hen]
    calc ‖γ‖ * ‖l i‖ ≤ b * ‖l i‖ := by gcongr
      _ ≤ ‖y‖ := h1
      _ ≤ 1 := hy1
  choose a ha using fun i => exists_mk_untilt_eq (p := p)
    (⟨e * l i, mem_normInteger.2 (hlb i)⟩ : normInteger K)
  have ha' : ∀ i, ‖((PreTilt.untilt (a i) : normInteger K) : K) - e * l i‖ ≤ ‖(p : K)‖ :=
    fun i => mk_eq_mk_iff_norm_sub_le.1 (ha i)
  choose ω hω using fun i => (norm_le_one_iff_exists_algebraMap (K := C) (p := p)).1 (hnorm i).1
  set φ := preTiltMap p (algebraMap K C) (norm_algebraMap' C)
  have hφmem : ∀ c : 𝒪K♭, φ c ∈ integerTilt K C p N := fun c => by
    rw [mem_integerTilt]
    have : algebraMap K♭ C♭ (algebraMap 𝒪K♭ K♭ c) = algebraMap 𝒪C♭ C♭ (φ c) :=
      tiltMap_algebraMap _ _ c
    rw [← this]; exact N.algebraMap_mem _
  have hωmem : ∀ i, ω i ∈ integerTilt K C p N := fun i => by
    rw [mem_integerTilt, hω]; exact hwN i
  set X : 𝒪C♭ := ∑ i, φ (a i) * ω i
  have hXmem : X ∈ integerTilt K C p N :=
    Subring.sum_mem _ fun i _ => mul_mem (hφmem _) (hωmem i)
  set X' := (frobeniusEquiv 𝒪C♭ p).symm X
  have hX'mem : X' ∈ integerTilt K C p N := frobeniusEquiv_symm_mem_integerTilt hXmem
  have hX'p : ((PreTilt.untilt X' : normInteger C) : C) ^ p = ((PreTilt.untilt X : normInteger C) : C) := by
    rw [← SubmonoidClass.coe_pow, ← map_pow, frobeniusEquiv_symm_pow_p]
  set q : C := ((PreTilt.untilt X' : normInteger C) : C) / algebraMap K C e'
  have hqF : q ∈ untiltField K C p N :=
    div_mem (coe_mem_untiltField (untilt_mem_untiltInteger hX'mem))
      (IntermediateField.algebraMap_mem _ _)
  have hqp : q ^ p = ((PreTilt.untilt X : normInteger C) : C) / algebraMap K C e := by
    rw [div_pow, hX'p, ← map_pow, hee']

  have hterm : ∀ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C) =
      ((PreTilt.untilt (a i) : normInteger K) : K) • tiltSharp C p (w i) := by
    intro i
    rw [map_mul, Subring.coe_mul, coe_untilt_preTiltMap, Algebra.smul_def, ← hω,
      tiltSharp_algebraMap]
  have h1 : ‖algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)‖ ≤
      ‖(p : K)‖ := by
    have : algebraMap K C e * y -
        ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C) =
        ∑ i, (e * l i - ((PreTilt.untilt (a i) : normInteger K) : K)) • tiltSharp C p (w i) := by
      rw [← hl, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm]
      simp only [Algebra.smul_def, map_mul, map_sub]
      ring
    rw [this]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_smul, norm_tiltSharp, norm_sub_rev]
    calc ‖((PreTilt.untilt (a i) : normInteger K) : K) - e * l i‖ * ‖w i‖
        ≤ ‖(p : K)‖ * 1 := mul_le_mul (ha' i) (hnorm i).1 (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_one _
  have h2 : ‖((PreTilt.untilt X : normInteger C) : C) -
      ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by
    rw [← norm_natCast_algebra (K := K) (C := C)]
    exact norm_untilt_sum_sub_le Finset.univ fun i => φ (a i) * ω i
  have h3 : ‖algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by
    have : algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C) =
        (algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)) -
        (((PreTilt.untilt X : normInteger C) : C) -
          ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)) := by ring
    rw [this]
    have := IsUltrametricDist.norm_add_le_max
      (algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C))
      (-(((PreTilt.untilt X : normInteger C) : C) -
          ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)))
    rw [norm_neg, ← sub_eq_add_neg] at this
    exact this.trans (max_le h1 h2)
  have hae : algebraMap K C e ≠ 0 :=
    (map_ne_zero _).2 (fun h => by rw [h, norm_zero] at he0; exact lt_irrefl _ he0)
  have hyq : ‖y - q ^ p‖ ≤ base := by
    have : y - q ^ p = (algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C)) /
        algebraMap K C e := by
      rw [hqp]; field_simp
    rw [this, norm_div, norm_algebraMap', hbase]
    exact div_le_div_of_nonneg_right h3 he0.le
  refine ⟨q, hqF, ?_, hyq.trans hbaseπ⟩
  have hqp1 : ‖q‖ ^ p ≤ 1 := by
    rw [← norm_pow]
    have : q ^ p = y - (y - q ^ p) := by ring
    rw [this]
    have := IsUltrametricDist.norm_add_le_max y (-(y - q ^ p))
    rw [norm_neg, ← sub_eq_add_neg] at this
    exact this.trans (max_le hy1 (hyq.trans hbase1.le))
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Fact.out : p.Prime).ne_zero).1 hqp1
instance isPerfectoidField_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    IsPerfectoidField (untiltField K C p N) p := by
  have := IsPerfectoidField.completeSpace (K := K) p
  have : CompleteSpace (untiltField K C p N) := FiniteDimensional.complete K _
  obtain ⟨πK, hπ, h⟩ := exists_norm_sub_pow_le_untiltField (K := K) (C := C) (p := p) N
  refine IsPerfectoidField.of_norm_sub_pow_le p ?_ ?_ (π := algebraMap K _ πK) ?_ ?_
  · change ‖((p : untiltField K C p N) : C)‖ < 1
    rw [show ((p : untiltField K C p N) : C) = (p : C) from map_natCast (untiltField K C p N).val p,
      norm_natCast_algebra (K := K)]
    exact IsPerfectoidField.norm_natCast_lt_one
  · intro r hr
    obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r hr
    refine ⟨algebraMap K _ x, ?_, ?_⟩ <;> rw [norm_algebraMap'] <;> assumption
  · rw [norm_algebraMap']; exact hπ
  · intro x hx
    obtain ⟨q, hqF, hq1, hq⟩ := h x x.2 hx
    refine ⟨⟨q, hqF⟩, hq1, ?_⟩
    rw [norm_algebraMap']
    exact hq
end GroundTheory.PAdicHodge


