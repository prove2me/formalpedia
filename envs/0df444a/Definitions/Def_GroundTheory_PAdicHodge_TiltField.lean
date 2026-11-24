-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_TiltField
-- name    : GroundTheory_PAdicHodge_TiltField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:09.557012+00:00
-- url     : https://prove2.me/theorems/ffc96020-1f58-4de3-b2e2-498097cce385
-- title:
--   Tilt Field
-- statement:
--   Definitions and structural lemmas for Tilt Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltField.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_isDomain_preTilt
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_perfectRing
import Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_untilt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "♮" x:max => ((PreTilt.untilt x : normInteger K) : K)
instance isDomain_preTilt_of_isPerfectoidField : IsDomain 𝒪♭ :=
  IsPerfectoidField.isDomain_preTilt p
instance algebraPreTiltTilt : Algebra 𝒪♭ K♭ :=
  inferInstanceAs (Algebra 𝒪♭ (FractionRing 𝒪♭))
instance isFractionRing_preTilt_tilt : IsFractionRing 𝒪♭ K♭ :=
  inferInstanceAs (IsFractionRing 𝒪♭ (FractionRing 𝒪♭))
section Sharp
theorem untiltK_mul (a b : 𝒪♭) : ♮(a * b) = ♮a * ♮b := by
  rw [map_mul, Subring.coe_mul]
theorem untiltK_one : ♮(1 : 𝒪♭) = 1 := by
  rw [map_one, OneMemClass.coe_one]
theorem untiltK_ne_zero {a : 𝒪♭} (ha : a ≠ 0) : ♮a ≠ 0 :=
  fun h => ha (untilt_eq_zero_iff.1 h)
theorem exists_mul_algebraMap_eq (x : K♭) :
    ∃ a b : 𝒪♭, b ≠ 0 ∧ x * algebraMap 𝒪♭ K♭ b = algebraMap 𝒪♭ K♭ a :=
  ⟨_, _, nonZeroDivisors.ne_zero (IsLocalization.sec (nonZeroDivisors 𝒪♭) x).2.2,
    IsLocalization.sec_spec (nonZeroDivisors 𝒪♭) x⟩
variable (K p) in

def tiltSharpFun (x : K♭) : K :=
  ♮(IsLocalization.sec (nonZeroDivisors 𝒪♭) x).1 /
    ♮((IsLocalization.sec (nonZeroDivisors 𝒪♭) x).2 : 𝒪♭)
theorem tiltSharpFun_eq {x : K♭} {a b : 𝒪♭} (hb : b ≠ 0)
    (h : x * algebraMap 𝒪♭ K♭ b = algebraMap 𝒪♭ K♭ a) : tiltSharpFun K p x = ♮a / ♮b := by
  have hs := IsLocalization.sec_spec (nonZeroDivisors 𝒪♭) x
  set a' := (IsLocalization.sec (nonZeroDivisors 𝒪♭) x).1
  set b' : 𝒪♭ := ((IsLocalization.sec (nonZeroDivisors 𝒪♭) x).2 : 𝒪♭) with hb'def
  have hb' : b' ≠ 0 := nonZeroDivisors.ne_zero (IsLocalization.sec (nonZeroDivisors 𝒪♭) x).2.2
  have key : a' * b = a * b' := by
    apply IsFractionRing.injective 𝒪♭ K♭
    rw [map_mul, map_mul, ← hs, ← h]
    ring
  have key' : ♮a' * ♮b = ♮a * ♮b' := by
    rw [← untiltK_mul, ← untiltK_mul, key]
  change ♮a' / ♮b' = _
  rw [div_eq_div_iff (untiltK_ne_zero hb') (untiltK_ne_zero hb), key']
variable (K p) in

def tiltSharp : K♭ →*₀ K where
  toFun := tiltSharpFun K p
  map_zero' := by
    rw [tiltSharpFun_eq (a := 0) (b := 1) one_ne_zero (by simp)]
    simp
  map_one' := by
    rw [tiltSharpFun_eq (a := 1) (b := 1) one_ne_zero (by simp), div_self]
    exact untiltK_ne_zero one_ne_zero
  map_mul' x y := by
    obtain ⟨a, b, hb, h⟩ := exists_mul_algebraMap_eq x
    obtain ⟨c, d, hd, h'⟩ := exists_mul_algebraMap_eq y
    rw [tiltSharpFun_eq hb h, tiltSharpFun_eq hd h',
      tiltSharpFun_eq (a := a * c) (b := b * d) (mul_ne_zero hb hd)
        (by rw [map_mul, map_mul, ← h, ← h']; ring),
      untiltK_mul, untiltK_mul, div_mul_div_comm]
theorem tiltSharp_eq {x : K♭} {a b : 𝒪♭} (hb : b ≠ 0)
    (h : x * algebraMap 𝒪♭ K♭ b = algebraMap 𝒪♭ K♭ a) : tiltSharp K p x = ♮a / ♮b :=
  tiltSharpFun_eq hb h
@[simp]
theorem tiltSharp_algebraMap (a : 𝒪♭) : tiltSharp K p (algebraMap 𝒪♭ K♭ a) = ♮a := by
  rw [tiltSharp_eq (a := a) (b := 1) one_ne_zero (by simp), untiltK_one, div_one]
theorem tiltSharp_eq_zero_iff {x : K♭} : tiltSharp K p x = 0 ↔ x = 0 := by
  obtain ⟨a, b, hb, h⟩ := exists_mul_algebraMap_eq x
  rw [tiltSharp_eq hb h, div_eq_zero_iff, or_iff_left (untiltK_ne_zero hb)]
  constructor
  · intro ha
    have ha' : a = 0 := untilt_eq_zero_iff.1 ha
    have hb' : algebraMap 𝒪♭ K♭ b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective 𝒪♭ K♭)).2 hb
    rw [ha', map_zero] at h
    exact (mul_eq_zero.1 h).resolve_right hb'
  · rintro rfl
    rw [zero_mul, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective 𝒪♭ K♭)] at h
    rw [h, untilt_zero, ZeroMemClass.coe_zero]
theorem norm_tiltSharp_add_le (x y : K♭) :
    ‖tiltSharp K p (x + y)‖ ≤ max ‖tiltSharp K p x‖ ‖tiltSharp K p y‖ := by
  obtain ⟨a, b, hb, h⟩ := exists_mul_algebraMap_eq x
  obtain ⟨c, d, hd, h'⟩ := exists_mul_algebraMap_eq y
  have hbd : b * d ≠ 0 := mul_ne_zero hb hd
  rw [tiltSharp_eq (x := x) (a := a * d) (b := b * d) hbd
      (by rw [map_mul, map_mul, ← h]; ring),
    tiltSharp_eq (x := y) (a := c * b) (b := b * d) hbd
      (by rw [map_mul, map_mul, ← h']; ring),
    tiltSharp_eq (x := x + y) (a := a * d + c * b) (b := b * d) hbd
      (by rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']; ring),
    norm_div, norm_div, norm_div, max_div_div_right (norm_nonneg _)]
  exact div_le_div_of_nonneg_right (norm_untilt_add_le _ _) (norm_nonneg _)
end Sharp
section Norm
variable (K p) in

def tiltAbv : AbsoluteValue K♭ ℝ where
  toFun x := ‖tiltSharp K p x‖
  map_mul' x y := by simp only [map_mul, norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by rw [norm_eq_zero, tiltSharp_eq_zero_iff]
  add_le' x y := (norm_tiltSharp_add_le x y).trans
    (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _))
instance normedFieldTilt : NormedField K♭ := (tiltAbv K p).toNormedField
theorem norm_tiltSharp (x : K♭) : ‖tiltSharp K p x‖ = ‖x‖ := rfl
@[simp]
theorem norm_algebraMap_preTilt (a : 𝒪♭) : ‖algebraMap 𝒪♭ K♭ a‖ = ‖a‖ := by
  rw [← norm_tiltSharp, tiltSharp_algebraMap, preTilt_norm_def]
theorem dist_algebraMap_preTilt (a b : 𝒪♭) :
    dist (algebraMap 𝒪♭ K♭ a) (algebraMap 𝒪♭ K♭ b) = dist a b := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_algebraMap_preTilt]
instance isUltrametricDist_tilt : IsUltrametricDist K♭ :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm norm_tiltSharp_add_le
theorem norm_le_one_iff_exists_algebraMap {x : K♭} :
    ‖x‖ ≤ 1 ↔ ∃ a : 𝒪♭, algebraMap 𝒪♭ K♭ a = x := by
  constructor
  · intro hx
    obtain ⟨a, b, hb, h⟩ := exists_mul_algebraMap_eq x
    have hle : ‖a‖ ≤ ‖b‖ := by
      rw [← norm_algebraMap_preTilt (K := K) a, ← h, norm_mul, norm_algebraMap_preTilt]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
    obtain ⟨c, rfl⟩ := preTilt_dvd_iff_norm_le.2 hle
    have hb' : algebraMap 𝒪♭ K♭ b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective 𝒪♭ K♭)).2 hb
    refine ⟨c, ?_⟩
    rw [map_mul, mul_comm x] at h
    exact (mul_left_cancel₀ hb' h).symm
  · rintro ⟨a, rfl⟩
    rw [norm_algebraMap_preTilt]
    exact preTilt_norm_le_one a
theorem normInteger_tilt_eq_range : normInteger K♭ = (algebraMap 𝒪♭ K♭).range := by
  ext x
  rw [mem_normInteger, norm_le_one_iff_exists_algebraMap, RingHom.mem_range]
variable (K p) in

def preTiltEquivNormInteger : 𝒪♭ ≃+* normInteger K♭ :=
  (RingEquiv.ofBijective (algebraMap 𝒪♭ K♭).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective 𝒪♭ K♭ (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).trans
    (RingEquiv.subringCongr normInteger_tilt_eq_range.symm)
@[simp]
theorem coe_preTiltEquivNormInteger (a : 𝒪♭) :
    ((preTiltEquivNormInteger K p a : normInteger K♭) : K♭) = algebraMap 𝒪♭ K♭ a := rfl
theorem exists_tilt_norm_mem_Ioo (r : ℝ) (hr : r < 1) : ∃ x : K♭, r < ‖x‖ ∧ ‖x‖ < 1 := by
  obtain ⟨ϖ, h1, h2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) (max r ‖(p : K)‖)
    (max_lt hr IsPerfectoidField.norm_natCast_lt_one)
  obtain ⟨a, ha⟩ := exists_norm_untilt_eq (p := p) ⟨ϖ, mem_normInteger.2 h2.le⟩
    ((le_max_right _ _).trans_lt h1)
  refine ⟨algebraMap 𝒪♭ K♭ a, ?_, ?_⟩ <;> rw [norm_algebraMap_preTilt, preTilt_norm_def, ha]
  · exact (le_max_left _ _).trans_lt h1
  · exact h2
instance nontriviallyNormedFieldTilt : NontriviallyNormedField K♭ where
  __ := normedFieldTilt
  non_trivial := by
    obtain ⟨x, hx0, hx1⟩ := exists_tilt_norm_mem_Ioo (K := K) (p := p) 0 zero_lt_one
    refine ⟨x⁻¹, ?_⟩
    rw [norm_inv]
    exact one_lt_inv₀ hx0 |>.2 hx1
instance completeSpace_tilt : CompleteSpace K♭ := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hu 1 one_pos
  have hmem : ∀ m : ℕ, ∃ a : 𝒪♭, algebraMap 𝒪♭ K♭ a = u (m + N) - u N := fun m =>
    norm_le_one_iff_exists_algebraMap.1 (by
      rw [← dist_eq_norm]; exact (hN _ (Nat.le_add_left _ _)).le)
  choose w hw using hmem
  have hw' : CauchySeq w := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hu ε hε
    refine ⟨M, fun m hm n hn => ?_⟩
    rw [← dist_algebraMap_preTilt (K := K), hw, hw, dist_sub_right]
    exact hM _ (by omega) _ (by omega)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hw'
  refine ⟨u N + algebraMap 𝒪♭ K♭ L, ?_⟩
  have hι : Tendsto (fun m => algebraMap 𝒪♭ K♭ (w m)) atTop (𝓝 (algebraMap 𝒪♭ K♭ L)) := by
    rw [tendsto_iff_dist_tendsto_zero] at hL ⊢
    simpa only [dist_algebraMap_preTilt] using hL
  have h1 : Tendsto (fun m => u (m + N)) atTop (𝓝 (u N + algebraMap 𝒪♭ K♭ L)) := by
    refine ((tendsto_const_nhds (x := u N)).add hι).congr fun m => ?_
    rw [hw]
    abel
  exact (tendsto_add_atTop_iff_nat N).1 h1
instance charP_tilt : CharP K♭ p :=
  charP_of_injective_algebraMap (IsFractionRing.injective 𝒪♭ K♭) p
instance perfectRing_tilt : PerfectRing K♭ p := by
  refine PerfectRing.ofSurjective K♭ p fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝒪♭) x
  have ha : ((frobeniusEquiv 𝒪♭ p).symm a) ^ p = a := by
    rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]
  have hb : ((frobeniusEquiv 𝒪♭ p).symm b) ^ p = b := by
    rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]
  refine ⟨algebraMap 𝒪♭ K♭ ((frobeniusEquiv 𝒪♭ p).symm a) /
    algebraMap 𝒪♭ K♭ ((frobeniusEquiv 𝒪♭ p).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap 𝒪♭ K♭), ← map_pow (algebraMap 𝒪♭ K♭), ha, hb]
instance isPerfectoidField_tilt : IsPerfectoidField K♭ p :=
  IsPerfectoidField.of_perfectRing p exists_tilt_norm_mem_Ioo
end Norm
section ValueGroup
end ValueGroup
end GroundTheory.PAdicHodge
end


