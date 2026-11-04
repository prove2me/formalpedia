-- Prove2me | solution 1 for AIMInventory.UnknownRho.lemma_9_corrected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:00:22.233695+00:00
-- url     : https://prove2.me/submissions/d54c62d6-913b-4a6a-a693-58413890de75

import Mathlib
import Definitions.Def_AIMInventory_UnknownRho_Model
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal
open scoped ENNReal NNReal BigOperators

namespace AIMInventory.UnknownRho

lemma shift_map (P : DemandLaw) (k : ℕ) :
    Measure.map (fun (d : DemandPath) (n : ℕ) => d (n + k)) (CappedBaseStock.demandPathLaw P)
      = CappedBaseStock.demandPathLaw P := by
  unfold CappedBaseStock.demandPathLaw
  refine Measure.eq_infinitePi (fun _ : ℕ => P.law) ?_
  intro s t ht
  have hm : Measurable (fun (d : DemandPath) (n : ℕ) => d (n + k)) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply _)
  have hpre : (fun (d : DemandPath) (n : ℕ) => d (n + k)) ⁻¹' (Set.pi (↑s) t)
      = Set.pi (↑(s.image (fun i => i + k))) (fun j => t (j - k)) := by
    ext d
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro h j ⟨i, hi, rfl⟩
      have := h i hi
      rwa [Nat.add_sub_cancel]
    · intro h i hi
      have := h (i + k) ⟨i, hi, rfl⟩
      rwa [Nat.add_sub_cancel] at this
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)), hpre,
    Measure.infinitePi_pi _ (fun j _ => ht _)]
  rw [Finset.prod_image (by intro a _ b _ h; simpa using h)]
  exact Finset.prod_congr rfl (fun i _ => by rw [Nat.add_sub_cancel])

lemma K_eq (d : DemandPath) (θ z : ℝ) :
    K d θ z = ⨅ n : ℕ, if z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) ≤ 0 then (n : ℝ≥0∞) else ⊤ := by
  apply le_antisymm
  · refine le_iInf (fun n => ?_)
    split_ifs with h
    · exact sInf_le ⟨n, rfl, h⟩
    · exact le_top
  · refine le_sInf ?_
    rintro u ⟨n, rfl, h⟩
    exact iInf_le_of_le n (by rw [if_pos h])

lemma measurable_K (θ z : ℝ) : Measurable (fun d : DemandPath => K d θ z) := by
  simp_rw [K_eq]
  refine Measurable.iInf (fun n => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  refine measurableSet_le ?_ measurable_const
  fun_prop

lemma measurable_W (θ : ℝ) (t : ℕ) : Measurable (fun d : DemandPath => W d θ t) := by
  induction t with
  | zero => simp [W]
  | succ t ih =>
    by_cases ht : t = 0
    · simp [W, ht]
    · simp only [W, ht, if_false]
      fun_prop

lemma firstBusyLength_eq (d : DemandPath) (θ : ℝ) :
    firstBusyLength d θ = ⨅ n : ℕ, if 1 ≤ n ∧ W d θ (n + 1) = 0 then (n : ℝ≥0∞) else ⊤ := by
  apply le_antisymm
  · refine le_iInf (fun n => ?_)
    split_ifs with h
    · exact sInf_le ⟨n, h.1, rfl, h.2⟩
    · exact le_top
  · refine le_sInf ?_
    rintro u ⟨n, h1, rfl, h⟩
    exact iInf_le_of_le n (by simp [h1, h])

lemma measurable_firstBusyLength (θ : ℝ) : Measurable (fun d : DemandPath => firstBusyLength d θ) := by
  simp_rw [firstBusyLength_eq]
  refine Measurable.iInf (fun n => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have h : MeasurableSet {d : DemandPath | W d θ (n + 1) = 0} :=
    measurableSet_eq_fun (measurable_W θ (n+1)) measurable_const
  by_cases h1 : 1 ≤ n
  · simpa [h1] using h
  · simp [h1]

/-- A lintegral of a shifted measurable function. -/
lemma lintegral_shift (P : DemandLaw) (k : ℕ) {f : DemandPath → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ d, f (fun n => d (n + k)) ∂CappedBaseStock.demandPathLaw P
      = ∫⁻ d, f d ∂CappedBaseStock.demandPathLaw P := by
  have hm : Measurable (fun (d : DemandPath) (n : ℕ) => d (n + k)) :=
    measurable_pi_lambda _ (fun n => measurable_pi_apply _)
  conv_rhs => rw [← shift_map P k]
  rw [lintegral_map hf hm]

lemma integrable_pow_of_memLp4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 4 μ) {k : ℕ} (hk : k ≤ 4) :
    Integrable (fun ω => f ω ^ k) μ := by
  have h4 : Integrable (fun ω => ‖f ω‖ ^ 4) μ := by
    have := MemLp.integrable_norm_pow' (p := 4) (by exact_mod_cast hf)
    exact this
  have hk' := integrable_norm_pow_of_le hf.aestronglyMeasurable hk h4
  have : Integrable (fun ω => ‖f ω ^ k‖) μ := by simpa [norm_pow] using hk'
  exact (integrable_norm_iff (hf.aestronglyMeasurable.pow k)).mp this

lemma moment_step {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {S X : Ω → ℝ} (hS : MemLp S 4 μ) (hX : MemLp X 4 μ)
    (hind : ProbabilityTheory.IndepFun S X μ) (hS0 : ∫ ω, S ω ∂μ = 0) (hX0 : ∫ ω, X ω ∂μ = 0) :
    ∫ ω, (S ω + X ω) ^ 2 ∂μ = ∫ ω, S ω ^ 2 ∂μ + ∫ ω, X ω ^ 2 ∂μ ∧
    ∫ ω, (S ω + X ω) ^ 4 ∂μ = ∫ ω, S ω ^ 4 ∂μ + 6 * ((∫ ω, S ω ^ 2 ∂μ) * ∫ ω, X ω ^ 2 ∂μ)
      + ∫ ω, X ω ^ 4 ∂μ := by
  have iS : ∀ k, k ≤ 4 → Integrable (fun ω => S ω ^ k) μ := fun k hk => integrable_pow_of_memLp4 hS hk
  have iX : ∀ k, k ≤ 4 → Integrable (fun ω => X ω ^ k) μ := fun k hk => integrable_pow_of_memLp4 hX hk
  have hi : ∀ a b : ℕ, ProbabilityTheory.IndepFun (fun ω => S ω ^ a) (fun ω => X ω ^ b) μ := by
    intro a b
    exact hind.comp (φ := fun x : ℝ => x ^ a) (ψ := fun x : ℝ => x ^ b) (by fun_prop) (by fun_prop)
  have hSX : ∀ a b : ℕ, a ≤ 4 → b ≤ 4 → Integrable (fun ω => S ω ^ a * X ω ^ b) μ := by
    intro a b ha hb
    exact (hi a b).integrable_mul (iS a ha) (iX b hb)
  have hmul : ∀ a b : ℕ, ∫ ω, S ω ^ a * X ω ^ b ∂μ = (∫ ω, S ω ^ a ∂μ) * ∫ ω, X ω ^ b ∂μ := by
    intro a b
    exact (hi a b).integral_fun_mul_eq_mul_integral (hS.aestronglyMeasurable.pow a)
      (hX.aestronglyMeasurable.pow b)
  have hS1 : ∫ ω, S ω ^ 1 ∂μ = 0 := by simpa using hS0
  have hX1 : ∫ ω, X ω ^ 1 ∂μ = 0 := by simpa using hX0
  constructor
  · have e : (fun ω => (S ω + X ω) ^ 2) =
        fun ω => S ω ^ 2 + 2 * (S ω ^ 1 * X ω ^ 1) + X ω ^ 2 := by funext ω; ring
    have j1 : Integrable (fun ω => S ω ^ 2) μ := iS 2 (by norm_num)
    have j2 : Integrable (fun ω => 2 * (S ω ^ 1 * X ω ^ 1)) μ :=
      (hSX 1 1 (by norm_num) (by norm_num)).const_mul 2
    have j3 : Integrable (fun ω => X ω ^ 2) μ := iX 2 (by norm_num)
    have j12 : Integrable (fun ω => S ω ^ 2 + 2 * (S ω ^ 1 * X ω ^ 1)) μ := j1.add j2
    rw [e, integral_add j12 j3, integral_add j1 j2, integral_const_mul, hmul, hS1]
    ring
  · have e : (fun ω => (S ω + X ω) ^ 4) =
        fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * X ω ^ 1) + 6 * (S ω ^ 2 * X ω ^ 2) +
          4 * (S ω ^ 1 * X ω ^ 3) + X ω ^ 4 := by funext ω; ring
    have i1 : Integrable (fun ω => S ω ^ 4) μ := iS 4 (by norm_num)
    have i2 : Integrable (fun ω => 4 * (S ω ^ 3 * X ω ^ 1)) μ :=
      (hSX 3 1 (by norm_num) (by norm_num)).const_mul 4
    have i3 : Integrable (fun ω => 6 * (S ω ^ 2 * X ω ^ 2)) μ :=
      (hSX 2 2 (by norm_num) (by norm_num)).const_mul 6
    have i4 : Integrable (fun ω => 4 * (S ω ^ 1 * X ω ^ 3)) μ :=
      (hSX 1 3 (by norm_num) (by norm_num)).const_mul 4
    have i5 : Integrable (fun ω => X ω ^ 4) μ := iX 4 (by norm_num)
    have i12 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * X ω ^ 1)) μ := i1.add i2
    have i123 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * X ω ^ 1) + 6 * (S ω ^ 2 * X ω ^ 2)) μ :=
      i12.add i3
    have i1234 : Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * X ω ^ 1) + 6 * (S ω ^ 2 * X ω ^ 2)
        + 4 * (S ω ^ 1 * X ω ^ 3)) μ := i123.add i4
    rw [e, integral_add i1234 i5, integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
      integral_const_mul, integral_const_mul, integral_const_mul, hmul, hmul, hmul, hX1, hS1]
    ring

section
open ProbabilityTheory

lemma int_coord (P : DemandLaw) (g : ℝ≥0 → ℝ) (hg : Measurable g) (i : ℕ) :
    ∫ d : DemandPath, g (d i) ∂CappedBaseStock.demandPathLaw P = ∫ x, g x ∂P.law := by
  unfold CappedBaseStock.demandPathLaw
  have h1 := Measure.infinitePi_map_eval (fun _ : ℕ => P.law) i
  rw [← integral_map (φ := fun x : DemandPath => x i) (measurable_pi_apply i).aemeasurable
    (by rw [h1]; exact hg.aestronglyMeasurable), h1]

lemma memLp4_base (P : DemandLaw) (hfourth : Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 4) P.law) :
    MemLp (fun d : ℝ≥0 => (d : ℝ) - CappedBaseStock.mean P) 4 P.law := by
  have hD : MemLp (fun d : ℝ≥0 => (d : ℝ)) 4 P.law := by
    have hm : AEStronglyMeasurable (fun d : ℝ≥0 => (d : ℝ)) P.law :=
      (by fun_prop : Measurable fun d : ℝ≥0 => (d : ℝ)).aestronglyMeasurable
    have := (integrable_norm_rpow_iff (μ := P.law) (p := 4) hm (by norm_num) (by norm_num)).mp
    refine this ?_
    have e : (fun d : ℝ≥0 => ‖(d : ℝ)‖ ^ (4 : ℝ≥0∞).toReal) = fun d : ℝ≥0 => (d : ℝ) ^ 4 := by
      funext d
      simp only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg d)]
      norm_num
    rw [e]; exact hfourth
  exact hD.sub (memLp_const _)

/-- Fourth moment of centered partial sums. -/
lemma fourth_moment (P : DemandLaw) (hfourth : Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 4) P.law) (n : ℕ) :
    MemLp (fun d : DemandPath => ∑ i ∈ Finset.range n, ((d i : ℝ) - CappedBaseStock.mean P)) 4
        (CappedBaseStock.demandPathLaw P) ∧
    ∫ d : DemandPath, (∑ i ∈ Finset.range n, ((d i : ℝ) - CappedBaseStock.mean P))
        ∂CappedBaseStock.demandPathLaw P = 0 ∧
    ∫ d : DemandPath, (∑ i ∈ Finset.range n, ((d i : ℝ) - CappedBaseStock.mean P)) ^ 2
        ∂CappedBaseStock.demandPathLaw P = n * ∫ x : ℝ≥0, ((x : ℝ) - CappedBaseStock.mean P) ^ 2 ∂P.law ∧
    ∫ d : DemandPath, (∑ i ∈ Finset.range n, ((d i : ℝ) - CappedBaseStock.mean P)) ^ 4
        ∂CappedBaseStock.demandPathLaw P ≤ 3 * (n : ℝ) ^ 2 * centralFourth P := by
  have hbase := memLp4_base P hfourth
  set μ0 := CappedBaseStock.mean P with hμ0
  set s2 := ∫ x : ℝ≥0, ((x : ℝ) - μ0) ^ 2 ∂P.law with hs2
  have hXi : ∀ i, MemLp (fun d : DemandPath => (d i : ℝ) - μ0) 4 (CappedBaseStock.demandPathLaw P) := by
    intro i
    exact hbase.comp_measurePreserving (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) i)
  have hX0 : ∀ i, ∫ d : DemandPath, ((d i : ℝ) - μ0) ∂CappedBaseStock.demandPathLaw P = 0 := by
    intro i
    rw [int_coord P (fun x => (x : ℝ) - μ0) (by fun_prop) i]
    rw [integral_sub P.finiteMean (integrable_const _)]
    simp [CappedBaseStock.mean, hμ0]
  have hX2 : ∀ i, ∫ d : DemandPath, ((d i : ℝ) - μ0) ^ 2 ∂CappedBaseStock.demandPathLaw P = s2 := by
    intro i
    exact int_coord P (fun x => ((x : ℝ) - μ0) ^ 2) (by fun_prop) i
  have hX4 : ∀ i, ∫ d : DemandPath, ((d i : ℝ) - μ0) ^ 4 ∂CappedBaseStock.demandPathLaw P = centralFourth P := by
    intro i
    exact int_coord P (fun x => ((x : ℝ) - μ0) ^ 4) (by fun_prop) i
  have hind : iIndepFun (fun (i : ℕ) (d : DemandPath) => (d i : ℝ) - μ0) (CappedBaseStock.demandPathLaw P) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => P.law) (X := fun _ x => (x : ℝ) - μ0) (by fun_prop)
  -- s2^2 ≤ fourth
  have hs2sq : s2 ^ 2 ≤ centralFourth P := by
    have i2 : Integrable (fun x : ℝ≥0 => ((x : ℝ) - μ0) ^ 2) P.law := integrable_pow_of_memLp4 hbase (by norm_num)
    have i4 : Integrable (fun x : ℝ≥0 => ((x : ℝ) - μ0) ^ 4) P.law := integrable_pow_of_memLp4 hbase (by norm_num)
    have h0 : 0 ≤ ∫ x : ℝ≥0, (((x : ℝ) - μ0) ^ 2 - s2) ^ 2 ∂P.law :=
      integral_nonneg (fun x => sq_nonneg _)
    have e : (fun x : ℝ≥0 => (((x : ℝ) - μ0) ^ 2 - s2) ^ 2) =
        fun x : ℝ≥0 => ((x : ℝ) - μ0) ^ 4 - 2 * s2 * ((x : ℝ) - μ0) ^ 2 + s2 ^ 2 := by
      funext x; ring
    have k1 : Integrable (fun x : ℝ≥0 => 2 * s2 * ((x : ℝ) - μ0) ^ 2) P.law := i2.const_mul _
    have k2 : Integrable (fun x : ℝ≥0 => ((x : ℝ) - μ0) ^ 4 - 2 * s2 * ((x : ℝ) - μ0) ^ 2) P.law :=
      i4.sub k1
    rw [e, integral_add k2 (integrable_const _), integral_sub i4 k1, integral_const_mul] at h0
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h0
    unfold centralFourth
    rw [← hs2] at h0
    nlinarith
  have hμ4 : 0 ≤ centralFourth P := by
    unfold centralFourth; exact integral_nonneg (fun x => by positivity)
  induction n with
  | zero => exact ⟨by simpa using memLp_const (0 : ℝ), by simp, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨ihL, ih0, ih2, ih4⟩ := ih
    have hsum : (fun d : DemandPath => ∑ i ∈ Finset.range (n + 1), ((d i : ℝ) - μ0)) =
        fun d => (∑ i ∈ Finset.range n, ((d i : ℝ) - μ0)) + ((d n : ℝ) - μ0) := by
      funext d; rw [Finset.sum_range_succ]
    have hindS : IndepFun (fun d : DemandPath => ∑ i ∈ Finset.range n, ((d i : ℝ) - μ0))
        (fun d : DemandPath => (d n : ℝ) - μ0) (CappedBaseStock.demandPathLaw P) := by
      have := hind.indepFun_finsetSum_of_notMem (s := Finset.range n) (i := n)
        (fun i => by fun_prop) (by simp)
      convert this using 1
      funext d; simp [Finset.sum_apply]
    obtain ⟨m2, m4⟩ := moment_step ihL (hXi n) hindS ih0 (hX0 n)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsum]; exact ihL.add (hXi n)
    · rw [hsum]
      rw [integral_add (ihL.integrable (by norm_num)) ((hXi n).integrable (by norm_num)), ih0, hX0 n]
      simp
    · simp_rw [Finset.sum_range_succ]
      beta_reduce at m2
      rw [m2, ih2, hX2 n]
      push_cast; ring
    · simp_rw [Finset.sum_range_succ]
      beta_reduce at m4
      rw [m4, ih2, hX2 n, hX4 n]
      push_cast
      nlinarith [ih4, hs2sq, hμ4, sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

end

lemma K_le_tsum (d : DemandPath) (θ z : ℝ) :
    K d θ z ≤ ∑' n : ℕ,
      (if 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) then (1 : ℝ≥0∞) else 0) := by
  classical
  by_cases hex : ∃ n : ℕ, z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) ≤ 0
  · have hK : K d θ z = (Nat.find hex : ℕ) := by
      apply le_antisymm
      · exact sInf_le ⟨Nat.find hex, rfl, Nat.find_spec hex⟩
      · refine le_sInf ?_
        rintro u ⟨n, rfl, h⟩
        exact_mod_cast Nat.find_min' hex h
    rw [hK]
    calc ((Nat.find hex : ℕ) : ℝ≥0∞) = ∑ i ∈ Finset.range (Nat.find hex), (1 : ℝ≥0∞) := by simp
      _ ≤ ∑ i ∈ Finset.range (Nat.find hex),
          (if 0 < z + ∑ j ∈ Finset.range i, (θ - (d j : ℝ)) then (1 : ℝ≥0∞) else 0) := by
          apply Finset.sum_le_sum
          intro i hi
          have := Nat.find_min hex (Finset.mem_range.mp hi)
          push_neg at this
          rw [if_pos this]
      _ ≤ _ := ENNReal.sum_le_tsum _
  · push_neg at hex
    have : (fun n : ℕ => (if 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) then (1 : ℝ≥0∞) else 0))
        = fun _ => 1 := by
      funext n; rw [if_pos (hex n)]
    rw [this, ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
    exact le_top

lemma measurableSet_A (θ z : ℝ) (n : ℕ) :
    MeasurableSet {d : DemandPath | 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ))} := by
  refine measurableSet_lt measurable_const ?_
  fun_prop

/-- Chebyshev-type tail bound from the fourth moment. -/
lemma tail_bound (P : DemandLaw) (hfourth : Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 4) P.law)
    (θ z : ℝ) (hθ : θ < CappedBaseStock.mean P) (n : ℕ) (hn : 2 * z ≤ n * (CappedBaseStock.mean P - θ))
    (hz : 0 < z) :
    CappedBaseStock.demandPathLaw P {d : DemandPath | 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ))}
      ≤ ENNReal.ofReal (48 * centralFourth P / (CappedBaseStock.mean P - θ) ^ 4 * (1 / (n : ℝ) ^ 2)) := by
  set δ := CappedBaseStock.mean P - θ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    simp at hn; linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set Y : DemandPath → ℝ := fun d => ∑ i ∈ Finset.range n, ((d i : ℝ) - CappedBaseStock.mean P) with hY
  obtain ⟨hL, h0, h2, h4⟩ := fourth_moment P hfourth n
  have hYm : Measurable Y := by rw [hY]; fun_prop
  have hint : Integrable (fun d => Y d ^ 4) (CappedBaseStock.demandPathLaw P) :=
    integrable_pow_of_memLp4 hL (by norm_num)
  set ε : ℝ := (n * δ / 2) ^ 4 with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hsub : {d : DemandPath | 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ))}
      ⊆ {d | ENNReal.ofReal ε ≤ ENNReal.ofReal (Y d ^ 4)} := by
    intro d hd
    simp only [Set.mem_setOf_eq] at hd ⊢
    apply ENNReal.ofReal_le_ofReal
    have hsum : ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) = -(n * δ) - Y d := by
      rw [hY, hδ]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hsum] at hd
    have h5 : n * δ / 2 ≤ -(Y d) := by nlinarith
    have h6 : 0 ≤ n * δ / 2 := by positivity
    calc ε = (n * δ / 2) ^ 4 := rfl
      _ ≤ (-(Y d)) ^ 4 := pow_le_pow_left₀ h6 h5 4
      _ = Y d ^ 4 := by ring
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := CappedBaseStock.demandPathLaw P)
    (f := fun d => ENNReal.ofReal (Y d ^ 4)) (hYm.pow_const 4 |>.ennreal_ofReal.aemeasurable) (ENNReal.ofReal ε)
  have hlint : ∫⁻ d, ENNReal.ofReal (Y d ^ 4) ∂CappedBaseStock.demandPathLaw P
      ≤ ENNReal.ofReal (3 * (n : ℝ) ^ 2 * centralFourth P) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun d => by positivity))]
    exact ENNReal.ofReal_le_ofReal h4
  have hmain : ENNReal.ofReal ε * CappedBaseStock.demandPathLaw P
      {d : DemandPath | 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ))}
      ≤ ENNReal.ofReal (3 * (n : ℝ) ^ 2 * centralFourth P) := by
    refine le_trans (mul_le_mul' le_rfl (measure_mono hsub)) (hmarkov.trans hlint)
  have hεne : ENNReal.ofReal ε ≠ 0 := by simpa using hεpos
  have hdiv : CappedBaseStock.demandPathLaw P
      {d : DemandPath | 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ))}
      ≤ ENNReal.ofReal (3 * (n : ℝ) ^ 2 * centralFourth P) / ENNReal.ofReal ε := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hεne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hmain
  refine hdiv.trans ?_
  rw [← ENNReal.ofReal_div_of_pos hεpos]
  apply le_of_eq
  congr 1
  rw [hε]
  field_simp
  ring

theorem lemma9_core (P : DemandLaw) (θ z : ℝ)
    (hθ : θ < CappedBaseStock.mean P) (hz : 0 < z)
    (hfourth : Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 4) P.law) :
    expectedK P θ z ≤ ENNReal.ofReal
      (1 + 2 * z / (CappedBaseStock.mean P - θ) +
        8 * Real.pi ^ 2 * centralFourth P /
          (CappedBaseStock.mean P - θ) ^ 4) := by
  classical
  set δ := CappedBaseStock.mean P - θ with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hμ4 : 0 ≤ centralFourth P := by
    unfold centralFourth; exact integral_nonneg (fun x => by positivity)
  set μP := CappedBaseStock.demandPathLaw P with hμP
  -- Step 1 & 2
  have h1 : expectedK P θ z ≤ ∑' n : ℕ, μP {d : DemandPath | 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ))} := by
    unfold expectedK
    calc ∫⁻ d, K d θ z ∂μP ≤ ∫⁻ d, ∑' n : ℕ,
          (if 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) then (1 : ℝ≥0∞) else 0) ∂μP :=
          lintegral_mono (fun d => K_le_tsum d θ z)
      _ = ∑' n : ℕ, ∫⁻ d, (if 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ)) then (1 : ℝ≥0∞) else 0) ∂μP := by
          apply lintegral_tsum
          intro n
          exact (Measurable.ite (measurableSet_A θ z n) measurable_const measurable_const).aemeasurable
      _ = _ := by
          refine tsum_congr (fun n => ?_)
          rw [← lintegral_indicator_one (measurableSet_A θ z n)]
          refine lintegral_congr (fun d => ?_)
          simp [Set.indicator_apply]
  -- Step 3
  set c0 : ℝ := 2 * z / δ with hc0
  have hc0pos : 0 < c0 := by positivity
  have h3 : ∀ n : ℕ, μP {d : DemandPath | 0 < z + ∑ i ∈ Finset.range n, (θ - (d i : ℝ))} ≤
      (if n ∈ Finset.range (⌈c0⌉₊) then (1 : ℝ≥0∞) else 0) +
        ENNReal.ofReal (48 * centralFourth P / δ ^ 4 * (1 / (n : ℝ) ^ 2)) := by
    intro n
    by_cases hn : (n : ℝ) < c0
    · have : n ∈ Finset.range (⌈c0⌉₊) := by
        rw [Finset.mem_range]; exact Nat.lt_ceil.mpr hn
      rw [if_pos this]
      calc _ ≤ 1 := prob_le_one
        _ ≤ _ := le_self_add
    · push_neg at hn
      have hn' : 2 * z ≤ n * δ := by
        have : 2 * z / δ ≤ n := hn
        rwa [div_le_iff₀ hδpos] at this
      calc _ ≤ ENNReal.ofReal (48 * centralFourth P / δ ^ 4 * (1 / (n : ℝ) ^ 2)) :=
            tail_bound P hfourth θ z hθ n hn' hz
        _ ≤ _ := le_add_self
  -- Step 4
  have hsumA : ∑' n : ℕ, (if n ∈ Finset.range (⌈c0⌉₊) then (1 : ℝ≥0∞) else 0)
      ≤ ENNReal.ofReal (1 + c0) := by
    rw [tsum_eq_sum (s := Finset.range ⌈c0⌉₊) (fun n hn => by rw [if_neg hn])]
    simp only [Finset.sum_boole, Finset.filter_true_of_mem (fun x hx => hx), Finset.card_range]
    have : (⌈c0⌉₊ : ℝ) ≤ 1 + c0 := by
      have := Nat.ceil_lt_add_one hc0pos.le
      linarith
    calc ((⌈c0⌉₊ : ℕ) : ℝ≥0∞) = ENNReal.ofReal (⌈c0⌉₊ : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal this
  have hsumB : ∑' n : ℕ, ENNReal.ofReal (48 * centralFourth P / δ ^ 4 * (1 / (n : ℝ) ^ 2))
      = ENNReal.ofReal (8 * Real.pi ^ 2 * centralFourth P / δ ^ 4) := by
    have hs : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
    have hs2 : HasSum (fun n : ℕ => 48 * centralFourth P / δ ^ 4 * (1 / (n : ℝ) ^ 2))
        (48 * centralFourth P / δ ^ 4 * (Real.pi ^ 2 / 6)) := hs.mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs2.summable, hs2.tsum_eq]
    congr 1
    ring
  calc expectedK P θ z ≤ _ := h1
    _ ≤ ∑' n : ℕ, ((if n ∈ Finset.range (⌈c0⌉₊) then (1 : ℝ≥0∞) else 0) +
          ENNReal.ofReal (48 * centralFourth P / δ ^ 4 * (1 / (n : ℝ) ^ 2))) :=
        ENNReal.tsum_le_tsum h3
    _ = _ := ENNReal.tsum_add
    _ ≤ ENNReal.ofReal (1 + c0) + ENNReal.ofReal (8 * Real.pi ^ 2 * centralFourth P / δ ^ 4) := by
        rw [hsumB]; exact add_le_add_left hsumA _
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

end AIMInventory.UnknownRho

open AIMInventory.UnknownRho


theorem solution (P : DemandLaw) (θ z : ℝ)
    (hθ : θ < CappedBaseStock.mean P) (hz : 0 < z)
    (hfourth : Integrable (fun d : ℝ≥0 => (d : ℝ) ^ 4) P.law) :
    expectedK P θ z ≤ ENNReal.ofReal
      (1 + 2 * z / (CappedBaseStock.mean P - θ) +
        8 * Real.pi ^ 2 * centralFourth P /
          (CappedBaseStock.mean P - θ) ^ 4) := by
  exact lemma9_core P θ z hθ hz hfourth
