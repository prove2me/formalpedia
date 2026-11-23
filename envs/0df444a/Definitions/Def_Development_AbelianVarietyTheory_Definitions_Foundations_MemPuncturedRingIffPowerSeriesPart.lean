-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:47.529701+00:00
-- url     : https://prove2.me/theorems/d3d25dc4-91e1-4cd7-aaa8-c58a92596a38
-- title:
--   Mem Punctured Ring Iff Power Series Part
-- statement:
--   Definitions and structural lemmas for Mem Punctured Ring Iff Power Series Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemPuncturedRingIffPowerSeriesPart.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric
noncomputable section
namespace GlobalTheory.Conv
def radius (f : ℂ⟦X⟧) : ℝ≥0∞ :=
  (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n f).radius
def sum (f : ℂ⟦X⟧) (u : ℂ) : ℂ := ∑' n, PowerSeries.coeff n f * u ^ n
def ConvergesOn (ε : ℝ) (f : ℂ⟦X⟧) : Prop :=
  ∀ u : ℂ, ‖u‖ < ε → Summable fun n => PowerSeries.coeff n f * u ^ n
theorem ConvergesOn.mono {ε ε' : ℝ} {f : ℂ⟦X⟧} (h : ConvergesOn ε f) (hε : ε' ≤ ε) :
    ConvergesOn ε' f := fun u hu => h u (hu.trans_le hε)
theorem ConvergesOn.hasSum {ε : ℝ} {f : ℂ⟦X⟧} (h : ConvergesOn ε f) {u : ℂ} (hu : ‖u‖ < ε) :
    HasSum (fun n => PowerSeries.coeff n f * u ^ n) (sum f u) := (h u hu).hasSum
theorem convergesOn_iff_le_radius {ε : ℝ} {f : ℂ⟦X⟧} :
    ConvergesOn ε f ↔ ENNReal.ofReal ε ≤ radius f := by
  constructor
  · intro h
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hr' : (r : ℝ) < ε := by
      rw [← ENNReal.ofReal_coe_nnreal] at hr
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 hr
    apply FormalMultilinearSeries.le_radius_of_summable_norm
    have := (summable_norm_iff.2 (h (r : ℝ) (by simpa using hr')))
    simpa [FormalMultilinearSeries.ofScalars_norm] using this
  · intro h u hu
    have hu' : u ∈ Metric.eball (0 : ℂ) (radius f) := by
      rw [mem_eball_zero_iff]
      refine lt_of_lt_of_le ?_ h
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).2 hu
    have := FormalMultilinearSeries.summable _ hu'
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using this
theorem radius_pos_iff {f : ℂ⟦X⟧} : 0 < radius f ↔ ∃ ε > 0, ConvergesOn ε f := by
  constructor
  · intro h
    obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
    refine ⟨r, by simpa using hr0, convergesOn_iff_le_radius.2 ?_⟩
    simpa using hr.le
  · rintro ⟨ε, hε, h⟩
    exact (ENNReal.ofReal_pos.2 hε).trans_le (convergesOn_iff_le_radius.1 h)
theorem hasSum_mul {f g : ℂ⟦X⟧} {u : ℂ} (hf : Summable fun n => PowerSeries.coeff n f * u ^ n)
    (hg : Summable fun n => PowerSeries.coeff n g * u ^ n) :
    HasSum (fun n => PowerSeries.coeff n (f * g) * u ^ n) (sum f u * sum g u) := by
  have hf' := summable_norm_iff.2 hf
  have hg' := summable_norm_iff.2 hg
  have key : ∀ n, PowerSeries.coeff n (f * g) * u ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (PowerSeries.coeff kl.1 f * u ^ kl.1) *
        (PowerSeries.coeff kl.2 g * u ^ kl.2) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hkl]
    ring
  simp only [key]
  rw [sum, sum, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf' hg']
  exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hf' hg').of_norm.hasSum
theorem hasSum_C (c u : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.C c) * u ^ n) c := by
  have := hasSum_single (f := fun n => PowerSeries.coeff n (PowerSeries.C c) * u ^ n) 0
    (fun n hn => by simp [PowerSeries.coeff_C, hn])
  simpa using this
theorem hasSum_X (u : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.X : ℂ⟦X⟧) * u ^ n) u := by
  have := hasSum_single (f := fun n => PowerSeries.coeff n (PowerSeries.X : ℂ⟦X⟧) * u ^ n) 1
    (fun n hn => by simp [PowerSeries.coeff_X, hn])
  simpa using this
@[simp] theorem sum_C (c u : ℂ) : sum (PowerSeries.C c) u = c := (hasSum_C c u).tsum_eq
@[simp] theorem sum_X (u : ℂ) : sum PowerSeries.X u = u := (hasSum_X u).tsum_eq
@[simp] theorem sum_zero_right (f : ℂ⟦X⟧) : sum f 0 = PowerSeries.constantCoeff f := by
  have := hasSum_single (f := fun n => PowerSeries.coeff n f * (0 : ℂ) ^ n) 0
    (fun n hn => by simp [hn])
  simpa [sum] using this.tsum_eq
def discSeries (ε : ℝ) : Subalgebra ℂ ℂ⟦X⟧ where
  carrier := {f | ConvergesOn ε f}
  mul_mem' hf hg u hu := (hasSum_mul (hf u hu) (hg u hu)).summable
  add_mem' hf hg u hu := by simpa [add_mul] using (hf u hu).add (hg u hu)
  algebraMap_mem' c u _ := (hasSum_C c u).summable
theorem mem_discSeries {ε : ℝ} {f : ℂ⟦X⟧} : f ∈ discSeries ε ↔ ConvergesOn ε f := Iff.rfl
theorem discSeries_anti : Antitone discSeries := fun _ _ h _ hf => ConvergesOn.mono hf h
theorem X_mem_discSeries (ε : ℝ) : (PowerSeries.X : ℂ⟦X⟧) ∈ discSeries ε :=
  fun u _ => (hasSum_X u).summable
theorem coe_mem_discSeries (ε : ℝ) (p : Polynomial ℂ) : (p : ℂ⟦X⟧) ∈ discSeries ε := by
  induction p using Polynomial.induction_on with
  | C a => simpa using (discSeries ε).algebraMap_mem a
  | add p q hp hq => simpa using add_mem hp hq
  | monomial n a h =>
    simpa [pow_succ, mul_assoc] using mul_mem h (X_mem_discSeries ε)
def evalDisc (ε : ℝ) (u₀ : ℂ) (h : ‖u₀‖ < ε) : discSeries ε →ₐ[ℂ] ℂ where
  toFun f := sum f u₀
  map_one' := by simpa using sum_C 1 u₀
  map_mul' f g := (hasSum_mul (f.2 u₀ h) (g.2 u₀ h)).tsum_eq
  map_zero' := by simp [sum]
  map_add' f g := by
    simpa [sum, add_mul] using (f.2 u₀ h).tsum_add (g.2 u₀ h)
  commutes' c := sum_C c u₀
@[simp] theorem evalDisc_apply {ε : ℝ} {u₀ : ℂ} (h : ‖u₀‖ < ε) (f : discSeries ε) :
    evalDisc ε u₀ h f = sum f u₀ := rfl
theorem convergesOn_X_mul {ε : ℝ} {f : ℂ⟦X⟧} :
    ConvergesOn ε (PowerSeries.X * f) ↔ ConvergesOn ε f := by
  refine ⟨fun h u hu => ?_, fun h => mul_mem (X_mem_discSeries ε) (mem_discSeries.2 h)⟩
  rcases eq_or_ne u 0 with rfl | h0
  · exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp [show n ≠ 0 by simpa using hn]
  · have := ((summable_nat_add_iff 1).2 (h u hu)).mul_right u⁻¹
    refine this.congr fun n => ?_
    rw [PowerSeries.coeff_succ_X_mul]
    field_simp
    ring
theorem convergesOn_X_pow_mul {ε : ℝ} {f : ℂ⟦X⟧} (n : ℕ) :
    ConvergesOn ε (PowerSeries.X ^ n * f) ↔ ConvergesOn ε f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, convergesOn_X_mul, ih]
theorem hasFPowerSeriesOnBall_sum {f : ℂ⟦X⟧} (h : 0 < radius f) :
    HasFPowerSeriesOnBall (sum f)
      (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n f) 0 (radius f) := by
  have h1 : sum f = (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n f).sum := by
    funext u
    simp [sum, FormalMultilinearSeries.sum, mul_comm]
  rw [h1]
  exact FormalMultilinearSeries.hasFPowerSeriesOnBall _ h
theorem ConvergesOn.analyticOnNhd {ε : ℝ} {f : ℂ⟦X⟧} (h : ConvergesOn ε f) :
    AnalyticOnNhd ℂ (sum f) (ball 0 ε) := by
  intro u hu
  have hu' : ‖u‖ < ε := by simpa using hu
  have hε : 0 < ε := (norm_nonneg u).trans_lt hu'
  refine (hasFPowerSeriesOnBall_sum (radius_pos_iff.2 ⟨ε, hε, h⟩)).analyticAt_of_mem ?_
  rw [mem_eball_zero_iff]
  refine lt_of_lt_of_le ?_ (convergesOn_iff_le_radius.1 h)
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).2 hu'
def taylor (F : ℂ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0
theorem hasSum_taylor {ε : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 ε)) {u : ℂ}
    (hu : ‖u‖ < ε) : HasSum (fun n => PowerSeries.coeff n (taylor F) * u ^ n) (F u) := by
  have := Complex.hasSum_taylorSeries_on_ball hF (z := u) (by simpa using hu)
  refine this.congr_fun fun n => ?_
  simp only [taylor, PowerSeries.coeff_mk, sub_zero, smul_eq_mul]
  ring
theorem taylor_mem_discSeries {ε : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 ε)) :
    taylor F ∈ discSeries ε := fun _ hu => (hasSum_taylor hF hu).summable
theorem sum_taylor {ε : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 ε)) {u : ℂ}
    (hu : ‖u‖ < ε) : sum (taylor F) u = F u := (hasSum_taylor hF hu).tsum_eq
def convSeries : Subalgebra ℂ ℂ⟦X⟧ where
  carrier := {f | 0 < radius f}
  mul_mem' {f g} hf hg := by
    obtain ⟨ε, hε, hf⟩ := radius_pos_iff.1 hf
    obtain ⟨δ, hδ, hg⟩ := radius_pos_iff.1 hg
    exact radius_pos_iff.2 ⟨min ε δ, lt_min hε hδ, mul_mem
      (discSeries_anti (min_le_left ε δ) hf) (discSeries_anti (min_le_right ε δ) hg)⟩
  add_mem' {f g} hf hg := by
    obtain ⟨ε, hε, hf⟩ := radius_pos_iff.1 hf
    obtain ⟨δ, hδ, hg⟩ := radius_pos_iff.1 hg
    exact radius_pos_iff.2 ⟨min ε δ, lt_min hε hδ, add_mem
      (discSeries_anti (min_le_left ε δ) hf) (discSeries_anti (min_le_right ε δ) hg)⟩
  algebraMap_mem' c := radius_pos_iff.2 ⟨1, one_pos, (discSeries 1).algebraMap_mem c⟩
theorem mem_convSeries {f : ℂ⟦X⟧} : f ∈ convSeries ↔ ∃ ε > 0, f ∈ discSeries ε := radius_pos_iff
theorem discSeries_le_convSeries {ε : ℝ} (hε : 0 < ε) : discSeries ε ≤ convSeries :=
  fun _ hf => mem_convSeries.2 ⟨ε, hε, hf⟩
theorem mem_convSeries_iff_eventually {f : ℂ⟦X⟧} :
    f ∈ convSeries ↔ ∀ᶠ u in 𝓝 (0 : ℂ), Summable fun n => PowerSeries.coeff n f * u ^ n := by
  simp only [mem_convSeries, Metric.eventually_nhds_iff, dist_zero_right]
  rfl
theorem eventually_hasSum (f : convSeries) :
    ∀ᶠ u in 𝓝 (0 : ℂ), HasSum (fun n => PowerSeries.coeff n (f : ℂ⟦X⟧) * u ^ n) (sum f u) :=
  (mem_convSeries_iff_eventually.1 f.2).mono fun _ h => h.hasSum
theorem analyticAt_sum {f : ℂ⟦X⟧} (hf : f ∈ convSeries) : AnalyticAt ℂ (sum f) 0 :=
  (hasFPowerSeriesOnBall_sum hf).analyticAt
theorem taylor_spec {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    taylor F ∈ convSeries ∧ sum (taylor F) =ᶠ[𝓝 0] F := by
  obtain ⟨ε, hε, h⟩ := hF.exists_ball_analyticOnNhd
  refine ⟨discSeries_le_convSeries hε (taylor_mem_discSeries h.differentiableOn), ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hε] with u hu
  exact sum_taylor h.differentiableOn (by simpa using hu)
theorem eq_zero_of_frequently_sum_eq_zero {f : ℂ⟦X⟧} (hf : f ∈ convSeries)
    (h : ∃ᶠ u in 𝓝[≠] (0 : ℂ), sum f u = 0) : f = 0 := by
  have h1 := (analyticAt_sum hf).frequently_zero_iff_eventually_zero.1 h
  have h2 := (hasFPowerSeriesOnBall_sum hf).hasFPowerSeriesAt.eq_zero_of_eventually h1
  rw [FormalMultilinearSeries.ofScalars_series_eq_zero] at h2
  ext n
  simpa using congrFun h2 n
def germ : convSeries →+* Germ (𝓝 (0 : ℂ)) ℂ where
  toFun f := (sum f : Germ (𝓝 (0 : ℂ)) ℂ)
  map_one' := by
    rw [← Germ.coe_one, Germ.coe_eq]
    exact Eventually.of_forall fun u => by simpa using sum_C 1 u
  map_mul' f g := by
    rw [← Germ.coe_mul, Germ.coe_eq]
    filter_upwards [eventually_hasSum f, eventually_hasSum g] with u hf hg
    exact (hasSum_mul hf.summable hg.summable).tsum_eq
  map_zero' := by
    rw [← Germ.coe_zero, Germ.coe_eq]
    exact Eventually.of_forall fun u => by simp [sum]
  map_add' f g := by
    rw [← Germ.coe_add, Germ.coe_eq]
    filter_upwards [eventually_hasSum f, eventually_hasSum g] with u hf hg
    simpa [sum, add_mul] using hf.summable.tsum_add hg.summable
theorem germ_apply (f : convSeries) : germ f = (sum f : Germ (𝓝 (0 : ℂ)) ℂ) := rfl
theorem germ_injective : Function.Injective germ := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => Subtype.ext ?_
  rw [germ_apply, ← Germ.coe_zero, Germ.coe_eq] at hf
  exact eq_zero_of_frequently_sum_eq_zero f.2 (hf.filter_mono nhdsWithin_le_nhds).frequently
theorem mem_range_germ {F : ℂ → ℂ} :
    (F : Germ (𝓝 (0 : ℂ)) ℂ) ∈ germ.range ↔ AnalyticAt ℂ F 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact (analyticAt_sum f.2).congr (Germ.coe_eq.1 hf)
  · intro h
    exact ⟨⟨taylor F, (taylor_spec h).1⟩, Germ.coe_eq.2 (taylor_spec h).2⟩
def u : convSeries := ⟨PowerSeries.X, discSeries_le_convSeries one_pos (X_mem_discSeries 1)⟩
@[simp] theorem coe_u : (u : ℂ⟦X⟧) = PowerSeries.X := rfl
theorem X_pow_mul_mem_convSeries {f : ℂ⟦X⟧} (n : ℕ) :
    PowerSeries.X ^ n * f ∈ convSeries ↔ f ∈ convSeries := by
  simp only [mem_convSeries, mem_discSeries, convergesOn_X_pow_mul]
theorem isUnit_iff {f : convSeries} : IsUnit f ↔ PowerSeries.constantCoeff (f : ℂ⟦X⟧) ≠ 0 := by
  constructor
  · intro h
    exact (h.map (PowerSeries.constantCoeff.comp convSeries.val.toRingHom)).ne_zero
  · intro h
    have h0 : sum f 0 ≠ 0 := by simpa using h
    obtain ⟨g, hg⟩ := mem_range_germ.2 ((analyticAt_sum f.2).inv h0)
    refine IsUnit.of_mul_eq_one g (germ_injective ?_)
    rw [map_mul, map_one, show germ g = _ from hg, germ_apply, ← Germ.coe_mul, ← Germ.coe_one,
      Germ.coe_eq]
    filter_upwards [(analyticAt_sum f.2).continuousAt.eventually_ne h0] with v hv
    simp [hv]
instance : IsLocalHom (algebraMap convSeries ℂ⟦X⟧) where
  map_nonunit _ hf := isUnit_iff.2 (PowerSeries.isUnit_iff_constantCoeff.1 hf).ne_zero
theorem u_pow_dvd_iff {f : convSeries} {n : ℕ} :
    u ^ n ∣ f ↔ (PowerSeries.X : ℂ⟦X⟧) ^ n ∣ (f : ℂ⟦X⟧) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, by simp⟩
  · rintro ⟨g, hg⟩
    exact ⟨⟨g, (X_pow_mul_mem_convSeries n).1 (hg ▸ f.2)⟩, Subtype.ext (by simpa using hg)⟩
theorem irreducible_u : Irreducible u :=
  Irreducible.of_map (f := algebraMap convSeries ℂ⟦X⟧) PowerSeries.X_irreducible
theorem associated_u_pow_order {f : convSeries} (hf : f ≠ 0) :
    Associated (u ^ (f : ℂ⟦X⟧).order.toNat) f := by
  have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := (f : ℂ⟦X⟧))
  let g : convSeries := ⟨_, (X_pow_mul_mem_convSeries _).1 (h.symm ▸ f.2)⟩
  have hg : IsUnit g := isUnit_iff.2
    (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.2 fun h0 => hf (Subtype.ext h0))
  exact ⟨hg.unit, Subtype.ext (by simpa [g] using h)⟩
instance : IsDiscreteValuationRing convSeries :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨u, irreducible_u, fun hf => ⟨_, associated_u_pow_order hf⟩⟩
theorem maximalIdeal_eq : IsLocalRing.maximalIdeal convSeries = Ideal.span {u} :=
  irreducible_u.maximalIdeal_eq
theorem mem_maximalIdeal {f : convSeries} :
    f ∈ IsLocalRing.maximalIdeal convSeries ↔ PowerSeries.constantCoeff (f : ℂ⟦X⟧) = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff, not_not]
theorem mem_maximalIdeal_pow {f : convSeries} {n : ℕ} :
    f ∈ IsLocalRing.maximalIdeal convSeries ^ n ↔
      (f : ℂ⟦X⟧) ∈ (Ideal.span {PowerSeries.X} : Ideal ℂ⟦X⟧) ^ n := by
  rw [maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, u_pow_dvd_iff]
def evalZero : convSeries →ₐ[ℂ] ℂ where
  __ := PowerSeries.constantCoeff.comp convSeries.val.toRingHom
  commutes' c := by simp
@[simp] theorem evalZero_apply (f : convSeries) :
    evalZero f = PowerSeries.constantCoeff (f : ℂ⟦X⟧) := rfl
def residueFieldEquiv : IsLocalRing.ResidueField convSeries ≃ₐ[ℂ] ℂ :=
  (Ideal.quotientEquivAlgOfEq ℂ (J := RingHom.ker evalZero)
    (Ideal.ext fun _ => mem_maximalIdeal)).trans
    (Ideal.quotientKerAlgEquivOfSurjective fun c => ⟨algebraMap ℂ _ c, evalZero.commutes c⟩)
@[simp] theorem residueFieldEquiv_residue (f : convSeries) :
    residueFieldEquiv (IsLocalRing.residue _ f) = PowerSeries.constantCoeff (f : ℂ⟦X⟧) := rfl
theorem eventually_sum_eval (P : Polynomial convSeries) (a : convSeries) :
    ∀ᶠ v in 𝓝 (0 : ℂ), sum (P.eval a : convSeries) v =
      ∑ i ∈ Finset.range (P.natDegree + 1), sum (P.coeff i : convSeries) v * sum a v ^ i := by
  have h : germ (P.eval a) = ((fun v => ∑ i ∈ Finset.range (P.natDegree + 1),
      sum (P.coeff i : convSeries) v * sum a v ^ i : ℂ → ℂ) : Germ (𝓝 (0 : ℂ)) ℂ) := by
    rw [Polynomial.eval_eq_sum_range, map_sum]
    simp only [map_mul, map_pow, germ_apply]
    have := map_sum (Germ.coeRingHom (R := ℂ) (𝓝 (0 : ℂ)))
      (fun i => sum (P.coeff i : convSeries) * sum a ^ i) (Finset.range (P.natDegree + 1))
    simp only [map_mul, map_pow, Germ.coe_coeRingHom] at this
    rw [← this]
    congr 1
    funext v
    simp
  exact Germ.coe_eq.1 h
theorem exists_isRoot (P : Polynomial convSeries) (z₀ : ℂ)
    (h₀ : (P.map (evalZero : convSeries →+* ℂ)).eval z₀ = 0)
    (h₁ : (P.map (evalZero : convSeries →+* ℂ)).derivative.eval z₀ ≠ 0) :
    ∃ a : convSeries, P.IsRoot a ∧ evalZero a = z₀ := by
  set F : ℂ × ℂ → ℂ := fun p =>
    ∑ i ∈ Finset.range (P.natDegree + 1), sum (P.coeff i : convSeries) p.1 * p.2 ^ i with hF
  have hFa : AnalyticAt ℂ F (0, z₀) := by
    refine Finset.analyticAt_fun_sum _ fun i _ => AnalyticAt.mul ?_ (analyticAt_snd.pow i)
    exact AnalyticAt.comp (g := sum (P.coeff i : convSeries)) (f := Prod.fst)
      (analyticAt_sum (P.coeff i).2) analyticAt_fst
  have hF0 : ∀ z, F (0, z) = (P.map (evalZero : convSeries →+* ℂ)).eval z := by
    intro z
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    simp [hF]
  have hc : ContDiffAt ℂ ω F (0, z₀) := hFa.contDiffAt
  have hinv : (fderiv ℂ F (0, z₀) ∘L .inr ℂ ℂ ℂ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h₁), ?_⟩
    have h2 : HasFDerivAt (fun z : ℂ => F (0, z)) (fderiv ℂ F (0, z₀) ∘L .inr ℂ ℂ ℂ) z₀ :=
      HasFDerivAt.comp (g := F) (f := fun z : ℂ => ((0 : ℂ), z)) z₀
        hFa.differentiableAt.hasFDerivAt (hasFDerivAt_prodMk_right (0 : ℂ) z₀)
    have h3 := ((P.map (evalZero : convSeries →+* ℂ)).hasDerivAt z₀).hasFDerivAt
    simp only [hF0] at h2
    rw [h2.unique h3]
    ext
    simp
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hg : AnalyticAt ℂ (hc.implicitFunction hω hinv) 0 :=
    (hc.contDiffAt_implicitFunction hω hinv).analyticAt
  have hg0 : hc.implicitFunction hω hinv 0 = z₀ := hc.implicitFunction_apply_self hω hinv
  have hge := hc.eventually_apply_implicitFunction hω hinv
  obtain ⟨ha, hsum⟩ := taylor_spec hg
  refine ⟨⟨_, ha⟩, germ_injective ?_, ?_⟩
  · rw [map_zero, germ_apply, ← Germ.coe_zero, Germ.coe_eq]
    filter_upwards [eventually_sum_eval P ⟨_, ha⟩, hsum, hge] with v h1 h2 h3
    rw [h1]
    simp only [h2]
    rw [hF0, h₀] at h3
    exact h3
  · rw [evalZero_apply, ← sum_zero_right]
    exact hsum.self_of_nhds.trans hg0
instance : HenselianLocalRing convSeries where
  is_henselian P _ a₀ h₀ h₁ := by
    obtain ⟨a, ha, ha'⟩ := exists_isRoot P (evalZero a₀)
      (by
        have := mem_maximalIdeal.1 h₀
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (evalZero : convSeries →+* ℂ) a₀).trans this)
      (by
        have := isUnit_iff.1 h₁
        rw [Polynomial.derivative_map, Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (evalZero : convSeries →+* ℂ) a₀).trans_ne this)
    refine ⟨a, ha, mem_maximalIdeal.2 ?_⟩
    rw [← evalZero_apply, map_sub, ha', sub_self]
def quotientMap (n : ℕ) : (convSeries ⧸ IsLocalRing.maximalIdeal convSeries ^ n) →ₐ[ℂ]
    ℂ⟦X⟧ ⧸ (Ideal.span {PowerSeries.X} : Ideal ℂ⟦X⟧) ^ n :=
  Ideal.quotientMapₐ _ convSeries.val fun _ hf => mem_maximalIdeal_pow.1 hf
@[simp] theorem quotientMap_mk (n : ℕ) (f : convSeries) :
    quotientMap n (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (f : ℂ⟦X⟧) := rfl
theorem quotientMap_bijective (n : ℕ) : Function.Bijective (quotientMap n) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_maximalIdeal_pow.2 hx)
  · intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk _ ⟨(PowerSeries.trunc n f : ℂ⟦X⟧),
      discSeries_le_convSeries one_pos (coe_mem_discSeries 1 _)⟩, ?_⟩
    rw [quotientMap_mk, Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [PowerSeries.coeff_trunc, hm]
def quotientEquiv (n : ℕ) : (convSeries ⧸ IsLocalRing.maximalIdeal convSeries ^ n) ≃ₐ[ℂ]
    ℂ⟦X⟧ ⧸ (Ideal.span {PowerSeries.X} : Ideal ℂ⟦X⟧) ^ n :=
  AlgEquiv.ofBijective (quotientMap n) (quotientMap_bijective n)
@[simp] theorem quotientEquiv_mk (n : ℕ) (f : convSeries) :
    quotientEquiv n (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (f : ℂ⟦X⟧) := rfl
theorem factor_quotientMap_evalₐ {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ ℂ (Ideal.pow_le_pow_right hle)).comp
      ((quotientMap n).comp ((AdicCompletion.evalₐ _ n).restrictScalars ℂ)) =
      (quotientMap m).comp ((AdicCompletion.evalₐ _ m).restrictScalars ℂ) := by
  ext x
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective _ _ x
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AdicCompletion.evalₐ_mk,
    quotientMap_mk]
  change Ideal.Quotient.mk _ _ = _
  rw [Ideal.Quotient.eq]
  have := (AdicCompletion.AdicCauchySequence.mk_eq_mk hle a)
  rw [Submodule.Quotient.eq, smul_eq_mul, Ideal.mul_top] at this
  exact mem_maximalIdeal_pow.1 this
def completionMap : AdicCompletion (IsLocalRing.maximalIdeal convSeries) convSeries →ₐ[ℂ] ℂ⟦X⟧ :=
  IsAdicComplete.liftAlgHom (Ideal.span {PowerSeries.X})
    (fun n => (quotientMap n).comp ((AdicCompletion.evalₐ _ n).restrictScalars ℂ))
    factor_quotientMap_evalₐ
theorem mk_completionMap (n : ℕ)
    (x : AdicCompletion (IsLocalRing.maximalIdeal convSeries) convSeries) :
    Ideal.Quotient.mk ((Ideal.span {PowerSeries.X} : Ideal ℂ⟦X⟧) ^ n) (completionMap x) =
      quotientMap n (AdicCompletion.evalₐ _ n x) :=
  IsAdicComplete.mk_liftAlgHom _
    (fun n => (quotientMap n).comp ((AdicCompletion.evalₐ _ n).restrictScalars ℂ))
    factor_quotientMap_evalₐ n x
theorem completionMap_bijective : Function.Bijective completionMap := by
  constructor
  · intro x y h
    refine AdicCompletion.ext_evalₐ fun n => (quotientMap_bijective n).1 ?_
    rw [← mk_completionMap, ← mk_completionMap, h]
  · intro f
    let ψ : ℂ⟦X⟧ →ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal convSeries) convSeries :=
      AdicCompletion.liftAlgHom _
        (fun n => (quotientEquiv n).symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _))
        fun {m n} hle => by
          ext1 g
          obtain ⟨x, hx⟩ := (quotientEquiv n).surjective (Ideal.Quotient.mk _ g)
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
          change Ideal.Quotient.factorₐ ℂ (Ideal.pow_le_pow_right hle)
            ((quotientEquiv n).symm (Ideal.Quotient.mk _ g)) =
            (quotientEquiv m).symm (Ideal.Quotient.mk _ g)
          rw [← hx, AlgEquiv.symm_apply_apply, AlgEquiv.eq_symm_apply]
          change Ideal.Quotient.mk _ (a : ℂ⟦X⟧) = _
          rw [quotientEquiv_mk, Ideal.Quotient.eq] at hx
          exact Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right hle hx)
    refine ⟨ψ f, ?_⟩
    rw [← sub_eq_zero]
    refine IsHausdorff.haus' (I := (Ideal.span {PowerSeries.X} : Ideal ℂ⟦X⟧)) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, mk_completionMap]
    rw [AdicCompletion.evalₐ_liftAlgHom]
    exact (quotientEquiv n).apply_symm_apply _
def completionEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal convSeries) convSeries ≃ₐ[ℂ] ℂ⟦X⟧ :=
  AlgEquiv.ofBijective completionMap completionMap_bijective
@[simp] theorem completionEquiv_of (f : convSeries) :
    completionEquiv (AdicCompletion.of _ _ f) = (f : ℂ⟦X⟧) := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := (Ideal.span {PowerSeries.X} : Ideal ℂ⟦X⟧)) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  refine (mk_completionMap n _).trans ?_
  rw [AdicCompletion.evalₐ_of, quotientMap_mk]
instance : Module.FaithfullyFlat convSeries ℂ⟦X⟧ :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom
def puncturedDisc (ε : ℝ) : Set ℂ := ball 0 ε \ {0}
theorem mem_puncturedDisc {ε : ℝ} {v : ℂ} : v ∈ puncturedDisc ε ↔ v ≠ 0 ∧ ‖v‖ < ε := by
  simp [puncturedDisc, and_comm]
theorem isOpen_puncturedDisc (ε : ℝ) : IsOpen (puncturedDisc ε) :=
  isOpen_ball.sdiff isClosed_singleton
theorem puncturedDisc_mono : Monotone puncturedDisc := fun _ _ h _ hv =>
  mem_puncturedDisc.2 ⟨(mem_puncturedDisc.1 hv).1, (mem_puncturedDisc.1 hv).2.trans_le h⟩
theorem puncturedDisc_mem_nhds {ε : ℝ} (hε : 0 < ε) : puncturedDisc ε ∈ 𝓝[≠] (0 : ℂ) :=
  inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 hε)) self_mem_nhdsWithin
theorem eventually_iff_exists_puncturedDisc {p : ℂ → Prop} :
    (∀ᶠ v in 𝓝[≠] (0 : ℂ), p v) ↔ ∃ ε > 0, ∀ v ∈ puncturedDisc ε, p v := by
  constructor
  · intro h
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhdsWithin_iff.1 h
    exact ⟨ε, hε, fun v hv => h hv⟩
  · rintro ⟨ε, hε, h⟩
    exact mem_of_superset (puncturedDisc_mem_nhds hε) h
def lsum (f : ℂ⸨X⸩) (v : ℂ) : ℂ := ∑' n : ℤ, f.coeff n * v ^ n
theorem hasSum_coe_iff {g : ℂ⟦X⟧} {v a : ℂ} :
    HasSum (fun n : ℤ => (g : ℂ⸨X⸩).coeff n * v ^ n) a ↔
      HasSum (fun n : ℕ => PowerSeries.coeff n g * v ^ n) a := by
  rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff]
  · simp [Function.comp_def]
  · intro n hn
    have : n < 0 := by
      by_contra h
      exact hn ⟨n.toNat, by omega⟩
    simp [PowerSeries.coeff_coe, this]
theorem hasSum_single_mul {f : ℂ⸨X⸩} {v a : ℂ} (hv : v ≠ 0) (m : ℤ)
    (h : HasSum (fun n : ℤ => f.coeff n * v ^ n) a) :
    HasSum (fun n : ℤ => (HahnSeries.single m (1 : ℂ) * f).coeff n * v ^ n) (v ^ m * a) := by
  rw [← (Equiv.addRight m).hasSum_iff]
  refine (h.mul_left (v ^ m)).congr_fun fun n => ?_
  simp only [Function.comp_apply, Equiv.coe_addRight, HahnSeries.coeff_single_mul_add,
    zpow_add₀ hv]
  ring
theorem summable_single_mul_iff {f : ℂ⸨X⸩} {v : ℂ} (hv : v ≠ 0) (m : ℤ) :
    (Summable fun n : ℤ => (HahnSeries.single m (1 : ℂ) * f).coeff n * v ^ n) ↔
      Summable fun n : ℤ => f.coeff n * v ^ n := by
  refine ⟨fun h => ?_, fun h => (hasSum_single_mul hv m h.hasSum).summable⟩
  have := (hasSum_single_mul hv (-m) h.hasSum).summable
  rwa [← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one,
    HahnSeries.single_zero_one, one_mul] at this
theorem summable_single_mul_coe_iff {g : ℂ⟦X⟧} {v : ℂ} (hv : v ≠ 0) (m : ℤ) :
    (Summable fun n : ℤ => (HahnSeries.single m (1 : ℂ) * (g : ℂ⸨X⸩)).coeff n * v ^ n) ↔
      Summable fun n : ℕ => PowerSeries.coeff n g * v ^ n := by
  rw [summable_single_mul_iff hv]
  exact exists_congr fun _ => hasSum_coe_iff
theorem hasSum_single_mul_coe {g : ℂ⟦X⟧} {v : ℂ} (hv : v ≠ 0) (m : ℤ)
    (h : Summable fun n : ℕ => PowerSeries.coeff n g * v ^ n) :
    HasSum (fun n : ℤ => (HahnSeries.single m (1 : ℂ) * (g : ℂ⸨X⸩)).coeff n * v ^ n)
      (v ^ m * sum g v) :=
  hasSum_single_mul hv m (hasSum_coe_iff.2 h.hasSum)
@[simp] theorem lsum_coe (g : ℂ⟦X⟧) (v : ℂ) : lsum (g : ℂ⸨X⸩) v = sum g v := by
  by_cases h : Summable fun n : ℕ => PowerSeries.coeff n g * v ^ n
  · exact (hasSum_coe_iff.2 h.hasSum).tsum_eq
  · rw [sum, tsum_eq_zero_of_not_summable h, lsum, tsum_eq_zero_of_not_summable]
    exact fun h' => h (hasSum_coe_iff.1 h'.hasSum).summable
theorem hasSum_mul_laurent {f g : ℂ⸨X⸩} {v : ℂ} (hv : v ≠ 0)
    (hf : Summable fun n : ℤ => f.coeff n * v ^ n) (hg : Summable fun n : ℤ => g.coeff n * v ^ n) :
    HasSum (fun n : ℤ => (f * g).coeff n * v ^ n) (lsum f v * lsum g v) := by
  obtain ⟨a, p, rfl⟩ : ∃ (a : ℤ) (p : ℂ⟦X⟧), f = HahnSeries.single a (1 : ℂ) * (p : ℂ⸨X⸩) :=
    ⟨_, _, f.single_order_mul_powerSeriesPart.symm⟩
  obtain ⟨b, q, rfl⟩ : ∃ (a : ℤ) (p : ℂ⟦X⟧), g = HahnSeries.single a (1 : ℂ) * (p : ℂ⸨X⸩) :=
    ⟨_, _, g.single_order_mul_powerSeriesPart.symm⟩
  rw [summable_single_mul_coe_iff hv] at hf hg
  rw [lsum, lsum, (hasSum_single_mul_coe hv a hf).tsum_eq, (hasSum_single_mul_coe hv b hg).tsum_eq,
    mul_mul_mul_comm, HahnSeries.single_mul_single, mul_one, ← PowerSeries.coe_mul,
    mul_mul_mul_comm, ← zpow_add₀ hv]
  exact hasSum_single_mul hv _ (hasSum_coe_iff.2 (hasSum_mul hf hg))
theorem hasSum_single_laurent (m : ℤ) (c v : ℂ) :
    HasSum (fun n : ℤ => (HahnSeries.single m c : ℂ⸨X⸩).coeff n * v ^ n) (c * v ^ m) := by
  have := hasSum_single (f := fun n : ℤ => (HahnSeries.single m c : ℂ⸨X⸩).coeff n * v ^ n) m
    (fun n hn => by simp [HahnSeries.coeff_single_of_ne hn])
  simpa using this
@[simp] theorem lsum_single (m : ℤ) (c v : ℂ) : lsum (HahnSeries.single m c) v = c * v ^ m :=
  (hasSum_single_laurent m c v).tsum_eq
@[simp] theorem lsum_algebraMap (c v : ℂ) : lsum (algebraMap ℂ ℂ⸨X⸩ c) v = c := by
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, lsum_single]
  simp
def puncturedRing (ε : ℝ) : Subalgebra ℂ ℂ⸨X⸩ where
  carrier := {f | ∀ v ∈ puncturedDisc ε, Summable fun n : ℤ => f.coeff n * v ^ n}
  mul_mem' hf hg v hv :=
    (hasSum_mul_laurent (mem_puncturedDisc.1 hv).1 (hf v hv) (hg v hv)).summable
  add_mem' hf hg v hv := by simpa [add_mul] using (hf v hv).add (hg v hv)
  algebraMap_mem' c v _ := by
    rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
    exact (hasSum_single_laurent 0 c v).summable
theorem mem_puncturedRing {ε : ℝ} {f : ℂ⸨X⸩} :
    f ∈ puncturedRing ε ↔ ∀ v ∈ puncturedDisc ε, Summable fun n : ℤ => f.coeff n * v ^ n := Iff.rfl
theorem puncturedRing_anti : Antitone puncturedRing :=
  fun _ _ h _ hf v hv => hf v (puncturedDisc_mono h hv)
theorem single_mem_puncturedRing (ε : ℝ) (m : ℤ) (c : ℂ) :
    (HahnSeries.single m c : ℂ⸨X⸩) ∈ puncturedRing ε :=
  fun v _ => (hasSum_single_laurent m c v).summable
theorem single_mul_coe_mem_puncturedRing {ε : ℝ} {g : ℂ⟦X⟧} (m : ℤ) :
    HahnSeries.single m (1 : ℂ) * (g : ℂ⸨X⸩) ∈ puncturedRing ε ↔ g ∈ discSeries ε := by
  constructor
  · intro h v hv
    rcases eq_or_ne v 0 with rfl | h0
    · exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
        simp [show n ≠ 0 by simpa using hn]
    · exact (summable_single_mul_coe_iff h0 m).1 (h v (mem_puncturedDisc.2 ⟨h0, hv⟩))
  · intro h v hv
    exact (summable_single_mul_coe_iff (mem_puncturedDisc.1 hv).1 m).2
      (h v (mem_puncturedDisc.1 hv).2)
theorem coe_mem_puncturedRing {ε : ℝ} {g : ℂ⟦X⟧} :
    (g : ℂ⸨X⸩) ∈ puncturedRing ε ↔ g ∈ discSeries ε := by
  rw [← single_mul_coe_mem_puncturedRing 0, HahnSeries.single_zero_one, one_mul]
theorem mem_puncturedRing_iff_powerSeriesPart {ε : ℝ} {f : ℂ⸨X⸩} :
    f ∈ puncturedRing ε ↔ f.powerSeriesPart ∈ discSeries ε := by
  rw [← single_mul_coe_mem_puncturedRing f.order, f.single_order_mul_powerSeriesPart]
theorem mem_puncturedRing_iff_exists {ε : ℝ} {f : ℂ⸨X⸩} :
    f ∈ puncturedRing ε ↔ ∃ n : ℕ, ∃ g ∈ discSeries ε,
      f = HahnSeries.single (-n : ℤ) (1 : ℂ) * (g : ℂ⸨X⸩) := by
  constructor
  · intro hf
    obtain ⟨⟨g, _, n, rfl⟩, h⟩ :=
      IsLocalization.surj (Submonoid.powers (PowerSeries.X : ℂ⟦X⟧)) f
    have h' : f = HahnSeries.single (-n : ℤ) (1 : ℂ) * (g : ℂ⸨X⸩) := by
      simp only [LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X_pow] at h
      rw [← h, mul_comm f, ← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one,
        HahnSeries.single_zero_one, one_mul]
    exact ⟨n, g, (single_mul_coe_mem_puncturedRing _).1 (h' ▸ hf), h'⟩
  · rintro ⟨n, g, hg, rfl⟩
    exact (single_mul_coe_mem_puncturedRing _).2 hg
def evalAt (ε : ℝ) (u₀ : ℂ) (h : u₀ ∈ puncturedDisc ε) : puncturedRing ε →ₐ[ℂ] ℂ where
  toFun f := lsum f u₀
  map_one' := by simpa using lsum_single 0 1 u₀
  map_mul' f g := (hasSum_mul_laurent (mem_puncturedDisc.1 h).1 (f.2 u₀ h) (g.2 u₀ h)).tsum_eq
  map_zero' := by simp [lsum]
  map_add' f g := by
    simpa [lsum, add_mul] using (f.2 u₀ h).tsum_add (g.2 u₀ h)
  commutes' c := lsum_algebraMap c u₀
@[simp] theorem evalAt_apply {ε : ℝ} {u₀ : ℂ} (h : u₀ ∈ puncturedDisc ε) (f : puncturedRing ε) :
    evalAt ε u₀ h f = lsum f u₀ := rfl
theorem lsum_eq {ε : ℝ} {f : ℂ⸨X⸩} (hf : f ∈ puncturedRing ε) {v : ℂ} (hv : v ∈ puncturedDisc ε) :
    lsum f v = v ^ f.order * sum f.powerSeriesPart v := by
  have := hasSum_single_mul_coe (mem_puncturedDisc.1 hv).1 f.order
    (mem_puncturedRing_iff_powerSeriesPart.1 hf v (mem_puncturedDisc.1 hv).2)
  rw [f.single_order_mul_powerSeriesPart] at this
  exact this.tsum_eq
theorem analyticOnNhd_lsum {ε : ℝ} {f : ℂ⸨X⸩} (hf : f ∈ puncturedRing ε) :
    AnalyticOnNhd ℂ (lsum f) (puncturedDisc ε) := by
  intro v hv
  have h1 : AnalyticAt ℂ (fun w : ℂ => w ^ f.order * sum f.powerSeriesPart w) v :=
    (analyticAt_id.fun_zpow (mem_puncturedDisc.1 hv).1).mul
      ((mem_discSeries.1 (mem_puncturedRing_iff_powerSeriesPart.1 hf)).analyticOnNhd v hv.1)
  refine h1.congr ?_
  filter_upwards [(isOpen_puncturedDisc ε).mem_nhds hv] with w hw
  exact (lsum_eq hf hw).symm
theorem meromorphicAt_lsum {ε : ℝ} (hε : 0 < ε) {f : ℂ⸨X⸩} (hf : f ∈ puncturedRing ε) :
    MeromorphicAt (lsum f) 0 := by
  refine MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.2 ⟨f.order, sum f.powerSeriesPart,
    analyticAt_sum (discSeries_le_convSeries hε (mem_puncturedRing_iff_powerSeriesPart.1 hf)), ?_⟩
  filter_upwards [puncturedDisc_mem_nhds hε] with w hw
  simpa using lsum_eq hf hw
theorem exists_lsum_eq {ε : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (puncturedDisc ε))
    (h0 : MeromorphicAt F 0) : ∃ f ∈ puncturedRing ε, ∀ v ∈ puncturedDisc ε, lsum f v = F v := by
  obtain ⟨n, hn⟩ := h0
  have hG : DifferentiableOn ℂ (fun z : ℂ => (z - 0) ^ n • F z) (ball 0 ε) := by
    intro v hv
    rcases eq_or_ne v 0 with rfl | hv0
    · exact hn.differentiableAt.differentiableWithinAt
    · have := hF.differentiableAt ((isOpen_puncturedDisc ε).mem_nhds ⟨hv, hv0⟩)
      refine DifferentiableAt.differentiableWithinAt ?_
      fun_prop
  refine ⟨_, (single_mul_coe_mem_puncturedRing (-n : ℤ)).2 (taylor_mem_discSeries hG),
    fun v hv => ?_⟩
  obtain ⟨hv0, hv⟩ := mem_puncturedDisc.1 hv
  rw [lsum, (hasSum_single_mul_coe hv0 _ (taylor_mem_discSeries hG v hv)).tsum_eq,
    sum_taylor hG hv]
  simp [hv0]
theorem eq_zero_of_frequently_lsum_eq_zero {ε : ℝ} (hε : 0 < ε) {f : ℂ⸨X⸩}
    (hf : f ∈ puncturedRing ε) (h : ∃ᶠ v in 𝓝[≠] (0 : ℂ), lsum f v = 0) : f = 0 := by
  rw [← LaurentSeries.powerSeriesPart_eq_zero]
  refine eq_zero_of_frequently_sum_eq_zero
    (discSeries_le_convSeries hε (mem_puncturedRing_iff_powerSeriesPart.1 hf)) ?_
  refine (h.and_eventually (puncturedDisc_mem_nhds hε)).mono fun v hv => ?_
  have := hv.1
  rw [lsum_eq hf hv.2] at this
  exact (mul_eq_zero.1 this).resolve_left (zpow_ne_zero _ (mem_puncturedDisc.1 hv.2).1)
def meromorphicFunctions (ε : ℝ) : Subalgebra ℂ (puncturedDisc ε → ℂ) where
  carrier := {φ | ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (puncturedDisc ε) ∧ MeromorphicAt F 0 ∧
    ∀ v : puncturedDisc ε, φ v = F v}
  mul_mem' := by
    rintro _ _ ⟨F, hF, hF0, h⟩ ⟨G, hG, hG0, h'⟩
    exact ⟨F * G, hF.mul hG, hF0.mul hG0, fun v => by simp [h, h']⟩
  add_mem' := by
    rintro _ _ ⟨F, hF, hF0, h⟩ ⟨G, hG, hG0, h'⟩
    exact ⟨F + G, hF.add hG, hF0.add hG0, fun v => by simp [h, h']⟩
  algebraMap_mem' c := ⟨fun _ => c, differentiableOn_const c, MeromorphicAt.const c 0, fun _ => rfl⟩
def toFunction (ε : ℝ) : puncturedRing ε →ₐ[ℂ] (puncturedDisc ε → ℂ) :=
  AlgHom.pi fun v => evalAt ε v v.2
@[simp] theorem toFunction_apply {ε : ℝ} (f : puncturedRing ε) (v : puncturedDisc ε) :
    toFunction ε f v = lsum f v := rfl
theorem toFunction_injective {ε : ℝ} (hε : 0 < ε) : Function.Injective (toFunction ε) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => Subtype.ext ?_
  refine eq_zero_of_frequently_lsum_eq_zero hε f.2 (Eventually.frequently ?_)
  filter_upwards [puncturedDisc_mem_nhds hε] with v hv
  exact congrFun hf ⟨v, hv⟩
theorem range_toFunction {ε : ℝ} (hε : 0 < ε) :
    (toFunction ε).range = meromorphicFunctions ε := by
  ext φ
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨lsum f, (analyticOnNhd_lsum f.2).differentiableOn, meromorphicAt_lsum hε f.2,
      fun _ => rfl⟩
  · rintro ⟨F, hF, hF0, h⟩
    obtain ⟨f, hf, hf'⟩ := exists_lsum_eq hF hF0
    exact ⟨⟨f, hf⟩, funext fun v => (hf' v v.2).trans (h v).symm⟩
def puncturedEquiv {ε : ℝ} (hε : 0 < ε) : puncturedRing ε ≃ₐ[ℂ] meromorphicFunctions ε :=
  (AlgEquiv.ofInjective _ (toFunction_injective hε)).trans
    (Subalgebra.equivOfEq _ _ (range_toFunction hε))
@[simp] theorem puncturedEquiv_apply {ε : ℝ} (hε : 0 < ε) (f : puncturedRing ε)
    (v : puncturedDisc ε) : (puncturedEquiv hε f : puncturedDisc ε → ℂ) v = lsum f v := rfl
instance (ε : ℝ) : Algebra (discSeries ε) (puncturedRing ε) :=
  (((HahnSeries.ofPowerSeries ℤ ℂ).comp (discSeries ε).val.toRingHom).codRestrict
    (puncturedRing ε) fun g => coe_mem_puncturedRing.2 g.2).toAlgebra
@[simp] theorem coe_algebraMap_discSeries {ε : ℝ} (g : discSeries ε) :
    (algebraMap (discSeries ε) (puncturedRing ε) g : ℂ⸨X⸩) = ((g : ℂ⟦X⟧) : ℂ⸨X⸩) := rfl
instance (ε : ℝ) : IsScalarTower ℂ (discSeries ε) (puncturedRing ε) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance (ε : ℝ) : IsLocalization.Away
    (⟨PowerSeries.X, X_mem_discSeries ε⟩ : discSeries ε) (puncturedRing ε) := by
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one ⟨_, single_mem_puncturedRing ε (-1) 1⟩ (Subtype.ext ?_)
    simp [HahnSeries.single_mul_single]
  · intro f
    obtain ⟨n, g, hg, h⟩ := mem_puncturedRing_iff_exists.1 f.2
    refine ⟨n, ⟨g, hg⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_algebraMap_discSeries, h]
    rw [← PowerSeries.coe_pow, HahnSeries.ofPowerSeries_X_pow, mul_right_comm,
      HahnSeries.single_mul_single]
    simp
  · intro a b h
    exact ⟨0, congrArg _ (Subtype.ext (HahnSeries.ofPowerSeries_injective
      (congrArg Subtype.val h)))⟩
def convLaurent : IntermediateField ℂ ℂ⸨X⸩ where
  carrier := {f | ∃ ε > 0, f ∈ puncturedRing ε}
  mul_mem' := by
    rintro f g ⟨ε, hε, hf⟩ ⟨δ, hδ, hg⟩
    exact ⟨min ε δ, lt_min hε hδ, mul_mem
      (puncturedRing_anti (min_le_left ε δ) hf) (puncturedRing_anti (min_le_right ε δ) hg)⟩
  add_mem' := by
    rintro f g ⟨ε, hε, hf⟩ ⟨δ, hδ, hg⟩
    exact ⟨min ε δ, lt_min hε hδ, add_mem
      (puncturedRing_anti (min_le_left ε δ) hf) (puncturedRing_anti (min_le_right ε δ) hg)⟩
  algebraMap_mem' c := ⟨1, one_pos, (puncturedRing 1).algebraMap_mem c⟩
  inv_mem' := by
    rintro f ⟨ε, hε, hf⟩
    rcases eq_or_ne f 0 with rfl | h0
    · exact ⟨1, one_pos, by simp⟩
    let p : convSeries :=
      ⟨_, discSeries_le_convSeries hε (mem_puncturedRing_iff_powerSeriesPart.1 hf)⟩
    have hp : IsUnit p := isUnit_iff.2 <| by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simpa [p] using h0
    obtain ⟨q, hq⟩ := hp.exists_right_inv
    obtain ⟨δ, hδ, hq'⟩ := mem_convSeries.1 q.2
    have hq1 : (f.powerSeriesPart : ℂ⸨X⸩) * ((q : ℂ⟦X⟧) : ℂ⸨X⸩) = 1 := by
      rw [← PowerSeries.coe_mul, ← PowerSeries.coe_one]
      exact congrArg (fun x : convSeries => ((x : ℂ⟦X⟧) : ℂ⸨X⸩)) hq
    have : f⁻¹ = HahnSeries.single (-f.order) (1 : ℂ) * ((q : ℂ⟦X⟧) : ℂ⸨X⸩) := by
      refine inv_eq_of_mul_eq_one_right ?_
      nth_rw 1 [← f.single_order_mul_powerSeriesPart]
      rw [mul_mul_mul_comm, hq1, HahnSeries.single_mul_single]
      simp
    exact ⟨δ, hδ, this ▸ (single_mul_coe_mem_puncturedRing _).2 hq'⟩
theorem mem_convLaurent {f : ℂ⸨X⸩} : f ∈ convLaurent ↔ ∃ ε > 0, f ∈ puncturedRing ε := Iff.rfl
theorem puncturedRing_le_convLaurent {ε : ℝ} (hε : 0 < ε) :
    puncturedRing ε ≤ convLaurent.toSubalgebra := fun _ hf => ⟨ε, hε, hf⟩
def puncturedIncl {ε : ℝ} (hε : 0 < ε) : puncturedRing ε →ₐ[ℂ] convLaurent :=
  Subalgebra.inclusion (puncturedRing_le_convLaurent hε)
@[simp] theorem coe_puncturedIncl {ε : ℝ} (hε : 0 < ε) (f : puncturedRing ε) :
    (puncturedIncl hε f : ℂ⸨X⸩) = f := rfl
theorem mem_convLaurent_iff_eventually {f : ℂ⸨X⸩} :
    f ∈ convLaurent ↔ ∀ᶠ v in 𝓝[≠] (0 : ℂ), Summable fun n : ℤ => f.coeff n * v ^ n :=
  eventually_iff_exists_puncturedDisc.symm
theorem coe_mem_convLaurent {g : ℂ⟦X⟧} : (g : ℂ⸨X⸩) ∈ convLaurent ↔ g ∈ convSeries := by
  simp only [mem_convLaurent, mem_convSeries, coe_mem_puncturedRing]
theorem mem_convLaurent_iff_exists {f : ℂ⸨X⸩} :
    f ∈ convLaurent ↔ ∃ n : ℕ, ∃ g ∈ convSeries,
      f = HahnSeries.single (-n : ℤ) (1 : ℂ) * (g : ℂ⸨X⸩) := by
  constructor
  · rintro ⟨ε, hε, hf⟩
    obtain ⟨n, g, hg, h⟩ := mem_puncturedRing_iff_exists.1 hf
    exact ⟨n, g, discSeries_le_convSeries hε hg, h⟩
  · rintro ⟨n, g, hg, rfl⟩
    obtain ⟨ε, hε, hg⟩ := mem_convSeries.1 hg
    exact ⟨ε, hε, (single_mul_coe_mem_puncturedRing _).2 hg⟩
instance : Algebra convSeries convLaurent :=
  (((HahnSeries.ofPowerSeries ℤ ℂ).comp convSeries.val.toRingHom).codRestrict
    convLaurent fun g => coe_mem_convLaurent.2 g.2).toAlgebra
@[simp] theorem coe_algebraMap_convSeries (g : convSeries) :
    (algebraMap convSeries convLaurent g : ℂ⸨X⸩) = ((g : ℂ⟦X⟧) : ℂ⸨X⸩) := rfl
instance : IsScalarTower ℂ convSeries convLaurent :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance : IsScalarTower convSeries convLaurent ℂ⸨X⸩ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
theorem algebraMap_convSeries_injective :
    Function.Injective (algebraMap convSeries convLaurent) := fun _ _ h =>
  Subtype.ext (HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h))
instance : IsLocalization.Away u convLaurent := by
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · refine IsUnit.mk0 _ ?_
    rw [map_ne_zero_iff _ algebraMap_convSeries_injective]
    exact irreducible_u.ne_zero
  · intro f
    obtain ⟨n, g, hg, h⟩ := mem_convLaurent_iff_exists.1 f.2
    refine ⟨n, ⟨g, hg⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_algebraMap_convSeries, h, coe_u]
    rw [← PowerSeries.coe_pow, HahnSeries.ofPowerSeries_X_pow, mul_right_comm,
      HahnSeries.single_mul_single]
    simp
  · intro a b h
    exact ⟨0, congrArg _ (algebraMap_convSeries_injective h)⟩
instance : IsFractionRing convSeries convLaurent :=
  IsLocalization.of_le (Submonoid.powers u) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors irreducible_u.ne_zero) fun _ hf =>
    isUnit_of_mem_nonZeroDivisors <| map_mem_nonZeroDivisors _ algebraMap_convSeries_injective hf
theorem eventually_hasSum_lsum (f : convLaurent) :
    ∀ᶠ v in 𝓝[≠] (0 : ℂ), HasSum (fun n : ℤ => (f : ℂ⸨X⸩).coeff n * v ^ n) (lsum f v) :=
  (mem_convLaurent_iff_eventually.1 f.2).mono fun _ h => h.hasSum
def lgerm : convLaurent →+* Germ (𝓝[≠] (0 : ℂ)) ℂ where
  toFun f := (lsum f : Germ (𝓝[≠] (0 : ℂ)) ℂ)
  map_one' := by
    rw [← Germ.coe_one, Germ.coe_eq]
    exact Eventually.of_forall fun v => by simpa using lsum_single 0 1 v
  map_mul' f g := by
    rw [← Germ.coe_mul, Germ.coe_eq]
    filter_upwards [eventually_hasSum_lsum f, eventually_hasSum_lsum g, self_mem_nhdsWithin]
      with v hf hg hv
    exact (hasSum_mul_laurent hv hf.summable hg.summable).tsum_eq
  map_zero' := by
    rw [← Germ.coe_zero, Germ.coe_eq]
    exact Eventually.of_forall fun v => by simp [lsum]
  map_add' f g := by
    rw [← Germ.coe_add, Germ.coe_eq]
    filter_upwards [eventually_hasSum_lsum f, eventually_hasSum_lsum g] with v hf hg
    simpa [lsum, add_mul] using hf.summable.tsum_add hg.summable
section Expand
variable (k : ℕ) (hk : k ≠ 0)
def expandLaurent : ℂ⸨X⸩ →ₐ[ℂ] ℂ⸨X⸩ where
  __ := HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (k : ℤ))
    (mul_right_injective₀ (Int.natCast_ne_zero.2 hk))
    fun _ _ => mul_le_mul_iff_right₀ (Int.natCast_pos.2 (Nat.pos_of_ne_zero hk))
  commutes' c := by
    rw [LaurentSeries.algebraMap_apply]
    exact HahnSeries.embDomainRingHom_C
@[simp] theorem coeff_expandLaurent_mul (f : ℂ⸨X⸩) (n : ℤ) :
    (expandLaurent k hk f).coeff (k * n) = f.coeff n :=
  HahnSeries.embDomain_coeff
theorem coeff_expandLaurent_of_not_dvd (f : ℂ⸨X⸩) {n : ℤ} (h : ¬ (k : ℤ) ∣ n) :
    (expandLaurent k hk f).coeff n = 0 :=
  HahnSeries.embDomain_of_notMem_range fun ⟨m, hm⟩ => h ⟨m, hm.symm⟩
@[simp] theorem expandLaurent_coe (g : ℂ⟦X⟧) :
    expandLaurent k hk (g : ℂ⸨X⸩) = (PowerSeries.expand k hk g : ℂ⸨X⸩) := by
  ext n
  by_cases h : (k : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeff_expandLaurent_mul]
    have hk' : (0 : ℤ) < k := Int.natCast_pos.2 (Nat.pos_of_ne_zero hk)
    rcases lt_or_ge m 0 with hm | hm
    · simp [PowerSeries.coeff_coe, hm, mul_neg_of_pos_of_neg hk' hm]
    · lift m to ℕ using hm
      rw [← Nat.cast_mul, LaurentSeries.coeff_coe_powerSeries, LaurentSeries.coeff_coe_powerSeries,
        PowerSeries.coeff_expand_mul]
  · rw [coeff_expandLaurent_of_not_dvd k hk _ h, PowerSeries.coeff_coe]
    split_ifs
    · rfl
    · exact (PowerSeries.coeff_expand_of_not_dvd k hk g fun h' => h (Int.natCast_dvd.2 h')).symm
theorem hasSum_expandLaurent_iff {f : ℂ⸨X⸩} {v a : ℂ} :
    HasSum (fun n : ℤ => (expandLaurent k hk f).coeff n * v ^ n) a ↔
      HasSum (fun n : ℤ => f.coeff n * (v ^ k) ^ n) a := by
  rw [← (mul_right_injective₀ (Int.natCast_ne_zero.2 hk)).hasSum_iff]
  · simp [Function.comp_def, zpow_mul]
  · intro n hn
    rw [coeff_expandLaurent_of_not_dvd k hk f fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩, zero_mul]
@[simp] theorem lsum_expandLaurent (f : ℂ⸨X⸩) (v : ℂ) :
    lsum (expandLaurent k hk f) v = lsum f (v ^ k) := by
  by_cases h : Summable fun n : ℤ => f.coeff n * (v ^ k) ^ n
  · exact ((hasSum_expandLaurent_iff k hk).2 h.hasSum).tsum_eq
  · rw [lsum, lsum, tsum_eq_zero_of_not_summable h, tsum_eq_zero_of_not_summable]
    exact fun h' => h ((hasSum_expandLaurent_iff k hk).1 h'.hasSum).summable
@[simp] theorem sum_expand (g : ℂ⟦X⟧) (v : ℂ) :
    sum (PowerSeries.expand k hk g) v = sum g (v ^ k) := by
  rw [← lsum_coe, ← lsum_coe, ← expandLaurent_coe, lsum_expandLaurent]
include hk in

theorem image_pow_puncturedDisc {ε : ℝ} (hε : 0 ≤ ε) :
    (fun v : ℂ => v ^ k) '' puncturedDisc ε = puncturedDisc (ε ^ k) := by
  have key : ∀ v : ℂ, v ^ k ∈ puncturedDisc (ε ^ k) ↔ v ∈ puncturedDisc ε := fun v => by
    simp only [mem_puncturedDisc, norm_pow, pow_lt_pow_iff_left₀ (norm_nonneg v) hε hk,
      pow_ne_zero_iff hk]
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (key v).2 hv
  · intro hw
    obtain ⟨v, rfl⟩ := IsAlgClosed.exists_pow_nat_eq w (Nat.pos_of_ne_zero hk)
    exact ⟨v, (key v).1 hw, rfl⟩
theorem expandLaurent_mem_puncturedRing {ε : ℝ} (hε : 0 ≤ ε) {f : ℂ⸨X⸩} :
    expandLaurent k hk f ∈ puncturedRing ε ↔ f ∈ puncturedRing (ε ^ k) := by
  rw [mem_puncturedRing, mem_puncturedRing, ← image_pow_puncturedDisc k hk hε,
    Set.forall_mem_image]
  exact forall₂_congr fun _ _ => exists_congr fun _ => hasSum_expandLaurent_iff k hk
theorem expandLaurent_mem_convLaurent {f : ℂ⸨X⸩} :
    expandLaurent k hk f ∈ convLaurent ↔ f ∈ convLaurent := by
  constructor
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε ^ k, pow_pos hε k, (expandLaurent_mem_puncturedRing k hk hε.le).1 h⟩
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε ^ (k : ℝ)⁻¹, Real.rpow_pos_of_pos hε _,
      (expandLaurent_mem_puncturedRing k hk (Real.rpow_pos_of_pos hε _).le).2 ?_⟩
    rwa [Real.rpow_inv_natCast_pow hε.le hk]
theorem expand_mem_convSeries {g : ℂ⟦X⟧} :
    PowerSeries.expand k hk g ∈ convSeries ↔ g ∈ convSeries := by
  rw [← coe_mem_convLaurent, ← coe_mem_convLaurent, ← expandLaurent_coe,
    expandLaurent_mem_convLaurent]
def expandConv : convSeries →ₐ[ℂ] convSeries :=
  ((PowerSeries.expand k hk).comp convSeries.val).codRestrict _
    fun g => (expand_mem_convSeries k hk).2 g.2
def expandConvLaurent : convLaurent →ₐ[ℂ] convLaurent :=
  ((expandLaurent k hk).comp convLaurent.val).codRestrict convLaurent.toSubalgebra
    fun f => (expandLaurent_mem_convLaurent k hk).2 f.2
end Expand
section Scheme
open CategoryTheory AlgebraicGeometry
end Scheme
example (ε : ℝ) (u₀ : ℂ) (h : u₀ ∈ puncturedDisc ε) :
    evalAt ε u₀ h ⟨HahnSeries.single (-1) 1, single_mem_puncturedRing ε _ _⟩ = u₀⁻¹ := by
  simp
example : IsUnit (1 + u) ∧ ¬ IsUnit u := by
  simp [isUnit_iff]
example : ∃ a : convSeries, a ^ 2 = 1 + u ∧ evalZero a = 1 := by
  obtain ⟨a, ha, ha'⟩ := exists_isRoot (Polynomial.X ^ 2 - Polynomial.C (1 + u)) 1
    (by simp) (by simp)
  exact ⟨a, by simpa [sub_eq_zero] using ha, ha'⟩
example (ε : ℝ) : ValuationRing convSeries ∧ CharZero convLaurent ∧ IsDomain (puncturedRing ε) :=
  ⟨inferInstance, inferInstance, inferInstance⟩
end GlobalTheory.Conv


