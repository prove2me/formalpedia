-- Prove2me | Definitions.Def_EhrhartVolumeInequality
-- name    : EhrhartVolumeInequality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-19T10:54:31.198+00:00
-- url     : https://prove2.me/theorems/cfc026c4-fd7e-4bc8-89a9-8f2bc31253fa
-- title:
--   EhrhartVolumeInequality
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | EhrhartVolumeInequality | external Lean 4.33.1 validation; bundle SHA256 7150ea60aef8441515028279454832b05d0f964f3966505d147b2c1d8afe9763

import Mathlib
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance _p2m_local_instance_3610026555_5 {n : ℕ} : CoeFun (ContDiffBump (0 : Fin n → ℝ)) (fun _ => (Fin n → ℝ) → ℝ) :=
  ⟨ContDiffBump.toFun⟩
noncomputable section
namespace Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
abbrev Space (n : ℕ) := Fin n → ℝ
def integerPoint (n : ℕ) (z : Fin n → ℤ) : Space n :=
  fun i => (z i : ℝ)
def standardSimplex (n : ℕ) : Set (Space n) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1}
def simplexDilation (n : ℕ) (x : Space n) : Space n :=
  fun i => ((n : ℝ) + 1) * x i - 1
def centeredSimplex (n : ℕ) : Set (Space n) :=
  simplexDilation n '' standardSimplex n
def normalizedVolume {n : ℕ} (K : Set (Space n)) : ℝ :=
  ((volume : Measure (Space n)) K).toReal
def barycenter {n : ℕ} (K : Set (Space n)) : Space n :=
  (normalizedVolume K)⁻¹ • ∫ x in K, x ∂(volume : Measure (Space n))
def interiorLatticePoints {n : ℕ} (K : Set (Space n)) : Set (Fin n → ℤ) :=
  {z | integerPoint n z ∈ interior K}
structure CenteredBody (n : ℕ) where
  carrier : Set (Space n)
  convex : Convex ℝ carrier
  compact : IsCompact carrier
  fullDimensional : (interior carrier).Nonempty
  centered : barycenter carrier = 0
  uniqueInteriorLatticePoint : interiorLatticePoints carrier = {0}
theorem CenteredBody.volume_pos {n : ℕ} (K : CenteredBody n) :
    0 < normalizedVolume K.carrier := by
  unfold normalizedVolume
  exact ENNReal.toReal_pos
    (MeasureTheory.Measure.measure_pos_of_nonempty_interior
      (volume : Measure (Space n)) K.fullDimensional).ne'
    K.compact.measure_ne_top
def sharpConstant (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ n / (n.factorial : ℝ)
namespace BodyMeasure
open Set MeasureTheory
open scoped ENNReal
theorem volume_interior_eq_volume {n : ℕ} (K : CenteredBody n) :
    (volume : Measure (Space n)) (interior K.carrier) =
      (volume : Measure (Space n)) K.carrier := by
  exact measure_interior_of_null_frontier
    (K.convex.addHaar_frontier (volume : Measure (Space n)))
end BodyMeasure
namespace LatticeAsymptotics
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Pointwise Topology
def scaledIntegerLattice (n k : ℕ) : Set (Space n) :=
  (k : ℝ)⁻¹ •
    (↑(Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (Fin n)))) : Set (Space n))
def monomialIndex {n : ℕ}
    (K : CenteredBody n) (k : ℕ) : Set (Space n) :=
  interior K.carrier ∩ scaledIntegerLattice n k
theorem mem_scaledIntegerLattice_iff {n k : ℕ} (hk : 0 < k)
    (x : Space n) :
    x ∈ scaledIntegerLattice n k ↔
      ∀ i, (k : ℝ) * x i ∈ Set.range (algebraMap ℤ ℝ) := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  rw [scaledIntegerLattice, ← Submodule.coe_pointwise_smul]
  exact BoxIntegral.unitPartition.mem_smul_span_iff
    (n := k) (v := x)
theorem mem_monomialIndex_iff {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (x : Space n) :
    x ∈ monomialIndex K k ↔
      x ∈ interior K.carrier ∧
        ∀ i, (k : ℝ) * x i ∈ Set.range (algebraMap ℤ ℝ) := by
  rw [monomialIndex, Set.mem_inter_iff,
    mem_scaledIntegerLattice_iff hk]
theorem zero_mem_interior {n : ℕ}
    (K : CenteredBody n) :
    (0 : Space n) ∈ interior K.carrier := by
  have hz :
      (0 : Fin n → ℤ) ∈ interiorLatticePoints K.carrier := by
    rw [K.uniqueInteriorLatticePoint]
    exact Set.mem_singleton 0
  change integerPoint n (0 : Fin n → ℤ) ∈
    interior K.carrier at hz
  have hzero : integerPoint n (0 : Fin n → ℤ) =
      (0 : Space n) := by
    funext i
    simp [integerPoint]
  rwa [hzero] at hz
theorem mem_monomialIndex_one_iff {n : ℕ}
    (K : CenteredBody n) (x : Space n) :
    x ∈ monomialIndex K 1 ↔ x = 0 := by
  classical
  constructor
  · intro hx
    obtain ⟨hxinterior, hxinteger⟩ :=
      (mem_monomialIndex_iff K (by decide) x).mp hx
    have hcoordinates : ∀ i, ∃ m : ℤ, (m : ℝ) = x i := by
      intro i
      obtain ⟨m, hm⟩ := hxinteger i
      refine ⟨m, ?_⟩
      simpa using hm
    choose z hz using hcoordinates
    have hreal : integerPoint n z = x := by
      funext i
      exact hz i
    have hmem : z ∈ interiorLatticePoints K.carrier := by
      change integerPoint n z ∈ interior K.carrier
      rwa [hreal]
    have hzero : z = 0 := by
      have hzsingleton : z ∈ ({0} : Set (Fin n → ℤ)) := by
        rw [← K.uniqueInteriorLatticePoint]
        exact hmem
      simpa using hzsingleton
    rw [← hreal, hzero]
    funext i
    simp [integerPoint]
  · rintro rfl
    refine (mem_monomialIndex_iff K (by decide) 0).mpr
      ⟨zero_mem_interior K, ?_⟩
    intro i
    refine ⟨0, ?_⟩
    simp
theorem monomial_count_div_pow_tendsto_volume {n : ℕ}
    (K : CenteredBody n) :
    Tendsto
      (fun k : ℕ =>
        (Nat.card (monomialIndex K k) : ℝ) / (k : ℝ) ^ n)
      atTop (𝓝 (normalizedVolume K.carrier)) := by
  have hbounded : Bornology.IsBounded (interior K.carrier) :=
    K.compact.isBounded.subset interior_subset
  have hmeas : MeasurableSet (interior K.carrier) :=
    isOpen_interior.measurableSet
  have hfront :
      (volume : Measure (Space n))
        (frontier (interior K.carrier)) = 0 :=
    K.convex.interior.addHaar_frontier
      (volume : Measure (Space n))
  have hvolume :
      (volume : Measure (Space n)).real
        (interior K.carrier) =
      normalizedVolume K.carrier := by
    unfold Measure.real normalizedVolume
    rw [BodyMeasure.volume_interior_eq_volume K]
  simpa [monomialIndex, scaledIntegerLattice,
      Fintype.card_fin, hvolume] using
    (tendsto_card_div_pow_atTop_volume
      (s := interior K.carrier) hbounded hmeas hfront)
end LatticeAsymptotics
namespace SupportFunction
open Set
open scoped BigOperators
def pairing {n : ℕ} (u x : Space n) : ℝ :=
  ∑ i, u i * x i
def supportFunction {n : ℕ}
    (K : Set (Space n)) (x : Space n) : ℝ :=
  sSup ((fun y => pairing y x) '' K)
theorem continuous_pairing_left {n : ℕ} (x : Space n) :
    Continuous (fun u : Space n => pairing u x) := by
  unfold pairing
  exact continuous_finsetSum Finset.univ
    (fun i _ => (continuous_apply i).mul continuous_const)
theorem continuous_pairing_right {n : ℕ} (u : Space n) :
    Continuous (fun x : Space n => pairing u x) := by
  unfold pairing
  exact continuous_finsetSum Finset.univ
    (fun i _ => continuous_const.mul (continuous_apply i))
theorem pairing_le_supportFunction {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) {u : Space n}
    (hu : u ∈ K) (x : Space n) :
    pairing u x ≤ supportFunction K x := by
  unfold supportFunction
  exact le_csSup
    (hcompact.bddAbove_image (continuous_pairing_left x).continuousOn)
    (Set.mem_image_of_mem _ hu)
theorem supportFunction_le {n : ℕ}
    {K : Set (Space n)} (hnonempty : K.Nonempty)
    (x : Space n) {c : ℝ}
    (hbound : ∀ y ∈ K, pairing y x ≤ c) :
    supportFunction K x ≤ c := by
  unfold supportFunction
  apply csSup_le (hnonempty.image _)
  rintro _ ⟨y, hy, rfl⟩
  exact hbound y hy
theorem supportFunction_attained {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    (hnonempty : K.Nonempty) (x : Space n) :
    ∃ y ∈ K, supportFunction K x = pairing y x := by
  obtain ⟨y, hy, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty
      (continuous_pairing_left x).continuousOn
  refine ⟨y, hy, le_antisymm ?_ ?_⟩
  · exact supportFunction_le hnonempty x (fun z hz => hmax hz)
  · exact pairing_le_supportFunction hcompact hy x
def signVector {n : ℕ} (x : Space n) : Space n :=
  fun i => if 0 ≤ x i then 1 else -1
theorem norm_signVector_le_one {n : ℕ} (x : Space n) :
    ‖signVector x‖ ≤ (1 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  rw [Real.norm_eq_abs]
  dsimp [signVector]
  split_ifs <;> norm_num
theorem norm_le_sum_abs {n : ℕ} (x : Space n) :
    ‖x‖ ≤ ∑ i, |x i| := by
  have hnonneg : 0 ≤ ∑ i, |x i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (x i))
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum
    (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
theorem pairing_signVector {n : ℕ} (x : Space n) :
    pairing (signVector x) x = ∑ i, |x i| := by
  unfold pairing signVector
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 ≤ x i
  · simp [hi, abs_of_nonneg hi]
  · have hnegative : x i < 0 := lt_of_not_ge hi
    simp [hi, abs_of_neg hnegative]
theorem pairing_add_left {n : ℕ}
    (u v x : Space n) :
    pairing (u + v) x = pairing u x + pairing v x := by
  simp [pairing, add_mul, Finset.sum_add_distrib]
theorem pairing_smul_left {n : ℕ}
    (a : ℝ) (u x : Space n) :
    pairing (a • u) x = a * pairing u x := by
  simp [pairing, Finset.mul_sum, mul_assoc]
theorem interior_gap {n : ℕ} {K : Set (Space n)}
    (hcompact : IsCompact K) {u : Space n}
    (hu : u ∈ interior K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Space n,
      δ * ‖x‖ ≤ supportFunction K x - pairing u x := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) u hu
  have hhalf : 0 < r / 2 := half_pos hr
  refine ⟨r / 2, hhalf, ?_⟩
  intro x
  have hscaled_norm : ‖(r / 2) • signVector x‖ ≤ r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf]
    exact mul_le_of_le_one_right hhalf.le (norm_signVector_le_one x)
  have hmem_ball : u + (r / 2) • signVector x ∈ Metric.ball u r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖u + (r / 2) • signVector x - u‖ ≤ r / 2 := by
      simpa using hscaled_norm
    exact lt_of_le_of_lt hnorm (half_lt_self hr)
  have hmem : u + (r / 2) • signVector x ∈ K :=
    interior_subset (hball hmem_ball)
  have hsupport := pairing_le_supportFunction hcompact hmem x
  rw [pairing_add_left, pairing_smul_left, pairing_signVector] at hsupport
  have hnorm := norm_le_sum_abs x
  have hscaled := mul_le_mul_of_nonneg_left hnorm hhalf.le
  linarith
end SupportFunction
namespace MonomialIntegrability
open Set MeasureTheory
open scoped BigOperators
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a * |x|))
      (volume : Measure ℝ) := by
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)),
    integrableOn_union]
  constructor
  · have hpositive : IntegrableOn
        (fun x : ℝ => Real.exp (-a * x)) (Ioi (-(0 : ℝ)))
        (volume : Measure ℝ) := by
      simpa only [neg_zero] using exp_neg_integrableOn_Ioi (0 : ℝ) ha
    have h : IntegrableOn
        (fun x : ℝ => Real.exp (-a * (-x))) (Iio 0)
        (volume : Measure ℝ) :=
      hpositive.comp_neg_Iio (c := (0 : ℝ))
    refine h.congr_fun (fun x hx => ?_) measurableSet_Iio
    rw [abs_of_neg (Set.mem_Iio.mp hx)]
  · have h : IntegrableOn (fun x : ℝ => Real.exp (-a * x))
        (Ici 0) (volume : Measure ℝ) :=
      (integrableOn_Ici_iff_integrableOn_Ioi
        (f := fun x : ℝ => Real.exp (-a * x))
        (b := (0 : ℝ))).mpr (exp_neg_integrableOn_Ioi 0 ha)
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ici
    rw [abs_of_nonneg (Set.mem_Ici.mp hx)]
theorem sum_abs_le_dimension_mul_norm {n : ℕ} (x : Space n) :
    (∑ i, |x i|) ≤ (n : ℝ) * ‖x‖ := by
  calc
    (∑ i, |x i|) ≤ ∑ _i : Fin n, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    _ = (n : ℝ) * ‖x‖ := by simp [nsmul_eq_mul]
theorem integrable_exp_neg_mul_sum_abs (n : ℕ) {a : ℝ}
    (ha : 0 < a) :
    Integrable (fun x : Space n =>
      Real.exp (-a * ∑ i, |x i|))
      (volume : Measure (Space n)) := by
  have hprod :
      Integrable (fun x : Space n =>
        ∏ i, Real.exp (-a * |x i|))
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_abs ha)
  rw [volume_pi]
  have hfun :
      (fun x : Space n => Real.exp (-a * ∑ i, |x i|)) =
        (fun x : Space n => ∏ i, Real.exp (-a * |x i|)) := by
    funext x
    rw [← Real.exp_sum, ← Finset.mul_sum]
  rw [hfun]
  exact hprod
theorem integrable_exp_neg_mul_norm {n : ℕ} (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Space n => Real.exp (-a * ‖x‖))
      (volume : Measure (Space n)) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb : 0 < a / (n : ℝ) := div_pos ha hnreal
  refine (integrable_exp_neg_mul_sum_abs n hb).mono'
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_norm)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hsum := sum_abs_le_dimension_mul_norm x
  have hscaled :
      (a / (n : ℝ)) * (∑ i, |x i|) ≤ a * ‖x‖ := by
    calc
      (a / (n : ℝ)) * (∑ i, |x i|) ≤
          (a / (n : ℝ)) * ((n : ℝ) * ‖x‖) :=
        mul_le_mul_of_nonneg_left hsum hb.le
      _ = a * ‖x‖ := by
        field_simp
  linarith
def monomialWeight {n : ℕ} (k : ℝ) (u : Space n)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  Real.exp (k * (SupportFunction.pairing u x - φ x))
def monomialIntegral {n : ℕ} (k : ℝ) (u : Space n)
    (φ : Space n → ℝ) : ℝ :=
  ∫ x : Space n, monomialWeight k u φ x
    ∂(volume : Measure (Space n))
theorem continuous_monomialWeight {n : ℕ} (k : ℝ)
    (u : Space n) {φ : Space n → ℝ}
    (hφ : Continuous φ) :
    Continuous (monomialWeight k u φ) := by
  unfold monomialWeight
  exact Real.continuous_exp.comp
    (continuous_const.mul
      ((SupportFunction.continuous_pairing_right u).sub hφ))
theorem interior_sum_abs_gap {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Space n,
      δ * (∑ i, |x i|) ≤
        SupportFunction.supportFunction K x -
          SupportFunction.pairing u x := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) u hu
  have hhalf : 0 < r / 2 := half_pos hr
  refine ⟨r / 2, hhalf, fun x => ?_⟩
  have hscaled :
      ‖(r / 2) • SupportFunction.signVector x‖ ≤ r / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hhalf]
    exact mul_le_of_le_one_right hhalf.le
      (SupportFunction.norm_signVector_le_one x)
  have hmem_ball :
      u + (r / 2) • SupportFunction.signVector x ∈
        Metric.ball u r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm :
        ‖u + (r / 2) • SupportFunction.signVector x - u‖ ≤
          r / 2 := by
      simpa using hscaled
    exact lt_of_le_of_lt hnorm (half_lt_self hr)
  have hmem :
      u + (r / 2) • SupportFunction.signVector x ∈ K :=
    interior_subset (hball hmem_ball)
  have hsupport := SupportFunction.pairing_le_supportFunction
    hcompact hmem x
  rw [SupportFunction.pairing_add_left,
    SupportFunction.pairing_smul_left,
    SupportFunction.pairing_signVector] at hsupport
  linarith
theorem integrable_monomialWeight_of_support_le {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hpotential : ∀ x : Space n,
      SupportFunction.supportFunction K x ≤ φ x + C)
    {k : ℝ} (hk : 0 < k) :
    Integrable (monomialWeight k u φ)
      (volume : Measure (Space n)) := by
  obtain ⟨δ, hδ, hgap⟩ := interior_sum_abs_gap hcompact hu
  have hdecay := integrable_exp_neg_mul_sum_abs n (mul_pos hk hδ)
  have hmajorant := hdecay.const_mul (Real.exp (k * C))
  refine hmajorant.mono'
    (continuous_monomialWeight k u hφ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  unfold monomialWeight
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcoercive :
      SupportFunction.pairing u x - φ x ≤
        C - δ * ∑ i, |x i| := by
    have hsupport := hpotential x
    have hinterior := hgap x
    linarith
  calc
    k * (SupportFunction.pairing u x - φ x) ≤
        k * (C - δ * ∑ i, |x i|) :=
      mul_le_mul_of_nonneg_left hcoercive hk.le
    _ = k * C + -(k * δ) * ∑ i, |x i| := by ring
theorem integrable_monomialWeight_of_bounded_support {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C)
    {k : ℝ} (hk : 0 < k) :
    Integrable (monomialWeight k u φ)
      (volume : Measure (Space n)) := by
  apply integrable_monomialWeight_of_support_le hcompact hu hφ
    (C := C) (k := k) (hk := hk)
  intro x
  have hlower := (abs_le.mp (hbounded x)).1
  linarith
theorem monomialIntegral_pos_of_bounded_support {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C)
    {k : ℝ} (hk : 0 < k) :
    0 < monomialIntegral k u φ := by
  unfold monomialIntegral monomialWeight
  exact MeasureTheory.integral_exp_pos
    (integrable_monomialWeight_of_bounded_support
      hcompact hu hφ hbounded hk)
theorem integrable_monomialWeight_of_centeredBody {n : ℕ}
    (K : CenteredBody n) {u : Space n}
    (hu : u ∈ interior K.carrier)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    {k : ℝ} (hk : 0 < k) :
    Integrable (monomialWeight k u φ)
      (volume : Measure (Space n)) :=
  integrable_monomialWeight_of_bounded_support
    K.compact hu hφ hbounded hk
end MonomialIntegrability
namespace MonomialDivergence
open Set MeasureTheory
open scoped BigOperators ENNReal
def dualVector {n : ℕ}
    (f : Space n →L[ℝ] ℝ) : Space n :=
  fun i => f (Pi.single i (1 : ℝ))
theorem dual_apply_eq_pairing {n : ℕ}
    (f : Space n →L[ℝ] ℝ) (x : Space n) :
    f x = SupportFunction.pairing x (dualVector f) := by
  classical
  have hexpansion :
      (∑ i : Fin n,
        x i • (Pi.single i (1 : ℝ) : Space n)) = x := by
    simpa [Pi.basisFun_apply, Pi.basisFun_repr] using
      (Pi.basisFun ℝ (Fin n)).sum_repr x
  calc
    f x = f (∑ i : Fin n,
      x i • (Pi.single i (1 : ℝ) : Space n)) :=
      congrArg f hexpansion.symm
    _ = SupportFunction.pairing x (dualVector f) := by
      simp [SupportFunction.pairing, dualVector,
        map_sum, map_smul, smul_eq_mul]
theorem pairing_add_right {n : ℕ}
    (a x y : Space n) :
    SupportFunction.pairing a (x + y) =
      SupportFunction.pairing a x +
        SupportFunction.pairing a y := by
  simp [SupportFunction.pairing, mul_add,
    Finset.sum_add_distrib]
theorem pairing_smul_right {n : ℕ} (c : ℝ)
    (a x : Space n) :
    SupportFunction.pairing a (c • x) =
      c * SupportFunction.pairing a x := by
  simp [SupportFunction.pairing, Finset.mul_sum,
    mul_left_comm]
theorem abs_pairing_le_sum_abs_mul_norm {n : ℕ}
    (a x : Space n) :
    |SupportFunction.pairing a x| ≤
      (∑ i, |a i|) * ‖x‖ := by
  unfold SupportFunction.pairing
  calc
    |∑ i, a i * x i| ≤ ∑ i, |a i * x i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |x i| := by simp_rw [abs_mul]
    _ ≤ ∑ i, |a i| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i)
        (abs_nonneg (a i))
    _ = (∑ i, |a i|) * ‖x‖ := by
      rw [Finset.sum_mul]
theorem abs_pairing_le_dimension_mul_norm {n : ℕ}
    (a x : Space n) :
    |SupportFunction.pairing a x| ≤
      ((n : ℝ) * ‖a‖) * ‖x‖ := by
  calc
    |SupportFunction.pairing a x| ≤
        (∑ i, |a i|) * ‖x‖ :=
      abs_pairing_le_sum_abs_mul_norm a x
    _ ≤ ((n : ℝ) * ‖a‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (MonomialIntegrability.sum_abs_le_dimension_mul_norm a)
        (norm_nonneg x)
def rayBall {n : ℕ} (v : Space n) (j : ℕ) :
    Set (Space n) :=
  Metric.ball ((j : ℝ) • v) (‖v‖ / 4)
def rayTube {n : ℕ} (v : Space n) :
    Set (Space n) :=
  ⋃ j : ℕ, rayBall v j
end MonomialDivergence
namespace BergmanMonomials
open Set MeasureTheory Filter
open scoped BigOperators Pointwise Topology
def bergmanDimension {n : ℕ}
    (K : CenteredBody n) (k : ℕ) : ℕ :=
  Nat.card (LatticeAsymptotics.monomialIndex K k)
def monomialNormSquared {n : ℕ} (k : ℕ)
    (u : Space n) (φ : Space n → ℝ) : ℝ :=
  MonomialIntegrability.monomialIntegral (k : ℝ) u φ
def normalizedMonomialDensity {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x : Space n) : ℝ :=
  MonomialIntegrability.monomialWeight
    (k : ℝ) (u : Space n) φ x /
      monomialNormSquared k (u : Space n) φ
def diagonalTerm {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x : Space n) : ℝ :=
  Real.exp ((k : ℝ) *
    SupportFunction.pairing (u : Space n) x) /
      monomialNormSquared k (u : Space n) φ
def diagonalKernel {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  ∑' u : LatticeAsymptotics.monomialIndex K k,
    diagonalTerm K k φ u x
def weightedDiagonalKernel {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  ∑' u : LatticeAsymptotics.monomialIndex K k,
    normalizedMonomialDensity K k φ u x
theorem monomialIndex_finite {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    (LatticeAsymptotics.monomialIndex K k).Finite := by
  classical
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  unfold LatticeAsymptotics.monomialIndex
    LatticeAsymptotics.scaledIntegerLattice
  rw [← Submodule.coe_pointwise_smul,
    ZSpan.smul _ (inv_ne_zero hkreal)]
  exact ZSpan.setFinite_inter _
    (K.compact.isBounded.subset interior_subset)
theorem zero_mem_monomialIndex {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    (0 : Space n) ∈
      LatticeAsymptotics.monomialIndex K k := by
  apply (LatticeAsymptotics.mem_monomialIndex_iff
    K hk 0).mpr
  refine ⟨LatticeAsymptotics.zero_mem_interior K, ?_⟩
  intro i
  exact ⟨0, by simp⟩
theorem bergmanDimension_pos {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    0 < bergmanDimension K k := by
  let : Finite (LatticeAsymptotics.monomialIndex K k) :=
    (monomialIndex_finite K hk).to_subtype
  let : Nonempty (LatticeAsymptotics.monomialIndex K k) :=
    ⟨⟨0, zero_mem_monomialIndex K hk⟩⟩
  exact Nat.card_pos
theorem weighted_diagonalTerm_eq_normalizedMonomialDensity
    {n k : ℕ} (K : CenteredBody n)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x : Space n) :
    Real.exp (-(k : ℝ) * φ x) * diagonalTerm K k φ u x =
      normalizedMonomialDensity K k φ u x := by
  unfold diagonalTerm normalizedMonomialDensity
    MonomialIntegrability.monomialWeight
  rw [mul_div_assoc', ← Real.exp_add]
  congr 1
  ring_nf
theorem weightedDiagonalKernel_eq_exp_neg_mul_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ) (x : Space n) :
    weightedDiagonalKernel K k φ x =
      Real.exp (-(k : ℝ) * φ x) * diagonalKernel K k φ x := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel diagonalKernel
  rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact (weighted_diagonalTerm_eq_normalizedMonomialDensity
    K φ u x).symm
theorem bergmanDimension_div_pow_tendsto_volume {n : ℕ}
    (K : CenteredBody n) :
    Tendsto
      (fun k : ℕ =>
        (bergmanDimension K k : ℝ) / (k : ℝ) ^ n)
      atTop (𝓝 (normalizedVolume K.carrier)) := by
  exact LatticeAsymptotics.monomial_count_div_pow_tendsto_volume K
end BergmanMonomials
namespace TorusCharacters
open Set MeasureTheory Filter
open scoped BigOperators ComplexConjugate ENNReal Topology
local instance _p2m_local_instance_3610026555_936 : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
abbrev LogSpace (n : ℕ) := Fin n → ℂ
abbrev AngularTorus (n : ℕ) := UnitAddTorus (Fin n)
def characterExponent {n : ℕ}
    (m : Fin n → ℤ) (ζ : LogSpace n) : ℂ :=
  ∑ i, (m i : ℂ) * ζ i
def torusCharacter {n : ℕ}
    (m : Fin n → ℤ) (ζ : LogSpace n) : ℂ :=
  Complex.exp (characterExponent m ζ)
def imaginaryShift {n : ℕ}
    (q : Fin n → ℤ) : LogSpace n :=
  fun i => (q i : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
theorem differentiable_characterExponent {n : ℕ}
    (m : Fin n → ℤ) :
    Differentiable ℂ (characterExponent m) := by
  unfold characterExponent
  fun_prop
theorem differentiable_torusCharacter {n : ℕ}
    (m : Fin n → ℤ) :
    Differentiable ℂ (torusCharacter m) := by
  unfold torusCharacter
  exact (differentiable_characterExponent m).cexp
theorem characterExponent_add {n : ℕ}
    (m : Fin n → ℤ) (ζ η : LogSpace n) :
    characterExponent m (ζ + η) =
      characterExponent m ζ + characterExponent m η := by
  simp [characterExponent, mul_add, Finset.sum_add_distrib]
theorem torusCharacter_ne_zero {n : ℕ}
    (m : Fin n → ℤ) (ζ : LogSpace n) :
    torusCharacter m ζ ≠ 0 :=
  Complex.exp_ne_zero _
theorem characterExponent_imaginaryShift {n : ℕ}
    (m q : Fin n → ℤ) :
    characterExponent m (imaginaryShift q) =
      ((∑ i, m i * q i : ℤ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I) := by
  unfold characterExponent imaginaryShift
  calc
    (∑ i, (m i : ℂ) *
        ((q i : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) =
        ∑ i, ((m i * q i : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
            apply Finset.sum_congr rfl
            intro i _
            push_cast
            ring
    _ = ((∑ i, m i * q i : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
            rw [← Finset.sum_mul]
            norm_cast
theorem torusCharacter_imaginaryShift {n : ℕ}
    (m q : Fin n → ℤ) (ζ : LogSpace n) :
    torusCharacter m (ζ + imaginaryShift q) =
      torusCharacter m ζ := by
  unfold torusCharacter
  rw [characterExponent_add,
    characterExponent_imaginaryShift, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]
def realLogSlice {n : ℕ}
    (x : Space n) : LogSpace n :=
  fun i => (x i : ℂ) / 2
theorem characterExponent_realLogSlice_re {n : ℕ}
    (m : Fin n → ℤ) (x : Space n) :
    (characterExponent m (realLogSlice x)).re =
      (∑ i, (m i : ℝ) * x i) / 2 := by
  unfold characterExponent realLogSlice
  simp [Finset.sum_div, Complex.mul_re, ← mul_div_assoc]
theorem norm_sq_torusCharacter_realLogSlice {n : ℕ}
    (m : Fin n → ℤ) (x : Space n) :
    ‖torusCharacter m (realLogSlice x)‖ ^ 2 =
      Real.exp (∑ i, (m i : ℝ) * x i) := by
  rw [torusCharacter, Complex.norm_exp,
    characterExponent_realLogSlice_re, pow_two, ← Real.exp_add]
  congr 1
  ring
theorem angular_characters_orthonormal (n : ℕ) :
    Orthonormal ℂ
      (UnitAddTorus.mFourierLp
        (d := Fin n) 2) :=
  UnitAddTorus.orthonormal_mFourier
end TorusCharacters
section
open Set MeasureTheory Filter
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
namespace WeightedTorusHilbert
local instance _p2m_local_instance_3610026555_1046 : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance _p2m_local_instance_3610026555_1049 : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
abbrev LogTorus (n : ℕ) :=
  Space n × TorusCharacters.AngularTorus n
def angularMeasure (n : ℕ) :
    Measure (TorusCharacters.AngularTorus n) :=
  volume
instance angularMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (angularMeasure n) := by
  unfold angularMeasure
  infer_instance
def radialWeight {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (x : Space n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(k : ℝ) * φ x))
def radialMeasure {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) : Measure (Space n) :=
  (volume : Measure (Space n)).withDensity
    (radialWeight k φ)
instance radialMeasure_sFinite {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) : SFinite (radialMeasure k φ) := by
  unfold radialMeasure
  infer_instance
def weightedTorusMeasure {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) : Measure (LogTorus n) :=
  (radialMeasure k φ).prod (angularMeasure n)
abbrev weightedHilbert {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :=
  MeasureTheory.Lp ℂ 2 (weightedTorusMeasure k φ)
theorem radialWeight_measurable {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Measurable (radialWeight k φ) := by
  unfold radialWeight
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp
      (continuous_const.mul hφ)).measurable
theorem weightedTorusMeasure_eq_withDensity {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    weightedTorusMeasure k φ =
      ((volume : Measure (Space n)).prod
        (angularMeasure n)).withDensity
          (fun z : LogTorus n => radialWeight k φ z.1) := by
  unfold weightedTorusMeasure radialMeasure
  exact MeasureTheory.prod_withDensity_left
    (radialWeight_measurable k hφ)
theorem angularCharacter_norm {n : ℕ} (m : Fin n → ℤ)
    (θ : TorusCharacters.AngularTorus n) :
    ‖UnitAddTorus.mFourier m θ‖ = 1 := by
  simp [UnitAddTorus.mFourier, fourier_apply, norm_prod]
theorem angularCharacter_inner {n : ℕ} (m q : Fin n → ℤ) :
    (∫ θ : TorusCharacters.AngularTorus n,
      conj (UnitAddTorus.mFourier m θ) *
        UnitAddTorus.mFourier q θ
      ∂(angularMeasure n)) =
        if m = q then (1 : ℂ) else 0 := by
  have h := (orthonormal_iff_ite.mp
    (TorusCharacters.angular_characters_orthonormal n)) m q
  rw [ContinuousMap.inner_toLp] at h
  simpa only [angularMeasure, mul_comm] using h
def radialCharacter {n : ℕ}
    (m : Fin n → ℤ) (x : Space n) : ℂ :=
  TorusCharacters.torusCharacter m
    (TorusCharacters.realLogSlice x)
def torusMonomial {n : ℕ}
    (m : Fin n → ℤ) (z : LogTorus n) : ℂ :=
  radialCharacter m z.1 * UnitAddTorus.mFourier m z.2
theorem continuous_torusMonomial {n : ℕ}
    (m : Fin n → ℤ) :
    Continuous (torusMonomial m) := by
  unfold torusMonomial radialCharacter
    TorusCharacters.torusCharacter
    TorusCharacters.characterExponent
    TorusCharacters.realLogSlice
  fun_prop
theorem torusMonomial_norm_sq {n : ℕ}
    (m : Fin n → ℤ) (z : LogTorus n) :
    ‖torusMonomial m z‖ ^ 2 =
      Real.exp (SupportFunction.pairing
        (integerPoint n m) z.1) := by
  unfold torusMonomial
  rw [norm_mul, angularCharacter_norm, mul_one]
  exact TorusCharacters.norm_sq_torusCharacter_realLogSlice
    m z.1
def integerExponent {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (u : LatticeAsymptotics.monomialIndex K k) :
    Fin n → ℤ :=
  fun i => Classical.choose
    (((LatticeAsymptotics.mem_monomialIndex_iff K hk
      (u : Space n)).mp u.property).2 i)
theorem integerPoint_integerExponent {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (u : LatticeAsymptotics.monomialIndex K k) :
    integerPoint n (integerExponent K hk u) =
      (k : ℝ) • (u : Space n) := by
  funext i
  exact Classical.choose_spec
    (((LatticeAsymptotics.mem_monomialIndex_iff K hk
      (u : Space n)).mp u.property).2 i)
theorem integerExponent_injective {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    Function.Injective (integerExponent K hk) := by
  intro u v huv
  apply Subtype.ext
  have hscaled :
      (k : ℝ) • (u : Space n) =
        (k : ℝ) • (v : Space n) := by
    rw [← integerPoint_integerExponent K hk u,
      ← integerPoint_integerExponent K hk v, huv]
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  funext i
  apply mul_left_cancel₀ hkreal
  exact congrFun hscaled i
theorem radialWeight_mul_exp_pairing {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u)
    (x : Space n) :
    (radialWeight k φ x).toReal *
      Real.exp (SupportFunction.pairing
        (integerPoint n m) x) =
      MonomialIntegrability.monomialWeight
        (k : ℝ) u φ x := by
  unfold radialWeight
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,
    hm, SupportFunction.pairing_smul_left]
  unfold MonomialIntegrability.monomialWeight
  rw [← Real.exp_add]
  congr 1
  ring
theorem radial_exp_integral_eq_monomialIntegral {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u) :
    (∫ x : Space n,
      Real.exp (SupportFunction.pairing
        (integerPoint n m) x)
      ∂(radialMeasure k φ)) =
      MonomialIntegrability.monomialIntegral
        (k : ℝ) u φ := by
  have hfinite : ∀ᵐ x ∂(volume : Measure (Space n)),
      radialWeight k φ x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold radialMeasure
    MonomialIntegrability.monomialIntegral
  rw [integral_withDensity_eq_integral_toReal_smul
    (radialWeight_measurable k hφ) hfinite]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  simpa only [smul_eq_mul] using
    radialWeight_mul_exp_pairing k φ m u hm x
theorem radial_exp_integrable {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable
      (fun x : Space n =>
        Real.exp (SupportFunction.pairing
          (integerPoint n m) x))
      (radialMeasure k φ) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hfinite : ∀ᵐ x ∂(volume : Measure (Space n)),
      radialWeight k φ x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold radialMeasure
  apply (MeasureTheory.integrable_withDensity_iff_integrable_smul'
    (radialWeight_measurable k hφ) hfinite).2
  have hmono :=
    MonomialIntegrability.integrable_monomialWeight_of_centeredBody
      K hu hφ hbounded hkreal
  refine hmono.congr (Filter.Eventually.of_forall fun x => ?_)
  simpa only [smul_eq_mul] using
    (radialWeight_mul_exp_pairing k φ m u hm x).symm
theorem torusMonomial_sq_integrable {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable (fun z : LogTorus n => ‖torusMonomial m z‖ ^ 2)
      (weightedTorusMeasure k φ) := by
  have hradial := radial_exp_integrable
    K hk hφ hbounded m u hu hm
  have hangular : Integrable
      (fun _ : TorusCharacters.AngularTorus n => (1 : ℝ))
      (angularMeasure n) := integrable_const _
  have hproduct := hradial.mul_prod hangular
  unfold weightedTorusMeasure
  convert hproduct using 1
  funext z
  simp [torusMonomial_norm_sq]
theorem torusMonomial_memLp {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    MemLp (torusMonomial m) 2 (weightedTorusMeasure k φ) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (continuous_torusMonomial m).aestronglyMeasurable).2
  exact torusMonomial_sq_integrable
    K hk hφ hbounded m u hu hm
theorem integral_torusMonomial_norm_sq_eq_monomialIntegral
    {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u) :
    (∫ z : LogTorus n, ‖torusMonomial m z‖ ^ 2
      ∂(weightedTorusMeasure k φ)) =
      MonomialIntegrability.monomialIntegral
        (k : ℝ) u φ := by
  unfold weightedTorusMeasure
  calc
    (∫ z : LogTorus n, ‖torusMonomial m z‖ ^ 2
      ∂(radialMeasure k φ).prod (angularMeasure n)) =
        ∫ z : LogTorus n,
          Real.exp (SupportFunction.pairing
            (integerPoint n m) z.1) * (1 : ℝ)
          ∂(radialMeasure k φ).prod (angularMeasure n) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with z
            simp [torusMonomial_norm_sq]
    _ = (∫ x : Space n,
          Real.exp (SupportFunction.pairing
            (integerPoint n m) x)
          ∂(radialMeasure k φ)) *
          (∫ _θ : TorusCharacters.AngularTorus n,
            (1 : ℝ) ∂(angularMeasure n)) :=
          MeasureTheory.integral_prod_mul
            (μ := radialMeasure k φ) (ν := angularMeasure n)
            (fun x : Space n =>
              Real.exp (SupportFunction.pairing
                (integerPoint n m) x))
            (fun _ : TorusCharacters.AngularTorus n =>
              (1 : ℝ))
    _ = MonomialIntegrability.monomialIntegral
          (k : ℝ) u φ := by
          rw [radial_exp_integral_eq_monomialIntegral
            k hφ m u hm]
          simp
theorem torusMonomial_inner_factor {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (m q : Fin n → ℤ) :
    (∫ z : LogTorus n,
      conj (torusMonomial m z) * torusMonomial q z
      ∂(weightedTorusMeasure k φ)) =
      (∫ x : Space n,
        conj (radialCharacter m x) * radialCharacter q x
        ∂(radialMeasure k φ)) *
          if m = q then (1 : ℂ) else 0 := by
  unfold weightedTorusMeasure
  calc
    (∫ z : LogTorus n,
      conj (torusMonomial m z) * torusMonomial q z
      ∂(radialMeasure k φ).prod (angularMeasure n)) =
        ∫ z : LogTorus n,
          (conj (radialCharacter m z.1) * radialCharacter q z.1) *
          (conj (UnitAddTorus.mFourier m z.2) *
            UnitAddTorus.mFourier q z.2)
          ∂(radialMeasure k φ).prod (angularMeasure n) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with z
            simp only [torusMonomial, map_mul]
            ring
    _ = (∫ x : Space n,
          conj (radialCharacter m x) * radialCharacter q x
          ∂(radialMeasure k φ)) *
        (∫ θ : TorusCharacters.AngularTorus n,
          conj (UnitAddTorus.mFourier m θ) *
            UnitAddTorus.mFourier q θ
          ∂(angularMeasure n)) :=
          MeasureTheory.integral_prod_mul
            (μ := radialMeasure k φ) (ν := angularMeasure n)
            (fun x : Space n =>
              conj (radialCharacter m x) * radialCharacter q x)
            (fun θ : TorusCharacters.AngularTorus n =>
              conj (UnitAddTorus.mFourier m θ) *
                UnitAddTorus.mFourier q θ)
    _ = _ := by rw [angularCharacter_inner]
theorem torusMonomial_inner_eq_zero_of_ne {n : ℕ}
    (k : ℕ) (φ : Space n → ℝ)
    (m q : Fin n → ℤ) (hmq : m ≠ q) :
    (∫ z : LogTorus n,
      conj (torusMonomial m z) * torusMonomial q z
      ∂(weightedTorusMeasure k φ)) = 0 := by
  rw [torusMonomial_inner_factor]
  simp [hmq]
def indexedMonomialLp {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (u : LatticeAsymptotics.monomialIndex K k) :
    weightedHilbert k φ :=
  (torusMonomial_memLp K hk hφ hbounded
    (integerExponent K hk u) (u : Space n)
    u.property.1 (integerPoint_integerExponent K hk u)).toLp
      (torusMonomial (integerExponent K hk u))
end WeightedTorusHilbert
namespace JetEnvelopeSlopeBridge
theorem coeFn_finset_sum_ae
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (I : Finset ι)
    (f : ι → MeasureTheory.Lp ℂ 2 μ) :
    (fun x : α => (∑ i ∈ I, f i) x)
      =ᵐ[μ] (fun x : α => ∑ i ∈ I, f i x) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      filter_upwards [MeasureTheory.Lp.coeFn_zero ℂ 2 μ]
        with x hx
      simpa only [Finset.sum_empty, Pi.zero_apply] using hx
  | @insert i I hi hI =>
      rw [Finset.sum_insert hi]
      have hadd := MeasureTheory.Lp.coeFn_add (f i) (∑ j ∈ I, f j)
      filter_upwards [hadd, hI] with x hx hsum
      simpa [Finset.sum_insert hi, Pi.add_apply] using
        hx.trans (congrArg (fun z : ℂ => f i x + z) hsum)
end JetEnvelopeSlopeBridge
namespace JetEnvelopeSlopeConvergence
def sourceTorusBaseMeasure (n : ℕ) :
    Measure (WeightedTorusHilbert.LogTorus n) :=
  (volume : Measure (Space n)).prod
    (WeightedTorusHilbert.angularMeasure n)
end JetEnvelopeSlopeConvergence
end
namespace BergmanNormalization
open Set MeasureTheory
open scoped BigOperators ENNReal
def normalizedDiagonalDensity {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  BergmanMonomials.weightedDiagonalKernel K k φ x /
    (BergmanMonomials.bergmanDimension K k : ℝ)
def normalizedBergmanMeasure {n : ℕ}
    (K : CenteredBody n) (k : ℕ)
    (φ : Space n → ℝ) : Measure (Space n) :=
  (volume : Measure (Space n)).withDensity
    (fun x => ENNReal.ofReal (normalizedDiagonalDensity K k φ x))
end BergmanNormalization
namespace BergmanJetSlope
open Set MeasureTheory
open scoped BigOperators ENNReal
end BergmanJetSlope
namespace JetCounting
open scoped BigOperators
def JetIndexLT (n j : ℕ) :=
  {α : Fin n → ℕ // (∑ i, α i) < j}
def symSigmaEquivJetIndexLT (n j : ℕ) :
    (Σ r : Fin j, Sym (Fin n) (r : ℕ)) ≃ JetIndexLT n j :=
  (Equiv.sigmaCongr Fin.equivSubtype
    (fun r : Fin j => Sym.equivNatSumOfFintype (Fin n) (r : ℕ))).trans
      (Equiv.sigmaSubtypeFiberEquivSubtype
        (fun α : Fin n → ℕ => ∑ i, α i)
        (p := fun α : Fin n → ℕ => (∑ i, α i) < j)
        (q := fun r : ℕ => r < j)
        (fun _ => Iff.rfl))
noncomputable instance instFintypeJetIndexLT (n j : ℕ) :
    Fintype (JetIndexLT n j) :=
  Fintype.ofEquiv (Σ r : Fin j, Sym (Fin n) (r : ℕ))
    (symSigmaEquivJetIndexLT n j)
end JetCounting
namespace BergmanJetFiltration
open Set MeasureTheory
open scoped BigOperators ENNReal
end BergmanJetFiltration
namespace AdaptedBergmanBasis
open Set MeasureTheory Module
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
def monomialIndexEquivFin {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k) :
    LatticeAsymptotics.monomialIndex K k ≃
      Fin (BergmanMonomials.bergmanDimension K k) := by
  letI := (BergmanMonomials.monomialIndex_finite K hk).fintype
  apply Fintype.equivFinOfCardEq
  simp [BergmanMonomials.bergmanDimension,
    Nat.card_eq_fintype_card]
def normalizedHolomorphicMonomial {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (ζ : TorusCharacters.LogSpace n) : ℂ :=
  ((Real.sqrt (BergmanMonomials.monomialNormSquared
      k (u : Space n) φ) : ℂ)⁻¹) *
    TorusCharacters.torusCharacter
      (WeightedTorusHilbert.integerExponent K hk u) ζ
theorem differentiable_normalizedHolomorphicMonomial {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ)
    (u : LatticeAsymptotics.monomialIndex K k) :
    Differentiable ℂ (normalizedHolomorphicMonomial K hk φ u) := by
  unfold normalizedHolomorphicMonomial
  exact (TorusCharacters.differentiable_torusCharacter _).const_mul _
def multiIndexCoordinate {n : ℕ} (α : Fin n → ℕ) :
    Fin (∑ i, α i) → Fin n := by
  classical
  let e : ((i : Fin n) × Fin (α i)) ≃ Fin (∑ i, α i) :=
    Fintype.equivFinOfCardEq (by simp)
  exact fun q => (e.symm q).1
def holomorphicMonomialJet {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    (φ : Space n → ℝ)
    (p : TorusCharacters.LogSpace n)
    (u : LatticeAsymptotics.monomialIndex K k)
    (α : Fin n → ℕ) : ℂ := by
  classical
  exact (iteratedFDeriv ℂ (∑ i, α i)
    (normalizedHolomorphicMonomial K hk φ u) p)
      (fun q => Pi.single (multiIndexCoordinate α q) (1 : ℂ))
end AdaptedBergmanBasis
namespace ArbitraryBodySmoothConvexPotentialBridge
open Set MeasureTheory
open scoped BigOperators Convolution Topology ContDiff
theorem pairing_sub_right {n : ℕ}
    (u x y : Space n) :
    SupportFunction.pairing u (x - y) =
      SupportFunction.pairing u x -
        SupportFunction.pairing u y := by
  simp [SupportFunction.pairing, mul_sub,
    Finset.sum_sub_distrib]
theorem supportFunction_lipschitzWith {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    {R : ℝ} (hR : ∀ u ∈ K, ‖u‖ ≤ R) :
    LipschitzWith (Real.toNNReal ((n : ℝ) * R))
      (SupportFunction.supportFunction K) := by
  apply LipschitzWith.of_le_add_mul' ((n : ℝ) * R)
  intro x y
  obtain ⟨u, hu, hmax⟩ :=
    SupportFunction.supportFunction_attained
      hcompact hnonempty x
  have hy := SupportFunction.pairing_le_supportFunction
    hcompact hu y
  have hpair :
      SupportFunction.pairing u (x - y) ≤
        ((n : ℝ) * R) * dist x y := by
    calc
      SupportFunction.pairing u (x - y) ≤
          |SupportFunction.pairing u (x - y)| :=
        le_abs_self _
      _ ≤ ((n : ℝ) * ‖u‖) * ‖x - y‖ :=
        MonomialDivergence.abs_pairing_le_dimension_mul_norm
          u (x - y)
      _ ≤ ((n : ℝ) * R) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hR u hu) (Nat.cast_nonneg n))
          (norm_nonneg _)
      _ = ((n : ℝ) * R) * dist x y := by rw [dist_eq_norm]
  calc
    SupportFunction.supportFunction K x =
        SupportFunction.pairing u x := hmax
    _ = SupportFunction.pairing u y +
          SupportFunction.pairing u (x - y) := by
      rw [pairing_sub_right]
      ring
    _ ≤ SupportFunction.supportFunction K y +
          ((n : ℝ) * R) * dist x y :=
      add_le_add hy hpair
theorem uniformContinuous_supportFunction {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) :
    UniformContinuous (SupportFunction.supportFunction K) := by
  obtain ⟨R, hRpos, hR⟩ := hcompact.isBounded.exists_pos_norm_le
  exact (supportFunction_lipschitzWith hcompact hnonempty hR).uniformContinuous
theorem continuous_supportFunction {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) :
    Continuous (SupportFunction.supportFunction K) :=
  (uniformContinuous_supportFunction hcompact hnonempty).continuous
theorem convexOn_supportFunction {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) :
    ConvexOn ℝ Set.univ
      (SupportFunction.supportFunction K) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply SupportFunction.supportFunction_le hnonempty _
  intro u hu
  have hux :=
    SupportFunction.pairing_le_supportFunction hcompact hu x
  have huy :=
    SupportFunction.pairing_le_supportFunction hcompact hu y
  calc
    SupportFunction.pairing u (a • x + b • y) =
        a * SupportFunction.pairing u x +
          b * SupportFunction.pairing u y := by
      simp [SupportFunction.pairing, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
    _ ≤ a * SupportFunction.supportFunction K x +
          b * SupportFunction.supportFunction K y :=
      add_le_add (mul_le_mul_of_nonneg_left hux ha)
        (mul_le_mul_of_nonneg_left huy hb)
    _ = a • SupportFunction.supportFunction K x +
          b • SupportFunction.supportFunction K y := by
      simp [smul_eq_mul]
def mollifiedSupport {n : ℕ} (K : Set (Space n))
    (ρ : ContDiffBump (0 : Space n)) :
    Space n → ℝ :=
  ρ.normed (volume : Measure (Space n)) ⋆
    SupportFunction.supportFunction K
theorem contDiff_mollifiedSupport {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    (ρ : ContDiffBump (0 : Space n)) :
    ContDiff ℝ ∞ (mollifiedSupport K ρ) := by
  unfold mollifiedSupport
  exact ρ.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ρ.contDiff_normed
    (continuous_supportFunction hcompact hnonempty).locallyIntegrable
theorem convexOn_mollifiedSupport {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    (ρ : ContDiffBump (0 : Space n)) :
    ConvexOn ℝ Set.univ (mollifiedSupport K ρ) := by
  change ConvexOn ℝ Set.univ
    (fun x : Space n =>
      ∫ t : Space n,
        ρ.normed (volume : Measure (Space n)) t *
          SupportFunction.supportFunction K (x - t)
        ∂(volume : Measure (Space n)))
  apply MeasureTheory.integral_convexOn_of_integrand_ae convex_univ
  · filter_upwards [] with t
    have htranslate :
        ConvexOn ℝ Set.univ
          (fun x : Space n =>
            SupportFunction.supportFunction K (x - t)) := by
      simpa [Function.comp_def, sub_eq_add_neg, add_comm] using
        (convexOn_supportFunction hcompact hnonempty).translate_right (-t)
    simpa [smul_eq_mul] using
      htranslate.smul
        (ρ.nonneg_normed (μ := (volume : Measure (Space n))) t)
  · intro x hx
    simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (ρ.hasCompactSupport_normed.convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        ρ.continuous_normed
        (continuous_supportFunction hcompact hnonempty).locallyIntegrable
        x).integrable
theorem dist_mollifiedSupport_le {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    {R : ℝ} (hRnonneg : 0 ≤ R)
    (hR : ∀ u ∈ K, ‖u‖ ≤ R)
    (ρ : ContDiffBump (0 : Space n))
    (x : Space n) :
    dist (mollifiedSupport K ρ x)
      (SupportFunction.supportFunction K x) ≤
      ((n : ℝ) * R) * ρ.rOut := by
  unfold mollifiedSupport
  apply ρ.dist_normed_convolution_le
    (continuous_supportFunction hcompact hnonempty).aestronglyMeasurable
  intro y hy
  have hlip :=
    (supportFunction_lipschitzWith hcompact hnonempty hR).dist_le_mul y x
  have hcoe :
      ((Real.toNNReal ((n : ℝ) * R) : ℝ)) =
        (n : ℝ) * R := by
    rw [Real.coe_toNNReal]
    positivity
  rw [hcoe] at hlip
  exact hlip.trans (mul_le_mul_of_nonneg_left
    (Metric.mem_ball.mp hy).le (mul_nonneg (Nat.cast_nonneg n) hRnonneg))
theorem exists_smooth_convex_potential_uniformly_close {n : ℕ}
    {K : Set (Space n)}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Space n → ℝ,
      ContDiff ℝ ∞ φ ∧ ConvexOn ℝ Set.univ φ ∧
        ∀ x : Space n,
          |φ x - SupportFunction.supportFunction K x| < ε := by
  obtain ⟨R, hRpos, hR⟩ := hcompact.isBounded.exists_pos_norm_le
  let L : ℝ := (n : ℝ) * R
  have hL : 0 ≤ L := mul_nonneg (Nat.cast_nonneg n) hRpos.le
  let δ : ℝ := ε / (L + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  let ρ : ContDiffBump (0 : Space n) :=
    ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  refine ⟨mollifiedSupport K ρ,
    contDiff_mollifiedSupport hcompact hnonempty ρ,
    convexOn_mollifiedSupport hcompact hnonempty ρ, ?_⟩
  intro x
  have hdist :=
    dist_mollifiedSupport_le hcompact hnonempty hRpos.le hR ρ x
  have hsmall : L * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < L + 1)).mpr
    nlinarith
  rw [Real.dist_eq] at hdist
  exact lt_of_le_of_lt hdist (by simpa [L, ρ] using hsmall)
theorem exists_smooth_convex_potential_of_centeredBody {n : ℕ}
    (K : CenteredBody n) :
    ∃ φ : Space n → ℝ,
      ContDiff ℝ ∞ φ ∧ ConvexOn ℝ Set.univ φ ∧
        ∀ x : Space n,
          |φ x -
            SupportFunction.supportFunction K.carrier x| ≤ 1 := by
  have hnonempty : K.carrier.Nonempty :=
    K.fullDimensional.mono interior_subset
  obtain ⟨φ, hφ, hconvex, hclose⟩ :=
    exists_smooth_convex_potential_uniformly_close
      K.compact hnonempty (show (0 : ℝ) < 1 by norm_num)
  exact ⟨φ, hφ, hconvex, fun x => (hclose x).le⟩
def smoothConvexPotential {n : ℕ} (K : CenteredBody n) :
    Space n → ℝ :=
  (exists_smooth_convex_potential_of_centeredBody K).choose
theorem smoothConvexPotential_contDiff {n : ℕ}
    (K : CenteredBody n) :
    ContDiff ℝ ∞ (smoothConvexPotential K) :=
  (exists_smooth_convex_potential_of_centeredBody K).choose_spec.1
theorem smoothConvexPotential_convex {n : ℕ}
    (K : CenteredBody n) :
    ConvexOn ℝ Set.univ (smoothConvexPotential K) :=
  (exists_smooth_convex_potential_of_centeredBody K).choose_spec.2.1
theorem smoothConvexPotential_bounded {n : ℕ}
    (K : CenteredBody n) (x : Space n) :
    |smoothConvexPotential K x -
      SupportFunction.supportFunction K.carrier x| ≤ 1 :=
  (exists_smooth_convex_potential_of_centeredBody K).choose_spec.2.2 x
end ArbitraryBodySmoothConvexPotentialBridge
namespace JetAdaptedOrthonormalBasis
open Set Module
open scoped BigOperators InnerProductSpace
theorem starProjection_commute_of_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (U W : Submodule ℂ V) (hUW : U ≤ W) :
    Commute (U.starProjection : V →ₗ[ℂ] V)
      (W.starProjection : V →ₗ[ℂ] V) := by
  apply LinearMap.ext
  intro x
  change U.starProjection (W.starProjection x) =
    W.starProjection (U.starProjection x)
  have h := DFunLike.congr_fun
    (Submodule.starProjection_comp_starProjection_of_le hUW) x
  rw [ContinuousLinearMap.comp_apply] at h
  rw [h]
  exact (Submodule.starProjection_eq_self_iff.mpr
    (hUW (U.starProjection_apply_mem x))).symm
theorem exists_orthonormalBasis_simultaneously_adapted_finite
    {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (F : ι → Submodule ℂ V)
    (hchain : ∀ i j, F i ≤ F j ∨ F j ≤ F i) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      ∀ (j : ι) (i : Fin (Module.finrank ℂ V)),
        b i ∈ F j ∨ b i ∈ (F j)ᗮ := by
  classical
  let T : ι → V →ₗ[ℂ] V :=
    fun j => ((F j).starProjection : V →ₗ[ℂ] V)
  have hsym : ∀ j, (T j).IsSymmetric := fun j =>
    (F j).starProjection_isSymmetric
  have hcomm : Pairwise (fun i j => Commute (T i) (T j)) := by
    intro i j _
    rcases hchain i j with hij | hji
    · exact starProjection_commute_of_le (F i) (F j) hij
    · exact (starProjection_commute_of_le (F j) (F i) hji).symm
  let code : (ι → Fin 2) → (ι → ℂ) :=
    fun σ i => ((σ i).val : ℂ)
  have hcode : Function.Injective code := by
    intro σ τ hστ
    funext i
    apply Fin.ext
    have hi : ((σ i).val : ℂ) = ((τ i).val : ℂ) := by
      simpa [code] using congrFun hστ i
    exact_mod_cast hi
  let J : (ι → Fin 2) → Submodule ℂ V :=
    fun σ => ⨅ i, Module.End.eigenspace (T i) (code σ i)
  have horth :=
    (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym).comp hcode
  have hfull :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hsym hcomm
  have htop : (⨆ σ : ι → Fin 2, J σ) = ⊤ := by
    apply top_unique
    rw [← hfull]
    apply iSup_le
    intro χ
    let σ : ι → Fin 2 :=
      fun i => if χ i = 0 then 0 else 1
    refine le_trans ?_ (le_iSup (fun q => J q) σ)
    intro x hx
    change x ∈ (⨅ i, Module.End.eigenspace (T i) (χ i)) at hx
    change x ∈ (⨅ i, Module.End.eigenspace (T i) (code σ i))
    apply (Submodule.mem_iInf _).mpr
    intro i
    have heig := Module.End.mem_eigenspace_iff.mp
      (((Submodule.mem_iInf _).mp hx) i)
    apply Module.End.mem_eigenspace_iff.mpr
    by_cases hzero : χ i = 0
    · simpa [code, σ, hzero] using heig
    · have hscaled : χ i • x ∈ F i := by
        rw [← heig]
        exact (F i).starProjection_apply_mem x
      have hmem := (F i).smul_mem (χ i)⁻¹ hscaled
      have hxF : x ∈ F i := by
        simpa [smul_smul, hzero] using hmem
      have hfix : (F i).starProjection x = x :=
        Submodule.starProjection_eq_self_iff.mpr hxF
      simpa [T, code, σ, hzero] using hfix
  have hinternal : DirectSum.IsInternal J := by
    apply horth.isInternal_iff.mpr
    rw [Submodule.orthogonal_eq_bot_iff]
    exact htop
  let b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V :=
    hinternal.subordinateOrthonormalBasis rfl horth
  refine ⟨b, ?_⟩
  intro j i
  let σ : ι → Fin 2 :=
    hinternal.subordinateOrthonormalBasisIndex rfl i horth
  have hbi : b i ∈ J σ :=
    hinternal.subordinateOrthonormalBasis_subordinate rfl i horth
  have heig : T j (b i) = code σ j • b i :=
    Module.End.mem_eigenspace_iff.mp
      (((Submodule.mem_iInf _).mp hbi) j)
  by_cases hzero : code σ j = 0
  · right
    have hproj : (F j).starProjection (b i) = 0 := by
      simpa [T, hzero] using heig
    have hker : b i ∈ (F j).starProjection.ker :=
      (LinearMap.mem_ker).2 hproj
    simpa only [Submodule.ker_starProjection] using hker
  · left
    have hscaled : code σ j • b i ∈ F j := by
      rw [← heig]
      exact (F j).starProjection_apply_mem (b i)
    have hmem := (F j).smul_mem (code σ j)⁻¹ hscaled
    simpa [smul_smul, hzero] using hmem
theorem finite_range_antitone_submodule
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (F : ℕ → Submodule ℂ V) (hF : Antitone F) :
    (Set.range F).Finite := by
  classical
  let d := Module.finrank ℂ V
  let rankFin : Submodule ℂ V → Fin (d + 1) := fun S =>
    ⟨Module.finrank ℂ S,
      Nat.lt_succ_of_le (Submodule.finrank_le S)⟩
  apply Set.Finite.of_finite_image (f := rankFin)
    (Set.toFinite (rankFin '' Set.range F))
  intro S hS W hW heq
  obtain ⟨i, rfl⟩ := hS
  obtain ⟨j, rfl⟩ := hW
  have hr : Module.finrank ℂ (F i) = Module.finrank ℂ (F j) := by
    simpa [rankFin] using congrArg Fin.val heq
  rcases le_total i j with hij | hji
  · exact (Submodule.eq_of_le_of_finrank_eq (hF hij) hr.symm).symm
  · exact Submodule.eq_of_le_of_finrank_eq (hF hji) hr
theorem exists_orthonormalBasis_simultaneously_adapted
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    (F : ℕ → Submodule ℂ V) (hF : Antitone F) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      ∀ (j : ℕ) (i : Fin (Module.finrank ℂ V)),
        b i ∈ F j ∨ b i ∈ (F j)ᗮ := by
  classical
  let s : Set (Submodule ℂ V) := Set.range F
  have hs : s.Finite := finite_range_antitone_submodule F hF
  let : Fintype s := hs.fintype
  let G : s → Submodule ℂ V := Subtype.val
  have hchain : ∀ a b : s, G a ≤ G b ∨ G b ≤ G a := by
    intro a b
    obtain ⟨i, hi⟩ := a.property
    obtain ⟨j, hj⟩ := b.property
    rcases le_total i j with hij | hji
    · right
      simpa [G, ← hi, ← hj] using hF hij
    · left
      simpa [G, ← hi, ← hj] using hF hji
  obtain ⟨b, hb⟩ :=
    exists_orthonormalBasis_simultaneously_adapted_finite G hchain
  refine ⟨b, ?_⟩
  intro j i
  exact hb ⟨F j, ⟨j, rfl⟩⟩ i
end JetAdaptedOrthonormalBasis
namespace GenuineJetAdaptedBasisCounting
open Set Module
open scoped BigOperators InnerProductSpace
def adaptedIndices {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (b : OrthonormalBasis ι ℂ V) (S : Submodule ℂ V) :
    Finset ι := by
  classical
  exact Finset.univ.filter (fun i => b i ∈ S)
end GenuineJetAdaptedBasisCounting
namespace LaurentJetSeparatedness
open Set Filter Module
open scoped BigOperators Topology
def bodyRadius {n : ℕ} (K : CenteredBody n) : ℝ :=
  Classical.choose K.compact.isBounded.exists_pos_norm_le
theorem bodyRadius_pos {n : ℕ} (K : CenteredBody n) :
    0 < bodyRadius K :=
  (Classical.choose_spec K.compact.isBounded.exists_pos_norm_le).1
theorem norm_le_bodyRadius {n : ℕ} (K : CenteredBody n)
    (x : Space n) (hx : x ∈ K.carrier) :
    ‖x‖ ≤ bodyRadius K :=
  (Classical.choose_spec K.compact.isBounded.exists_pos_norm_le).2 x hx
end LaurentJetSeparatedness
namespace LaplaceAsymptotics
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
def phase {n : ℕ} (u : Space n)
    (φ : Space n → ℝ) (x : Space n) : ℝ :=
  SupportFunction.pairing u x - φ x
def legendreTransform {n : ℕ}
    (φ : Space n → ℝ) (u : Space n) : ℝ :=
  sSup (Set.range (phase u φ))
theorem continuous_phase {n : ℕ} (u : Space n)
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous (phase u φ) :=
  (SupportFunction.continuous_pairing_right u).sub hφ
theorem exists_phase_le_const_sub_mul_sum_abs {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Space n,
      phase u φ x ≤ C - δ * ∑ i, |x i| := by
  obtain ⟨δ, hδ, hgap⟩ :=
    MonomialIntegrability.interior_sum_abs_gap hcompact hu
  refine ⟨δ, hδ, fun x => ?_⟩
  have hsupport := (abs_le.mp (hbounded x)).1
  have hinterior := hgap x
  unfold phase
  linarith
theorem exists_phase_maximizer {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C) :
    ∃ x : Space n, ∀ y : Space n,
      phase u φ y ≤ phase u φ x := by
  obtain ⟨δ, hδ, hcoercive⟩ :=
    exists_phase_le_const_sub_mul_sum_abs hcompact hu hbounded
  let R : ℝ := max 0 ((C - phase u φ 0) / δ)
  apply (continuous_phase u hφ).exists_forall_ge' 0
  filter_upwards [
    (isCompact_closedBall (0 : Space n) R).compl_mem_cocompact
  ] with x hx
  have hxnorm : R < ‖x‖ := by
    apply lt_of_not_ge
    intro h
    apply hx
    simpa [Metric.mem_closedBall] using h
  have hR : C - phase u φ 0 ≤ δ * R := by
    have hrange : (C - phase u φ 0) / δ ≤ R :=
      le_max_right _ _
    have hscale := (div_le_iff₀ hδ).mp hrange
    nlinarith
  have hnorm := SupportFunction.norm_le_sum_abs x
  have hscale := mul_lt_mul_of_pos_left hxnorm hδ
  have hcoerce := hcoercive x
  nlinarith [mul_le_mul_of_nonneg_left hnorm hδ.le]
theorem legendreTransform_eq_of_maximizer {n : ℕ}
    {u : Space n} {φ : Space n → ℝ}
    (x : Space n)
    (hmax : ∀ y : Space n,
      phase u φ y ≤ phase u φ x) :
    legendreTransform φ u = phase u φ x := by
  unfold legendreTransform
  apply le_antisymm
  · apply csSup_le
    · exact ⟨phase u φ x, ⟨x, rfl⟩⟩
    · rintro _ ⟨y, rfl⟩
      exact hmax y
  · apply le_csSup
    · exact ⟨phase u φ x, by
        rintro _ ⟨y, rfl⟩
        exact hmax y⟩
    · exact ⟨x, rfl⟩
theorem exists_legendre_maximizer {n : ℕ}
    {K : Set (Space n)} (hcompact : IsCompact K)
    {u : Space n} (hu : u ∈ interior K)
    {φ : Space n → ℝ} (hφ : Continuous φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K x| ≤ C) :
    ∃ x : Space n,
      phase u φ x = legendreTransform φ u ∧
      ∀ y : Space n, phase u φ y ≤ phase u φ x := by
  obtain ⟨x, hx⟩ :=
    exists_phase_maximizer hcompact hu hφ hbounded
  exact ⟨x, (legendreTransform_eq_of_maximizer x hx).symm, hx⟩
end LaplaceAsymptotics
namespace BergmanAsymptotics
open Set MeasureTheory Filter Matrix
open scoped BigOperators ENNReal Topology
def actualHessianBilinear {n : ℕ}
    (φ : Space n → ℝ) (x : Space n) :
    Space n →ₗ[ℝ] Space n →ₗ[ℝ] ℝ where
  toFun v := (fderiv ℝ (fderiv ℝ φ) x v).toLinearMap
  map_add' v w := by
    ext z
    simp
  map_smul' a v := by
    ext z
    simp
def actualHessianMatrix {n : ℕ}
    (φ : Space n → ℝ) (x : Space n) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix₂' ℝ (actualHessianBilinear φ x)
def pairingLinear {n : ℕ}
    (u : Space n) : Space n →ₗ[ℝ] ℝ where
  toFun := SupportFunction.pairing u
  map_add' x y :=
    MonomialDivergence.pairing_add_right u x y
  map_smul' c x := by
    simpa [smul_eq_mul] using
      MonomialDivergence.pairing_smul_right c u x
end BergmanAsymptotics
namespace GlobalBergmanKernelBound
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
theorem supportFunction_add_smul_le {n : ℕ}
    (K : CenteredBody n)
    (x v : Space n) {t : ℝ} (ht : 0 ≤ t) :
    SupportFunction.supportFunction K.carrier (x + t • v) ≤
      SupportFunction.supportFunction K.carrier x +
        t * SupportFunction.supportFunction K.carrier v := by
  have hnonempty : K.carrier.Nonempty :=
    K.fullDimensional.mono interior_subset
  apply SupportFunction.supportFunction_le hnonempty _
  intro u hu
  have hx := SupportFunction.pairing_le_supportFunction
    K.compact hu x
  have hv := SupportFunction.pairing_le_supportFunction
    K.compact hu v
  calc
    SupportFunction.pairing u (x + t • v) =
        SupportFunction.pairing u x +
          t * SupportFunction.pairing u v := by
      simp [SupportFunction.pairing, mul_add,
        Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
    _ ≤ SupportFunction.supportFunction K.carrier x +
        t * SupportFunction.supportFunction K.carrier v :=
      add_le_add hx (mul_le_mul_of_nonneg_left hv ht)
theorem convex_extrapolation_lower {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ)
    (x y : Space n) {t : ℝ} (ht : 1 ≤ t) :
    φ y + t * (φ x - φ y) ≤ φ (y + t • (x - y)) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have htne : t ≠ 0 := ne_of_gt htpos
  have hinvnonneg : 0 ≤ (1 / t : ℝ) := by positivity
  have hinvle : (1 / t : ℝ) ≤ 1 := by
    apply (div_le_iff₀ htpos).mpr
    simpa using ht
  have ha : 0 ≤ 1 - (1 / t : ℝ) := sub_nonneg.mpr hinvle
  have hsum : (1 - (1 / t : ℝ)) + 1 / t = 1 := by ring
  have hpoint :
      (1 - (1 / t : ℝ)) • y +
          (1 / t : ℝ) • (y + t • (x - y)) = x := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hconv := hφ.2
    (Set.mem_univ y)
    (Set.mem_univ (y + t • (x - y)))
    ha hinvnonneg hsum
  rw [hpoint] at hconv
  simp only [smul_eq_mul] at hconv
  have hscaled := mul_le_mul_of_nonneg_left hconv htpos.le
  have hcancel :
      t * ((1 - (1 / t : ℝ)) * φ y + (1 / t : ℝ) *
        φ (y + t • (x - y))) =
      (t - 1) * φ y + φ (y + t • (x - y)) := by
    field_simp
  rw [hcancel] at hscaled
  linarith
theorem convex_supportCompatible_sub_le_support {n : ℕ}
    (K : CenteredBody n)
    {φ : Space n → ℝ}
    (hconvex : ConvexOn ℝ Set.univ φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (x y : Space n) :
    φ x - φ y ≤
      SupportFunction.supportFunction K.carrier (x - y) := by
  by_contra hnot
  have hgap : 0 <
      φ x - φ y -
        SupportFunction.supportFunction K.carrier (x - y) := by
    have hstrict := lt_of_not_ge hnot
    linarith
  let gap : ℝ :=
    φ x - φ y -
      SupportFunction.supportFunction K.carrier (x - y)
  have hgappos : 0 < gap := hgap
  let D : ℝ :=
    SupportFunction.supportFunction K.carrier y + C - φ y
  let t : ℝ := max 1 (D / gap + 1)
  have ht : 1 ≤ t := le_max_left _ _
  have hlarge : D < t * gap := by
    have hmax : D / gap + 1 ≤ t := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right hmax hgappos.le
    have hcancel : (D / gap + 1) * gap = D + gap := by
      field_simp
    rw [hcancel] at hmul
    linarith
  have hconv := convex_extrapolation_lower hconvex x y ht
  have hsupport := supportFunction_add_smul_le
    K y (x - y) (show 0 ≤ t from (zero_le_one.trans ht))
  have hupper := (abs_le.mp (hbounded (y + t • (x - y)))).2
  have hcombined :
      φ (y + t • (x - y)) ≤
        SupportFunction.supportFunction K.carrier y +
          t * SupportFunction.supportFunction K.carrier (x - y) + C := by
    linarith
  dsimp [D, gap] at hlarge
  linarith
theorem convex_supportCompatible_lipschitz {n : ℕ}
    (K : CenteredBody n)
    {φ : Space n → ℝ}
    (hconvex : ConvexOn ℝ Set.univ φ) {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C) :
    LipschitzWith
      (Real.toNNReal ((n : ℝ) *
        LaurentJetSeparatedness.bodyRadius K)) φ := by
  apply LipschitzWith.of_le_add_mul'
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K)
  intro x y
  have hrec := convex_supportCompatible_sub_le_support
    K hconvex hbounded x y
  have hnonempty : K.carrier.Nonempty :=
    K.fullDimensional.mono interior_subset
  obtain ⟨u, hu, hmax⟩ :=
    SupportFunction.supportFunction_attained
      K.compact hnonempty (x - y)
  have hradius := LaurentJetSeparatedness.norm_le_bodyRadius
    K u hu
  have hpair :=
    MonomialDivergence.abs_pairing_le_dimension_mul_norm
      u (x - y)
  have hsupport :
      SupportFunction.supportFunction K.carrier (x - y) ≤
        ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * dist x y := by
    rw [hmax, dist_eq_norm]
    calc
      SupportFunction.pairing u (x - y) ≤
          |SupportFunction.pairing u (x - y)| := le_abs_self _
      _ ≤ ((n : ℝ) * ‖u‖) * ‖x - y‖ := hpair
      _ ≤ ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hradius (Nat.cast_nonneg n))
          (norm_nonneg _)
  linarith
def phaseSlopeBound {n : ℕ} (K : CenteredBody n)
    (L : NNReal) : ℝ :=
  (n : ℝ) * LaurentJetSeparatedness.bodyRadius K + (L : ℝ)
theorem phaseSlopeBound_nonneg {n : ℕ}
    (K : CenteredBody n) (L : NNReal) :
    0 ≤ phaseSlopeBound K L := by
  unfold phaseSlopeBound
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg n)
      (LaurentJetSeparatedness.bodyRadius_pos K).le)
    L.coe_nonneg
def bodyPhaseSlopeBound {n : ℕ} (K : CenteredBody n) : ℝ :=
  2 * ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K)
theorem phaseSlopeBound_body {n : ℕ}
    (K : CenteredBody n) :
    phaseSlopeBound K
      (Real.toNNReal ((n : ℝ) *
        LaurentJetSeparatedness.bodyRadius K)) =
      bodyPhaseSlopeBound K := by
  have hnonneg : 0 ≤
      (n : ℝ) * LaurentJetSeparatedness.bodyRadius K :=
    mul_nonneg (Nat.cast_nonneg n)
      (LaurentJetSeparatedness.bodyRadius_pos K).le
  unfold phaseSlopeBound bodyPhaseSlopeBound
  rw [Real.coe_toNNReal _ hnonneg]
  ring
theorem monomialExponent_norm_le_bodyRadius {n k : ℕ}
    (K : CenteredBody n)
    (u : LatticeAsymptotics.monomialIndex K k) :
    ‖(u : Space n)‖ ≤
      LaurentJetSeparatedness.bodyRadius K := by
  exact LaurentJetSeparatedness.norm_le_bodyRadius
    K u (interior_subset u.property.1)
theorem phase_abs_sub_le {n k : ℕ}
    (K : CenteredBody n)
    {φ : Space n → ℝ} {L : NNReal}
    (hφ : LipschitzWith L φ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x y : Space n) :
    |LaplaceAsymptotics.phase (u : Space n) φ x -
      LaplaceAsymptotics.phase (u : Space n) φ y| ≤
      phaseSlopeBound K L * dist x y := by
  have hpair :
      |SupportFunction.pairing (u : Space n) x -
        SupportFunction.pairing (u : Space n) y| ≤
        ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
          dist x y := by
    rw [← show
      SupportFunction.pairing (u : Space n) (x - y) =
        SupportFunction.pairing (u : Space n) x -
          SupportFunction.pairing (u : Space n) y by
        simp [SupportFunction.pairing, mul_sub,
          Finset.sum_sub_distrib]]
    calc
      |SupportFunction.pairing (u : Space n) (x - y)| ≤
          ((n : ℝ) * ‖(u : Space n)‖) * ‖x - y‖ :=
        MonomialDivergence.abs_pairing_le_dimension_mul_norm
          (u : Space n) (x - y)
      _ ≤ ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (monomialExponent_norm_le_bodyRadius K u)
            (Nat.cast_nonneg n))
          (norm_nonneg _)
      _ = ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * dist x y := by
        rw [dist_eq_norm]
  have hpot : |φ x - φ y| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using hφ.dist_le_mul x y
  calc
    |LaplaceAsymptotics.phase (u : Space n) φ x -
      LaplaceAsymptotics.phase (u : Space n) φ y| =
      |(SupportFunction.pairing (u : Space n) x -
        SupportFunction.pairing (u : Space n) y) -
        (φ x - φ y)| := by
      unfold LaplaceAsymptotics.phase
      congr 1
      ring
    _ ≤ |SupportFunction.pairing (u : Space n) x -
          SupportFunction.pairing (u : Space n) y| +
        |φ x - φ y| := abs_sub _ _
    _ ≤ ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) * dist x y +
        (L : ℝ) * dist x y := add_le_add hpair hpot
    _ = phaseSlopeBound K L * dist x y := by
      unfold phaseSlopeBound
      ring
theorem real_volume_ball_inv_nat {n k : ℕ}
    (hk : 0 < k) (x : Space n) :
    (volume : Measure (Space n)).real
      (Metric.ball x (k : ℝ)⁻¹) =
      (2 / (k : ℝ)) ^ n := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  unfold Measure.real
  rw [Real.volume_pi_ball x (inv_pos.mpr hkreal)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp [div_eq_mul_inv]
theorem phase_lower_on_inv_nat_ball {n k : ℕ}
    (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} {L : NNReal}
    (hφ : LipschitzWith L φ)
    (u : LatticeAsymptotics.monomialIndex K k)
    (x v : Space n)
    (hv : v ∈ Metric.ball x (k : ℝ)⁻¹) :
    LaplaceAsymptotics.phase (u : Space n) φ x -
      phaseSlopeBound K L / (k : ℝ) ≤
      LaplaceAsymptotics.phase (u : Space n) φ v := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hdist : dist x v < (k : ℝ)⁻¹ := by
    simpa only [dist_comm] using Metric.mem_ball.mp hv
  have hS := phaseSlopeBound_nonneg K L
  have habs := phase_abs_sub_le K hφ u x v
  have hbound : phaseSlopeBound K L * dist x v ≤
      phaseSlopeBound K L / (k : ℝ) := by
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hdist.le hS
  have hdiff :
      LaplaceAsymptotics.phase (u : Space n) φ x -
        LaplaceAsymptotics.phase (u : Space n) φ v ≤
        |LaplaceAsymptotics.phase (u : Space n) φ x -
          LaplaceAsymptotics.phase (u : Space n) φ v| :=
    le_abs_self _
  linarith [hkreal]
theorem eventually_bergmanDimension_le_volume_mul_pow
    {n : ℕ} (K : CenteredBody n) :
    ∀ᶠ k : ℕ in atTop,
      (BergmanMonomials.bergmanDimension K k : ℝ) ≤
        (normalizedVolume K.carrier + 1) * (k : ℝ) ^ n := by
  have hlimit := BergmanMonomials.bergmanDimension_div_pow_tendsto_volume K
  have hevent := hlimit.eventually
    (gt_mem_nhds (show normalizedVolume K.carrier <
      normalizedVolume K.carrier + 1 by linarith))
  filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with k hquot hk
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  exact (div_le_iff₀ (pow_pos hkreal n)).mp hquot.le
def globalKernelPolynomialConstant {n : ℕ}
    (K : CenteredBody n) : ℝ :=
  (normalizedVolume K.carrier + 1) *
    Real.exp (bodyPhaseSlopeBound K) / (2 : ℝ) ^ n
theorem globalKernelPolynomialConstant_pos {n : ℕ}
    (K : CenteredBody n) :
    0 < globalKernelPolynomialConstant K := by
  unfold globalKernelPolynomialConstant
  have hvolume := K.volume_pos
  positivity
def globalKernelLogError {n : ℕ}
    (K : CenteredBody n) (k : ℕ) : ℝ :=
  (Real.log (globalKernelPolynomialConstant K) +
    2 * (n : ℝ) * Real.log (k : ℝ)) / (k : ℝ)
theorem tendsto_globalKernelLogError {n : ℕ}
    (K : CenteredBody n) :
    Tendsto (globalKernelLogError K) atTop (𝓝 0) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconst : Tendsto
      (fun k : ℕ =>
        Real.log (globalKernelPolynomialConstant K) / (k : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto
      (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_
      ((Real.tendsto_pow_log_div_mul_add_atTop
        1 0 1 one_ne_zero).comp hnat)
    exact Filter.Eventually.of_forall fun _ => by simp
  have hscaled := hlog.const_mul (2 * (n : ℝ))
  have hsum := hconst.add hscaled
  have hpoint : globalKernelLogError K =
      (fun k : ℕ =>
        Real.log (globalKernelPolynomialConstant K) / (k : ℝ) +
          2 * (n : ℝ) * (Real.log (k : ℝ) / (k : ℝ))) := by
    funext k
    unfold globalKernelLogError
    rw [add_div]
    ring
  rw [hpoint]
  simpa using hsum
end GlobalBergmanKernelBound
namespace LaurentJetMultiplicityBridge
open Set Filter Module
open scoped BigOperators Topology
def coordinateMultiplicity {n r : ℕ}
    (q : Fin r → Fin n) (i : Fin n) : ℕ := by
  classical
  exact Fintype.card {a : Fin r // q a = i}
def multiIndexSigmaEquiv {n : ℕ} (α : Fin n → ℕ) :
    ((i : Fin n) × Fin (α i)) ≃ Fin (∑ i, α i) :=
  Fintype.equivFinOfCardEq (by simp)
theorem multiIndexCoordinate_eq_sigma {n : ℕ}
    (α : Fin n → ℕ) (q : Fin (∑ i, α i)) :
    AdaptedBergmanBasis.multiIndexCoordinate α q =
      ((multiIndexSigmaEquiv α).symm q).1 := by
  rfl
def multiIndexCoordinateFiberEquiv {n : ℕ}
    (α : Fin n → ℕ) (i : Fin n) :
    {q : Fin (∑ i, α i) //
      AdaptedBergmanBasis.multiIndexCoordinate α q = i} ≃
      Fin (α i) := by
  classical
  refine ((multiIndexSigmaEquiv α).symm.subtypeEquiv ?_).trans
    (Equiv.sigmaSubtype i)
  intro q
  exact ⟨fun h => (multiIndexCoordinate_eq_sigma α q).symm ▸ h,
    fun h => (multiIndexCoordinate_eq_sigma α q) ▸ h⟩
end LaurentJetMultiplicityBridge
namespace BergmanGeodesicConvexity
open Set Module
open scoped BigOperators InnerProductSpace
def exponentialMoment {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (r : ℕ) (t : ℝ) : ℝ :=
  ∑ i, w i * (order i : ℝ) ^ r *
    Real.exp (t * (order i : ℝ))
def exponentialPartition {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (t : ℝ) : ℝ :=
  exponentialMoment w order 0 t
theorem exponentialPartition_pos {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    (t : ℝ) : 0 < exponentialPartition w order t := by
  classical
  obtain ⟨i, hi⟩ := hpositive
  unfold exponentialPartition exponentialMoment
  simp only [pow_zero, mul_one]
  apply lt_of_lt_of_le (mul_pos hi (Real.exp_pos _))
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
    (Finset.mem_univ i)
theorem hasDerivAt_exponentialMoment {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (r : ℕ) (t : ℝ) :
    HasDerivAt (exponentialMoment w order r)
      (exponentialMoment w order (r + 1) t) t := by
  classical
  unfold exponentialMoment
  refine HasDerivAt.fun_sum (u := (Finset.univ : Finset ι))
    (fun i _ => ?_)
  exact ((((hasDerivAt_id t).mul_const (order i : ℝ)).exp).const_mul
    (w i * (order i : ℝ) ^ r)).congr_deriv (by
      simp [pow_succ, mul_assoc, mul_left_comm, mul_comm])
theorem hasDerivAt_exponentialPartition {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (t : ℝ) :
    HasDerivAt (exponentialPartition w order)
      (exponentialMoment w order 1 t) t := by
  change HasDerivAt (exponentialMoment w order 0)
    (exponentialMoment w order 1 t) t
  exact hasDerivAt_exponentialMoment w order 0 t
def logarithmicPotential {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ) (k : ℝ) (t : ℝ) : ℝ :=
  Real.log (exponentialPartition w order t) / k
theorem hasDerivAt_logarithmicPotential {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    (k t : ℝ) :
    HasDerivAt (logarithmicPotential w order k)
      (exponentialMoment w order 1 t /
        exponentialPartition w order t / k) t := by
  unfold logarithmicPotential
  exact ((hasDerivAt_exponentialPartition w order t).log
    (exponentialPartition_pos w order hw hpositive t).ne').div_const k
theorem logarithmicPotential_deriv_nonneg {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {k : ℝ} (hk : 0 < k) (t : ℝ) :
    0 ≤ deriv (logarithmicPotential w order k) t := by
  rw [(hasDerivAt_logarithmicPotential
    w order hw hpositive k t).deriv]
  apply div_nonneg
  · apply div_nonneg
    · unfold exponentialMoment
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (hw i) (by positivity))
          (Real.exp_pos _).le
    · exact (exponentialPartition_pos w order hw hpositive t).le
  · exact hk.le
theorem logarithmicPotential_deriv_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {k : ℝ} (hk : 0 < k) (J : ℕ)
    (horder : ∀ i, order i ≤ J) (t : ℝ) :
    deriv (logarithmicPotential w order k) t ≤
      (J : ℝ) / k := by
  rw [(hasDerivAt_logarithmicPotential
    w order hw hpositive k t).deriv]
  apply div_le_div_of_nonneg_right _ hk.le
  apply (div_le_iff₀
    (exponentialPartition_pos w order hw hpositive t)).mpr
  unfold exponentialMoment exponentialPartition
    exponentialMoment
  simp only [pow_one, pow_zero, mul_one, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : (order i : ℝ) ≤ (J : ℝ) := by
    exact_mod_cast horder i
  calc
    w i * (order i : ℝ) * Real.exp (t * (order i : ℝ)) ≤
        w i * (J : ℝ) * Real.exp (t * (order i : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hi (hw i))
        (Real.exp_pos _).le
    _ = (J : ℝ) * (w i * Real.exp (t * (order i : ℝ))) := by
      ring
end BergmanGeodesicConvexity
namespace BodyScale
open Set MeasureTheory
def canonicalScale {n : ℕ} (K : CenteredBody n) : ℝ :=
  ((n.factorial : ℝ) * normalizedVolume K.carrier) ^
    ((n : ℝ)⁻¹)
theorem factorial_mul_volume_pos {n : ℕ}
    (K : CenteredBody n) :
    0 < (n.factorial : ℝ) * normalizedVolume K.carrier := by
  exact mul_pos (by exact_mod_cast Nat.factorial_pos n) K.volume_pos
theorem canonicalScale_pos {n : ℕ}
    (K : CenteredBody n) : 0 < canonicalScale K := by
  unfold canonicalScale
  exact Real.rpow_pos_of_pos (factorial_mul_volume_pos K) _
end BodyScale
namespace JetAsymptotics
open Asymptotics Filter MeasureTheory
open scoped BigOperators Topology
end JetAsymptotics
namespace Geometry
open Set MeasureTheory
open scoped BigOperators
def coordinateSum (n : ℕ) : Space n →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by
    simp [Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Finset.mul_sum]
end Geometry
namespace SimplexVolume
open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise
def splitStandardSimplex (n : ℕ) : Set (ℝ × Space n) :=
  {p | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ p.1 + (∑ i, p.2 i) ≤ 1}
end SimplexVolume
namespace BergmanDiagonalBasisIndependence
open Set Filter MeasureTheory InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Topology
def realLogCoordinate {n : ℕ}
    (z : TorusCharacters.LogSpace n) : Space n :=
  fun i => 2 * (z i).re
theorem normSq_torusCharacter_eq_realLogSlice {n : ℕ}
    (m : Fin n → ℤ) (z : TorusCharacters.LogSpace n) :
    Complex.normSq (TorusCharacters.torusCharacter m z) =
      Complex.normSq (TorusCharacters.torusCharacter m
        (TorusCharacters.realLogSlice (realLogCoordinate z))) := by
  have hre :
      (TorusCharacters.characterExponent m z).re =
        (TorusCharacters.characterExponent m
          (TorusCharacters.realLogSlice
            (realLogCoordinate z))).re := by
    simp only [TorusCharacters.characterExponent,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [TorusCharacters.realLogSlice,
      realLogCoordinate, Complex.mul_re]
  simp only [Complex.normSq_eq_norm_sq,
    TorusCharacters.torusCharacter, Complex.norm_exp, hre]
theorem exponentialPartition_le_exp_mul_sum
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i)
    (J : ℕ) (horder : ∀ i, order i ≤ J)
    {t : ℝ} (ht : 0 ≤ t) :
    BergmanGeodesicConvexity.exponentialPartition w order t ≤
      Real.exp (t * (J : ℝ)) * ∑ i, w i := by
  classical
  unfold BergmanGeodesicConvexity.exponentialPartition
    BergmanGeodesicConvexity.exponentialMoment
  simp only [pow_zero, mul_one]
  calc
    (∑ i, w i * Real.exp (t * (order i : ℝ))) ≤
      ∑ i, w i * Real.exp (t * (J : ℝ)) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hw i)
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ ht
        exact_mod_cast horder i
    _ = Real.exp (t * (J : ℝ)) * ∑ i, w i := by
      rw [← Finset.sum_mul]
      ring
end BergmanDiagonalBasisIndependence
namespace ActualJetUpperEnvelope
open Set Filter MeasureTheory
open BergmanDiagonalBasisIndependence
open scoped BigOperators Topology
def localUpperBounds {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) : Set ℝ :=
  {c | ∀ᶠ y : X in 𝓝 x, f y ≤ c}
theorem localUpperBounds_bddBelow {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) :
    BddBelow (localUpperBounds f x) := by
  refine ⟨f x, ?_⟩
  intro c hc
  change (∀ᶠ y : X in 𝓝 x, f y ≤ c) at hc
  exact hc.self_of_nhds
def upperRegularization {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) : ℝ :=
  sInf (localUpperBounds f x)
theorem upperRegularization_le_of_eventually
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) {c : ℝ}
    (hc : ∀ᶠ y : X in 𝓝 x, f y ≤ c) :
    upperRegularization f x ≤ c := by
  exact csInf_le (localUpperBounds_bddBelow f x) hc
theorem le_upperRegularization
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X)
    (hb : (localUpperBounds f x).Nonempty) :
    f x ≤ upperRegularization f x := by
  apply le_csInf hb
  intro c hc
  change (∀ᶠ y : X in 𝓝 x, f y ≤ c) at hc
  exact hc.self_of_nhds
theorem upperSemicontinuous_upperRegularization
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ)
    (hb : ∀ x : X, (localUpperBounds f x).Nonempty) :
    UpperSemicontinuous (upperRegularization f) := by
  apply upperSemicontinuous_iff_isOpen_preimage.mpr
  intro a
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change upperRegularization f x < a at hx
  obtain ⟨c, hc, hca⟩ :=
    exists_lt_of_csInf_lt (hb x) hx
  obtain ⟨U, hUsub, hUopen, hxU⟩ :=
    mem_nhds_iff.mp hc
  apply Filter.mem_of_superset (hUopen.mem_nhds hxU)
  intro y hy
  change upperRegularization f y < a
  have hlocal : ∀ᶠ w : X in 𝓝 y, f w ≤ c :=
    Filter.mem_of_superset (hUopen.mem_nhds hy) hUsub
  exact lt_of_le_of_lt
    (upperRegularization_le_of_eventually f y hlocal) hca
theorem upperRegularization_le_of_continuous_majorant
    {X : Type*} [TopologicalSpace X]
    (f b : X → ℝ) (hb : Continuous b)
    (hpoint : ∀ x : X, f x ≤ b x) (x : X) :
    upperRegularization f x ≤ b x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ y : X in 𝓝 x,
      b y < b x + ε :=
    (hb.continuousAt.eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hε)))
  exact upperRegularization_le_of_eventually f x
    (hev.mono fun y hy => le_trans (hpoint y) hy.le)
theorem localUpperBounds_nonempty_of_continuous_majorant
    {X : Type*} [TopologicalSpace X]
    (f b : X → ℝ) (hb : Continuous b)
    (hpoint : ∀ x : X, f x ≤ b x) (x : X) :
    (localUpperBounds f x).Nonempty := by
  refine ⟨b x + 1, ?_⟩
  change ∀ᶠ y : X in 𝓝 x, f y ≤ b x + 1
  have hev : ∀ᶠ y : X in 𝓝 x,
      b y < b x + 1 :=
    hb.continuousAt.eventually
      (Iio_mem_nhds (by linarith : b x < b x + 1))
  exact hev.mono fun y hy => le_trans (hpoint y) hy.le
theorem upperRegularization_mono
    {X : Type*} [TopologicalSpace X]
    (f g : X → ℝ) (x : X)
    (hle : ∀ y : X, f y ≤ g y)
    (hg : (localUpperBounds g x).Nonempty) :
    upperRegularization f x ≤ upperRegularization g x := by
  apply csInf_le_csInf (localUpperBounds_bddBelow f x) hg
  intro c hc
  change (∀ᶠ y : X in 𝓝 x, g y ≤ c) at hc
  change ∀ᶠ y : X in 𝓝 x, f y ≤ c
  exact hc.mono fun y hy => le_trans (hle y) hy
abbrev PositiveJointLogSpace (n : ℕ) :=
  {q : TorusCharacters.LogSpace n × ℂ //
    1 < Complex.normSq q.2}
def jointLogTime {n : ℕ}
    (q : PositiveJointLogSpace n) : ℝ :=
  Real.log (Complex.normSq q.val.2)
theorem jointLogTime_pos {n : ℕ}
    (q : PositiveJointLogSpace n) :
    0 < jointLogTime q := by
  unfold jointLogTime
  exact Real.log_pos q.property
def jointRealCoordinate {n : ℕ}
    (q : PositiveJointLogSpace n) : Space n :=
  realLogCoordinate q.val.1
theorem continuous_jointRealCoordinate (n : ℕ) :
    Continuous (jointRealCoordinate (n := n)) := by
  unfold jointRealCoordinate realLogCoordinate
  fun_prop
theorem continuous_jointLogTime (n : ℕ) :
    Continuous (jointLogTime (n := n)) := by
  unfold jointLogTime
  have hτ : Continuous
      (fun q : PositiveJointLogSpace n => q.val.2) :=
    continuous_snd.comp continuous_subtype_val
  apply (Complex.continuous_normSq.comp hτ).log
  intro q
  exact ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) q.property)
end ActualJetUpperEnvelope
namespace ActualJetPlurisubharmonicEnvelope
open Set Metric Filter Function MeasureTheory InnerProductSpace
open scoped BigOperators Topology InnerProductSpace ENNReal
def positiveJointDomain (n : ℕ) :
    Set (TorusCharacters.LogSpace n × ℂ) :=
  {q | 1 < Complex.normSq q.2}
theorem log_norm_le_circleAverage_of_differentiable
    {g : ℂ → ℂ}
    (hg : Differentiable ℂ g)
    (hzero : g 0 ≠ 0)
    (R : ℝ) :
    Real.log ‖g 0‖ ≤
      Real.circleAverage (fun w : ℂ => Real.log ‖g w‖) 0 R := by
  let G : ℂ → ℂ := fun w => g ((R : ℂ) * w)
  have hG : Differentiable ℂ G := by
    exact hg.comp (by fun_prop)
  have hGanalytic : AnalyticOnNhd ℂ G (Set.univ : Set ℂ) :=
    hG.differentiableOn.analyticOnNhd isOpen_univ
  have hGzero : G 0 ≠ 0 := by
    simpa [G] using hzero
  have hmeromorphic : Meromorphic G := by
    intro w
    exact (hG.analyticAt w).meromorphicAt
  have hdivisor :
      0 ≤ MeromorphicOn.divisor G (Set.univ : Set ℂ) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hGanalytic
  have hcount :
      0 ≤ Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor G (Set.univ : Set ℂ)) 1 :=
    Function.locallyFinsuppWithin.logCounting_nonneg
      hdivisor (by norm_num)
  have hjensen :=
    Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
      hmeromorphic (by norm_num : (1 : ℝ) ≠ 0)
  rw [(hG.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero
    hGzero] at hjensen
  have hjensen' :
      Function.locallyFinsuppWithin.logCounting
        (MeromorphicOn.divisor G (Set.univ : Set ℂ)) 1 =
        Real.circleAverage
          (fun w : ℂ => Real.log ‖G w‖) 0 1 - Real.log ‖G 0‖ := by
    simpa only [top_eq_univ] using hjensen
  have hcenter :
      Real.log ‖G 0‖ ≤
        Real.circleAverage
          (fun w : ℂ => Real.log ‖G w‖) 0 1 := by
    rw [hjensen'] at hcount
    linarith
  simpa [G, Real.circleAverage_eq_circleAverage_zero_one] using hcenter
theorem log_hilbert_norm_le_circleAverage_all_radius
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {F : ℂ → H}
    (hF : Differentiable ℂ F)
    (hzero : F 0 ≠ 0)
    (R : ℝ)
    (hcircle : ∀ w ∈ Metric.sphere (0 : ℂ) |R|, F w ≠ 0) :
    Real.log ‖F 0‖ ≤
      Real.circleAverage (fun w : ℂ => Real.log ‖F w‖) 0 R := by
  by_cases hR : R = 0
  · simp [hR]
  let g : ℂ → ℂ := fun w => inner ℂ (F 0) (F w)
  have hg : Differentiable ℂ g := by
    simpa [g, Function.comp_def, innerSL_apply_apply] using
      (innerSL ℂ (F 0)).differentiable.comp hF
  have hgzero : g 0 ≠ 0 := by
    change inner ℂ (F 0) (F 0) ≠ 0
    exact (inner_self_ne_zero (𝕜 := ℂ)).mpr hzero
  have hganalytic : AnalyticOnNhd ℂ g (Set.univ : Set ℂ) :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hglobal : ∀ᶠ w : ℂ in codiscrete ℂ, g w ≠ 0 := by
    change {w : ℂ | g w ≠ 0} ∈ codiscrete ℂ
    exact hganalytic.preimage_zero_mem_codiscrete hgzero
  have hnonzero :
      ∀ᶠ w : ℂ in codiscreteWithin (Metric.sphere (0 : ℂ) |R|),
        g w ≠ 0 := by
    exact hglobal.filter_mono
      (Filter.codiscreteWithin_mono
        (Set.subset_univ (Metric.sphere (0 : ℂ) |R|)))
  let corrected : ℂ → ℝ := fun w =>
    if g w = 0 then
      Real.log ‖F 0‖ + Real.log ‖F w‖
    else Real.log ‖g w‖
  have hcodiscrete :
      (fun w : ℂ => Real.log ‖g w‖) =ᶠ[
        codiscreteWithin (Metric.sphere (0 : ℂ) |R|)]
          corrected := by
    filter_upwards [hnonzero] with w hw
    simp [corrected, hw]
  have hgint : CircleIntegrable
      (fun w : ℂ => Real.log ‖g w‖) 0 R := by
    apply MeromorphicOn.circleIntegrable_log_norm
    intro w _
    exact (hg.analyticAt w).meromorphicAt
  have hcorrectedint : CircleIntegrable corrected 0 R :=
    CircleIntegrable.congr_codiscreteWithin hcodiscrete hgint
  have hFint : CircleIntegrable
      (fun w : ℂ => Real.log ‖F w‖) 0 R := by
    apply ContinuousOn.circleIntegrable'
    exact hF.continuous.continuousOn.norm.log fun w hw =>
      norm_ne_zero_iff.mpr (hcircle w hw)
  have hconst : CircleIntegrable
      (fun _ : ℂ => Real.log ‖F 0‖) 0 R :=
    circleIntegrable_const (Real.log ‖F 0‖) 0 R
  have hboundint : CircleIntegrable
      (fun w : ℂ => Real.log ‖F 0‖ + Real.log ‖F w‖) 0 R := by
    exact hconst.fun_add hFint
  have hpoint :
      ∀ w ∈ Metric.sphere (0 : ℂ) |R|,
        corrected w ≤ Real.log ‖F 0‖ + Real.log ‖F w‖ := by
    intro w hw
    by_cases hgw : g w = 0
    · simp [corrected, hgw]
    · simp only [corrected, hgw, ↓reduceIte]
      calc
        Real.log ‖g w‖ ≤ Real.log (‖F 0‖ * ‖F w‖) := by
          apply Real.log_le_log (norm_pos_iff.mpr hgw)
          simpa [g] using norm_inner_le_norm (F 0) (F w)
        _ = Real.log ‖F 0‖ + Real.log ‖F w‖ :=
          Real.log_mul (norm_ne_zero_iff.mpr hzero)
            (norm_ne_zero_iff.mpr (hcircle w hw))
  have hmean :
      Real.circleAverage (fun w : ℂ => Real.log ‖g w‖) 0 R ≤
        Real.log ‖F 0‖ +
          Real.circleAverage (fun w : ℂ => Real.log ‖F w‖) 0 R := by
    calc
      Real.circleAverage (fun w : ℂ => Real.log ‖g w‖) 0 R =
          Real.circleAverage corrected 0 R :=
        Real.circleAverage_congr_codiscreteWithin hcodiscrete hR
      _ ≤ Real.circleAverage
          (fun w : ℂ => Real.log ‖F 0‖ + Real.log ‖F w‖) 0 R :=
        Real.circleAverage_mono hcorrectedint hboundint hpoint
      _ = Real.log ‖F 0‖ +
          Real.circleAverage (fun w : ℂ => Real.log ‖F w‖) 0 R := by
        rw [Real.circleAverage_fun_add hconst hFint,
          Real.circleAverage_const]
  have hscalar :=
    log_norm_le_circleAverage_of_differentiable hg hgzero R
  have hcombined := hscalar.trans hmean
  have hcenter : ‖g 0‖ = ‖F 0‖ ^ 2 := by
    simp [g, inner_self_eq_norm_sq_to_K]
  rw [hcenter, Real.log_pow] at hcombined
  norm_num at hcombined
  linarith
theorem log_hilbert_norm_sq_le_circleAverage_all_radius
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {F : ℂ → H}
    (hF : Differentiable ℂ F)
    (hzero : F 0 ≠ 0)
    (R : ℝ)
    (hcircle : ∀ w ∈ Metric.sphere (0 : ℂ) |R|, F w ≠ 0) :
    Real.log (‖F 0‖ ^ 2) ≤
      Real.circleAverage
        (fun w : ℂ => Real.log (‖F w‖ ^ 2)) 0 R := by
  have h := log_hilbert_norm_le_circleAverage_all_radius
    hF hzero R hcircle
  simp_rw [Real.log_pow]
  change 2 * Real.log ‖F 0‖ ≤
    Real.circleAverage (fun w : ℂ => 2 * Real.log ‖F w‖) 0 R
  rw [show (fun w : ℂ => 2 * Real.log ‖F w‖) =
    (fun w : ℂ => (2 : ℝ) • Real.log ‖F w‖) by rfl,
    Real.circleAverage_fun_smul]
  exact mul_le_mul_of_nonneg_left h (by norm_num)
end ActualJetPlurisubharmonicEnvelope
namespace TranslatedGaussianLatticeAsymptotics
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
def roundedLatticeExponent {n : ℕ} (k : ℕ)
    (u : Space n) : Space n :=
  fun i => (⌊(k : ℝ) * u i⌋ : ℝ) / (k : ℝ)
end TranslatedGaussianLatticeAsymptotics
namespace SpatialBergmanPointwiseAsymptotics
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators
open TranslatedGaussianLatticeAsymptotics
theorem zero_mem_monomialIndex_all_weights {n : ℕ}
    (K : CenteredBody n) (k : ℕ) :
    (0 : Space n) ∈
      LatticeAsymptotics.monomialIndex K k := by
  refine ⟨LatticeAsymptotics.zero_mem_interior K, ?_⟩
  unfold LatticeAsymptotics.scaledIntegerLattice
  exact Set.zero_mem_smul_set (Submodule.zero_mem _)
def nearestMonomialIndex {n : ℕ}
    (K : CenteredBody n)
    (u : Space n) (k : ℕ) :
    LatticeAsymptotics.monomialIndex K k := by
  classical
  exact
    if h : roundedLatticeExponent k u ∈
        LatticeAsymptotics.monomialIndex K k then
      ⟨roundedLatticeExponent k u, h⟩
    else
      ⟨0, zero_mem_monomialIndex_all_weights K k⟩
end SpatialBergmanPointwiseAsymptotics
namespace WeightedPoincare
open Set MeasureTheory Matrix
open scoped BigOperators ENNReal InnerProductSpace
def partition {n : ℕ} (a : Space n → ℝ) : ℝ :=
  ∫ x : Space n, Real.exp (-a x)
    ∂(volume : Measure (Space n))
def normalizedDensity {n : ℕ}
    (a : Space n → ℝ) (x : Space n) : ℝ :=
  Real.exp (-a x) / partition a
def normalizedMeasure {n : ℕ}
    (a : Space n → ℝ) : Measure (Space n) :=
  (volume : Measure (Space n)).withDensity
    (fun x => ENNReal.ofReal (normalizedDensity a x))
theorem partition_pos {n : ℕ} {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    0 < partition a := by
  exact MeasureTheory.integral_exp_pos ha
theorem normalizedDensity_pos {n : ℕ} {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) (x : Space n) :
    0 < normalizedDensity a x := by
  exact div_pos (Real.exp_pos _) (partition_pos ha)
theorem normalizedDensity_integrable {n : ℕ}
    {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    Integrable (normalizedDensity a)
      (volume : Measure (Space n)) := by
  exact ha.div_const _
theorem integral_normalizedDensity {n : ℕ}
    {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    (∫ x : Space n, normalizedDensity a x
      ∂(volume : Measure (Space n))) = 1 := by
  unfold normalizedDensity
  rw [MeasureTheory.integral_div]
  exact div_self (partition_pos ha).ne'
theorem normalizedMeasure_univ {n : ℕ}
    {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    normalizedMeasure a Set.univ = 1 := by
  unfold normalizedMeasure
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (normalizedDensity_integrable ha)
    (Filter.Eventually.of_forall
      (fun x => (normalizedDensity_pos ha x).le)),
    integral_normalizedDensity ha]
  exact ENNReal.ofReal_one
theorem normalizedMeasure_isProbability {n : ℕ}
    {a : Space n → ℝ}
    (ha : Integrable (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n))) :
    IsProbabilityMeasure (normalizedMeasure a) :=
  ⟨normalizedMeasure_univ ha⟩
def coordinateGradient {n : ℕ}
    (f : Space n → ℝ)
    (x : Space n) : Space n :=
  fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))
end WeightedPoincare
namespace SpatialBergmanFatouScheffe
open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators ENNReal
def actualGradient {n : ℕ}
    (φ : Space n → ℝ)
    (x : Space n) : Space n :=
  MonomialDivergence.dualVector (fderiv ℝ φ x)
theorem pairing_actualGradient_eq_fderiv {n : ℕ}
    (φ : Space n → ℝ)
    (x v : Space n) :
    SupportFunction.pairing (actualGradient φ x) v =
      (fderiv ℝ φ x) v := by
  calc
    SupportFunction.pairing (actualGradient φ x) v =
        SupportFunction.pairing v (actualGradient φ x) := by
          simp [SupportFunction.pairing, mul_comm]
    _ = (fderiv ℝ φ x) v := by
          exact (MonomialDivergence.dual_apply_eq_pairing
            (fderiv ℝ φ x) v).symm
end SpatialBergmanFatouScheffe
namespace MomentExistence
open Set Function Filter MeasureTheory
open ArbitraryBodySmoothConvexPotentialBridge LaplaceAsymptotics
open scoped BigOperators ENNReal Topology
structure SourceMomentPotential {n : ℕ}
    (K : CenteredBody n) where
  potential : Space n → ℝ
  smooth : ContDiff ℝ 2 potential
  convex : ConvexOn ℝ Set.univ potential
  supportError : ℝ
  supportBound : ∀ x : Space n,
    |potential x -
      SupportFunction.supportFunction K.carrier x| ≤
        supportError
def canonicalSourceMomentPotential {n : ℕ}
    (K : CenteredBody n) : SourceMomentPotential K where
  potential := smoothConvexPotential K
  smooth := (smoothConvexPotential_contDiff K).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  convex := smoothConvexPotential_convex K
  supportError := 1
  supportBound := smoothConvexPotential_bounded K
theorem sourceMomentDensity_integrable {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    Integrable
      (fun x : Space n => Real.exp (-D.potential x))
      (volume : Measure (Space n)) := by
  have h := MonomialIntegrability.integrable_monomialWeight_of_bounded_support
    K.compact (LatticeAsymptotics.zero_mem_interior K)
    D.smooth.continuous D.supportBound
    (k := (1 : ℝ)) (by norm_num)
  change Integrable
    (fun x : Space n =>
      Real.exp (1 *
        (SupportFunction.pairing
          (0 : Space n) x - D.potential x)))
    (volume : Measure (Space n)) at h
  simpa [SupportFunction.pairing] using h
theorem sourceMomentDensity_integral_pos {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 < (∫ x : Space n,
      Real.exp (-D.potential x)
      ∂(volume : Measure (Space n))) := by
  have h := MonomialIntegrability.monomialIntegral_pos_of_bounded_support
    K.compact (LatticeAsymptotics.zero_mem_interior K)
    D.smooth.continuous D.supportBound
    (k := (1 : ℝ)) (by norm_num)
  simpa [MonomialIntegrability.monomialIntegral,
    MonomialIntegrability.monomialWeight,
    SupportFunction.pairing] using h
theorem sourceMomentPhase_le_supportError {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier)
    (x : Space n) :
    phase p D.potential x ≤ D.supportError := by
  have hs := SupportFunction.pairing_le_supportFunction
    K.compact hp x
  have hb := (abs_le.mp (D.supportBound x)).1
  unfold phase
  linarith
theorem sourceMomentPhase_bddAbove {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier) :
    BddAbove (Set.range (phase p D.potential)) := by
  refine ⟨D.supportError, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact sourceMomentPhase_le_supportError D hp x
theorem sourceMomentLegendre_le_supportError {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier) :
    legendreTransform D.potential p ≤ D.supportError := by
  unfold legendreTransform
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact sourceMomentPhase_le_supportError D hp x
theorem neg_sourceMomentPotential_zero_le_legendre {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier) :
    -D.potential 0 ≤ legendreTransform D.potential p := by
  have h := le_csSup (sourceMomentPhase_bddAbove D hp)
    (show phase p D.potential 0 ∈
      Set.range (phase p D.potential) from ⟨0, rfl⟩)
  simpa [legendreTransform, phase,
    SupportFunction.pairing] using h
theorem abs_sourceMomentLegendre_le {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ K.carrier) :
    |legendreTransform D.potential p| ≤
      max D.supportError |D.potential 0| := by
  apply abs_le.mpr
  constructor
  · have hlow := neg_sourceMomentPotential_zero_le_legendre D hp
    have hφ := (le_abs_self (D.potential 0)).trans
      (le_max_right D.supportError |D.potential 0|)
    linarith
  · exact (sourceMomentLegendre_le_supportError D hp).trans
      (le_max_left D.supportError |D.potential 0|)
theorem convexOn_sourceMomentLegendre {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    ConvexOn ℝ K.carrier (legendreTransform D.potential) := by
  refine ⟨K.convex, ?_⟩
  intro p hp q hq a b ha hb hab
  unfold legendreTransform
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  have hpmax : phase p D.potential x ≤
      sSup (Set.range (phase p D.potential)) :=
    le_csSup (sourceMomentPhase_bddAbove D hp) ⟨x, rfl⟩
  have hqmax : phase q D.potential x ≤
      sSup (Set.range (phase q D.potential)) :=
    le_csSup (sourceMomentPhase_bddAbove D hq) ⟨x, rfl⟩
  have hphase :
      phase (a • p + b • q) D.potential x =
        a * phase p D.potential x +
          b * phase q D.potential x := by
    have hpull :
        (∑ i : Fin n, (a * p i) * x i) =
          a * ∑ i : Fin n, p i * x i := by
      simp [Finset.mul_sum, mul_assoc]
    have hqpull :
        (∑ i : Fin n, (b * q i) * x i) =
          b * ∑ i : Fin n, q i * x i := by
      simp [Finset.mul_sum, mul_assoc]
    simp only [phase, SupportFunction.pairing,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib]
    rw [hpull, hqpull]
    linear_combination D.potential x * hab
  rw [hphase]
  simpa [smul_eq_mul] using
    add_le_add (mul_le_mul_of_nonneg_left hpmax ha)
      (mul_le_mul_of_nonneg_left hqmax hb)
theorem continuousOn_sourceMomentLegendre_interior {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    ContinuousOn (legendreTransform D.potential)
      (interior K.carrier) :=
  (convexOn_sourceMomentLegendre D).continuousOn_interior
end MomentExistence
namespace MomentPotentialExistence
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence
open scoped BigOperators ENNReal Topology
theorem sourceMomentLegendre_aestronglyMeasurable_restrict
    {n : ℕ} {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    AEStronglyMeasurable
      (legendreTransform D.potential)
      ((volume : Measure (Space n)).restrict K.carrier) := by
  have hrestrict :
      (volume : Measure (Space n)).restrict
        (interior K.carrier) =
      (volume : Measure (Space n)).restrict K.carrier :=
    Measure.restrict_congr_set
      (interior_ae_eq_of_null_frontier
        (K.convex.addHaar_frontier
          (volume : Measure (Space n))))
  rw [← hrestrict]
  exact ContinuousOn.aestronglyMeasurable
    (continuousOn_sourceMomentLegendre_interior D)
    isOpen_interior.measurableSet
theorem sourceMomentLegendre_integrableOn
    {n : ℕ} {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    IntegrableOn
      (legendreTransform D.potential)
      K.carrier (volume : Measure (Space n)) := by
  let B : ℝ := max D.supportError |D.potential 0|
  have hconst : Integrable
      (fun _ : Space n => B)
      ((volume : Measure (Space n)).restrict K.carrier) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  apply hconst.mono'
    (sourceMomentLegendre_aestronglyMeasurable_restrict D)
  filter_upwards [MeasureTheory.ae_restrict_mem
    K.compact.measurableSet] with p hp
  simpa [Real.norm_eq_abs, B] using
    abs_sourceMomentLegendre_le D hp
def sourceMomentPartition {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  ∫ x : Space n,
    Real.exp (-D.potential x)
    ∂(volume : Measure (Space n))
theorem sourceMomentPartition_pos {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 < sourceMomentPartition D :=
  sourceMomentDensity_integral_pos D
def sourceMomentBodyEnergy {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  (normalizedVolume K.carrier)⁻¹ *
    (∫ p in K.carrier,
      legendreTransform D.potential p
      ∂(volume : Measure (Space n)))
def sourceMomentBermanFunctional {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  Real.log (sourceMomentPartition D) -
    sourceMomentBodyEnergy D
theorem exists_sourceMomentLegendre_maximizer
    {n : ℕ} {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n} (hp : p ∈ interior K.carrier) :
    ∃ x : Space n,
      phase p D.potential x =
        legendreTransform D.potential p ∧
      ∀ z : Space n,
        phase p D.potential z ≤ phase p D.potential x :=
  LaplaceAsymptotics.exists_legendre_maximizer
    K.compact hp D.smooth.continuous D.supportBound
end MomentPotentialExistence
namespace MomentMinimizer
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence
open scoped BigOperators ENNReal NNReal Topology
def sourceBodyLipschitzConstant {n : ℕ}
    (K : CenteredBody n) : ℝ≥0 :=
  Real.toNNReal ((n : ℝ) *
    LaurentJetSeparatedness.bodyRadius K)
def normalizedSourcePointwiseFamily {n : ℕ}
    (K : CenteredBody n) : Set (Space n → ℝ) :=
  {f | f 0 = 0 ∧
    ∀ x y : Space n,
      dist (f x) (f y) ≤
        (sourceBodyLipschitzConstant K : ℝ) * dist x y}
theorem isClosed_normalizedSourcePointwiseFamily {n : ℕ}
    (K : CenteredBody n) :
    IsClosed (normalizedSourcePointwiseFamily K) := by
  have hzero : IsClosed
      {f : Space n → ℝ | f 0 = 0} :=
    isClosed_eq (continuous_apply 0) continuous_const
  have hpair (x y : Space n) : IsClosed
      {f : Space n → ℝ |
        dist (f x) (f y) ≤
          (sourceBodyLipschitzConstant K : ℝ) * dist x y} :=
    isClosed_le ((continuous_apply x).dist (continuous_apply y))
      continuous_const
  have hforall : IsClosed
      {f : Space n → ℝ |
        ∀ x y : Space n,
          dist (f x) (f y) ≤
            (sourceBodyLipschitzConstant K : ℝ) * dist x y} := by
    have heq :
        {f : Space n → ℝ |
          ∀ x y : Space n,
            dist (f x) (f y) ≤
              (sourceBodyLipschitzConstant K : ℝ) * dist x y} =
          ⋂ x : Space n, ⋂ y : Space n,
            {f : Space n → ℝ |
              dist (f x) (f y) ≤
                (sourceBodyLipschitzConstant K : ℝ) * dist x y} := by
      ext f
      simp
    rw [heq]
    exact isClosed_iInter fun x => isClosed_iInter fun y => hpair x y
  exact hzero.inter hforall
theorem isCompact_normalizedSourcePointwiseFamily {n : ℕ}
    (K : CenteredBody n) :
    IsCompact (normalizedSourcePointwiseFamily K) := by
  let Q : Space n → Set ℝ := fun x =>
    Metric.closedBall 0
      ((sourceBodyLipschitzConstant K : ℝ) * dist x 0)
  have hQ : IsCompact (Set.univ.pi Q) :=
    isCompact_univ_pi (fun x => by
      simpa [Q] using
        (isCompact_closedBall (0 : ℝ)
          ((sourceBodyLipschitzConstant K : ℝ) * dist x 0)))
  refine IsCompact.of_isClosed_subset hQ
    (isClosed_normalizedSourcePointwiseFamily K) ?_
  intro f hf
  rw [Set.mem_pi]
  intro x _
  change dist (f x) 0 ≤
    (sourceBodyLipschitzConstant K : ℝ) * dist x 0
  simpa [hf.1] using hf.2 x 0
def normalizedSourceContinuousFamily {n : ℕ}
    (K : CenteredBody n) :
    Set C(Space n, ℝ) :=
  {f | f 0 = 0 ∧
    LipschitzWith (sourceBodyLipschitzConstant K) f}
theorem normalizedSourceContinuousFamily_image {n : ℕ}
    (K : CenteredBody n) :
    ContinuousMap.toFun '' normalizedSourceContinuousFamily K =
      normalizedSourcePointwiseFamily K := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨hg.1, fun x y => hg.2.dist_le_mul x y⟩
  · intro hf
    have hlip : LipschitzWith (sourceBodyLipschitzConstant K) f :=
      LipschitzWith.of_dist_le_mul hf.2
    let g : C(Space n, ℝ) := ⟨f, hlip.continuous⟩
    exact ⟨g, ⟨hf.1, hlip⟩, rfl⟩
theorem equicontinuous_normalizedSourceContinuousFamily {n : ℕ}
    (K : CenteredBody n) :
    Equicontinuous
      ((↑) : normalizedSourceContinuousFamily K →
        Space n → ℝ) := by
  apply Metric.equicontinuous_of_continuity_modulus
    (fun t : ℝ => (sourceBodyLipschitzConstant K : ℝ) * t)
    (by
      have hcontinuous : Continuous
          (fun t : ℝ => (sourceBodyLipschitzConstant K : ℝ) * t) := by
        fun_prop
      simpa only [mul_zero] using hcontinuous.tendsto (0 : ℝ))
  intro x y f
  exact f.property.2.dist_le_mul x y
theorem isCompact_normalizedSourceContinuousFamily {n : ℕ}
    (K : CenteredBody n) :
    IsCompact (normalizedSourceContinuousFamily K) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
    (normalizedSourceContinuousFamily K)
  · rw [normalizedSourceContinuousFamily_image]
    exact isCompact_normalizedSourcePointwiseFamily K
  · exact equicontinuous_normalizedSourceContinuousFamily K
theorem sourceMomentBodyFenchel_le {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier)
    (x : Space n) :
    SupportFunction.pairing p x -
        legendreTransform D.potential p ≤
      D.potential x := by
  have h := le_csSup (sourceMomentPhase_bddAbove D hp)
    (show phase p D.potential x ∈
      Set.range (phase p D.potential) from ⟨x, rfl⟩)
  change SupportFunction.pairing p x - D.potential x ≤
    legendreTransform D.potential p at h
  linarith
end MomentMinimizer
namespace MomentCoercivityCompactness
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentMinimizer
open scoped BigOperators ENNReal NNReal Topology
def sourceMomentMinimumPoint {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : Space n :=
  (exists_sourceMomentLegendre_maximizer D
    (LatticeAsymptotics.zero_mem_interior K)).choose
theorem sourceMomentMinimumPoint_le {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (x : Space n) :
    D.potential (sourceMomentMinimumPoint D) ≤ D.potential x := by
  have h :=
    (exists_sourceMomentLegendre_maximizer D
      (LatticeAsymptotics.zero_mem_interior K)).choose_spec.2 x
  simpa [sourceMomentMinimumPoint, phase,
    SupportFunction.pairing] using h
def minimumNormalizedSourceContinuousMap {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    C(Space n, ℝ) where
  toFun x :=
    D.potential (x + sourceMomentMinimumPoint D) -
      D.potential (sourceMomentMinimumPoint D)
  continuous_toFun :=
    (D.smooth.continuous.comp
      (continuous_id.add continuous_const)).sub continuous_const
theorem minimumNormalizedSourceContinuousMap_zero {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    minimumNormalizedSourceContinuousMap D 0 = 0 := by
  simp [minimumNormalizedSourceContinuousMap]
theorem minimumNormalizedSourceContinuousMap_nonneg {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (x : Space n) :
    0 ≤ minimumNormalizedSourceContinuousMap D x := by
  change 0 ≤ D.potential (x + sourceMomentMinimumPoint D) -
    D.potential (sourceMomentMinimumPoint D)
  exact sub_nonneg.mpr
    (sourceMomentMinimumPoint_le D
      (x + sourceMomentMinimumPoint D))
theorem minimumNormalizedSourceContinuousMap_le_support {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (x : Space n) :
    minimumNormalizedSourceContinuousMap D x ≤
      SupportFunction.supportFunction K.carrier x := by
  have h :=
    GlobalBergmanKernelBound.convex_supportCompatible_sub_le_support
      K D.convex D.supportBound
      (x + sourceMomentMinimumPoint D)
      (sourceMomentMinimumPoint D)
  simpa [minimumNormalizedSourceContinuousMap] using h
theorem convexOn_minimumNormalizedSourceContinuousMap {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    ConvexOn ℝ Set.univ (minimumNormalizedSourceContinuousMap D) := by
  let z := sourceMomentMinimumPoint D
  change ConvexOn ℝ Set.univ
    (fun x => D.potential (x + z) - D.potential z)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcombo :
      a • (x + z) + b • (y + z) =
        (a • x + b • y) + z := by
    calc
      a • (x + z) + b • (y + z) =
          (a • x + b • y) + (a • z + b • z) := by
        rw [smul_add, smul_add]
        abel
      _ = (a • x + b • y) + z := by
        rw [← add_smul, hab, one_smul]
  have h := D.convex.2 (Set.mem_univ (x + z))
    (Set.mem_univ (y + z)) ha hb hab
  rw [hcombo] at h
  change D.potential ((a • x + b • y) + z) ≤
    a * D.potential (x + z) + b * D.potential (y + z) at h
  change D.potential ((a • x + b • y) + z) - D.potential z ≤
    a * (D.potential (x + z) - D.potential z) +
      b * (D.potential (y + z) - D.potential z)
  calc
    D.potential ((a • x + b • y) + z) - D.potential z ≤
        (a * D.potential (x + z) +
          b * D.potential (y + z)) - D.potential z :=
      sub_le_sub_right h _
    _ = (a * D.potential (x + z) +
          b * D.potential (y + z)) - (a + b) * D.potential z := by
      simp [hab]
    _ = a * (D.potential (x + z) - D.potential z) +
          b * (D.potential (y + z) - D.potential z) := by
      ring
theorem minimumNormalizedSourceContinuousMap_lipschitz {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (minimumNormalizedSourceContinuousMap D) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hD :=
    GlobalBergmanKernelBound.convex_supportCompatible_lipschitz
      K D.convex D.supportBound
  simpa [minimumNormalizedSourceContinuousMap,
    sourceBodyLipschitzConstant, Real.dist_eq] using
    hD.dist_le_mul
      (x + sourceMomentMinimumPoint D)
      (y + sourceMomentMinimumPoint D)
theorem minimumNormalizedSourceContinuousMap_mem {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    minimumNormalizedSourceContinuousMap D ∈
      normalizedSourceContinuousFamily K :=
  ⟨minimumNormalizedSourceContinuousMap_zero D,
    minimumNormalizedSourceContinuousMap_lipschitz D⟩
theorem convexOn_of_tendsto_minimumNormalizedSourceContinuousMap
    {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f)) :
    ConvexOn ℝ Set.univ f := by
  have hpoint (x : Space n) :
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)) x)
        atTop (𝓝 (f x)) :=
    (continuous_eval_const x).continuousAt.tendsto.comp hconv
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  apply le_of_tendsto_of_tendsto
    (hpoint (a • x + b • y))
    ((hpoint x).const_mul a |>.add ((hpoint y).const_mul b))
  filter_upwards with j
  simpa only [smul_eq_mul] using
    (convexOn_minimumNormalizedSourceContinuousMap (D (φ j))).2
      (Set.mem_univ x) (Set.mem_univ y) ha hb hab
theorem exists_minimumNormalizedSourceConvex_subsequence {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K) :
    ∃ (f : C(Space n, ℝ))
      (φ : ℕ → ℕ),
      f 0 = 0 ∧
      LipschitzWith (sourceBodyLipschitzConstant K) f ∧
      ConvexOn ℝ Set.univ f ∧
      (∀ x : Space n,
        0 ≤ f x ∧
          f x ≤ SupportFunction.supportFunction K.carrier x) ∧
      StrictMono φ ∧
      Tendsto (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
        atTop (𝓝 f) := by
  obtain ⟨f, hf, φ, hφ, hconv⟩ :=
    (isCompact_normalizedSourceContinuousFamily K).tendsto_subseq
      (x := fun j => minimumNormalizedSourceContinuousMap (D j))
      (fun j => minimumNormalizedSourceContinuousMap_mem (D j))
  refine ⟨f, φ, hf.1, hf.2,
    convexOn_of_tendsto_minimumNormalizedSourceContinuousMap
      D φ f hconv, ?_, hφ, hconv⟩
  intro x
  have hpoint :
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)) x)
        atTop (𝓝 (f x)) :=
    (continuous_eval_const x).continuousAt.tendsto.comp hconv
  constructor
  · exact ge_of_tendsto hpoint
      (Eventually.of_forall fun j =>
        minimumNormalizedSourceContinuousMap_nonneg (D (φ j)) x)
  · exact le_of_tendsto hpoint
      (Eventually.of_forall fun j =>
        minimumNormalizedSourceContinuousMap_le_support (D (φ j)) x)
theorem sourceCenteredBody_setIntegral_id_eq_zero {n : ℕ}
    (K : CenteredBody n) :
    (∫ p in K.carrier, p
      ∂(volume : Measure (Space n))) = 0 := by
  have hcenter :
      (normalizedVolume K.carrier)⁻¹ •
        (∫ p in K.carrier, p
          ∂(volume : Measure (Space n))) = 0 := by
    simpa [barycenter] using K.centered
  exact (smul_eq_zero.mp hcenter).resolve_left
    (inv_ne_zero K.volume_pos.ne')
def sourcePairingContinuousLinear {n : ℕ}
    (x : Space n) : Space n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (BergmanAsymptotics.pairingLinear x)
theorem sourcePairingContinuousLinear_apply {n : ℕ}
    (x p : Space n) :
    sourcePairingContinuousLinear x p =
      SupportFunction.pairing p x := by
  change SupportFunction.pairing x p =
    SupportFunction.pairing p x
  simp [SupportFunction.pairing, mul_comm]
theorem sourceCenteredBody_pairing_integrableOn {n : ℕ}
    (K : CenteredBody n)
    (x : Space n) :
    IntegrableOn
      (fun p : Space n =>
        SupportFunction.pairing p x)
      K.carrier (volume : Measure (Space n)) := by
  simpa only [← sourcePairingContinuousLinear_apply] using
    (sourcePairingContinuousLinear x).continuous.continuousOn.integrableOn_compact
      K.compact
theorem sourceCenteredBody_setIntegral_pairing_eq_zero {n : ℕ}
    (K : CenteredBody n)
    (x : Space n) :
    (∫ p in K.carrier,
      SupportFunction.pairing p x
      ∂(volume : Measure (Space n))) = 0 := by
  let L := sourcePairingContinuousLinear x
  have hid : IntegrableOn
      (fun p : Space n => p)
      K.carrier (volume : Measure (Space n)) :=
    continuous_id.continuousOn.integrableOn_compact K.compact
  calc
    (∫ p in K.carrier,
      SupportFunction.pairing p x
      ∂(volume : Measure (Space n))) =
        ∫ p in K.carrier, L p
          ∂(volume : Measure (Space n)) := by
            apply integral_congr_ae
            filter_upwards with p
            exact (sourcePairingContinuousLinear_apply x p).symm
    _ = L (∫ p in K.carrier, p
          ∂(volume : Measure (Space n))) :=
        L.integral_comp_comm hid
    _ = 0 := by
      rw [sourceCenteredBody_setIntegral_id_eq_zero]
      exact map_zero L
def minimumNormalizedSourceBodyDual {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (p : Space n) : ℝ :=
  legendreTransform D.potential p -
    SupportFunction.pairing p
      (sourceMomentMinimumPoint D) +
    D.potential (sourceMomentMinimumPoint D)
theorem minimumNormalizedSource_phase {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    (p x : Space n) :
    phase p (minimumNormalizedSourceContinuousMap D) x =
      phase p D.potential
        (x + sourceMomentMinimumPoint D) -
      SupportFunction.pairing p
        (sourceMomentMinimumPoint D) +
      D.potential (sourceMomentMinimumPoint D) := by
  change
    SupportFunction.pairing p x -
        (D.potential (x + sourceMomentMinimumPoint D) -
          D.potential (sourceMomentMinimumPoint D)) =
      (SupportFunction.pairing p
          (x + sourceMomentMinimumPoint D) -
        D.potential (x + sourceMomentMinimumPoint D)) -
      SupportFunction.pairing p
        (sourceMomentMinimumPoint D) +
      D.potential (sourceMomentMinimumPoint D)
  rw [MonomialDivergence.pairing_add_right]
  ring
theorem minimumNormalizedSourcePhase_bddAbove {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier) :
    BddAbove
      (Set.range (phase p (minimumNormalizedSourceContinuousMap D))) := by
  refine ⟨D.supportError -
    SupportFunction.pairing p
      (sourceMomentMinimumPoint D) +
    D.potential (sourceMomentMinimumPoint D), ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [minimumNormalizedSource_phase]
  linarith [sourceMomentPhase_le_supportError D hp
    (x + sourceMomentMinimumPoint D)]
theorem minimumNormalizedSourceBodyDual_eq_legendre {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier) :
    minimumNormalizedSourceBodyDual D p =
      legendreTransform (minimumNormalizedSourceContinuousMap D) p := by
  apply le_antisymm
  · have hbdd := minimumNormalizedSourcePhase_bddAbove D hp
    have hupper :
        legendreTransform D.potential p ≤
          legendreTransform
              (minimumNormalizedSourceContinuousMap D) p +
            SupportFunction.pairing p
              (sourceMomentMinimumPoint D) -
            D.potential (sourceMomentMinimumPoint D) := by
      unfold legendreTransform
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨y, rfl⟩
      have h := le_csSup hbdd
        (show
          phase p (minimumNormalizedSourceContinuousMap D)
              (y - sourceMomentMinimumPoint D) ∈
            Set.range
              (phase p (minimumNormalizedSourceContinuousMap D))
          from ⟨y - sourceMomentMinimumPoint D, rfl⟩)
      rw [minimumNormalizedSource_phase] at h
      simp only [sub_add_cancel] at h
      linarith
    unfold minimumNormalizedSourceBodyDual
    linarith
  · change
      sSup (Set.range
        (phase p (minimumNormalizedSourceContinuousMap D))) ≤
        minimumNormalizedSourceBodyDual D p
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    rw [minimumNormalizedSource_phase]
    have h := le_csSup (sourceMomentPhase_bddAbove D hp)
      (show
        phase p D.potential
            (x + sourceMomentMinimumPoint D) ∈
          Set.range (phase p D.potential)
        from ⟨x + sourceMomentMinimumPoint D, rfl⟩)
    change
      phase p D.potential
          (x + sourceMomentMinimumPoint D) ≤
        legendreTransform D.potential p at h
    unfold minimumNormalizedSourceBodyDual
    linarith
theorem minimumNormalizedSourceBodyDual_nonneg {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier) :
    0 ≤ minimumNormalizedSourceBodyDual D p := by
  have h := sourceMomentBodyFenchel_le D hp
    (sourceMomentMinimumPoint D)
  unfold minimumNormalizedSourceBodyDual
  linarith
theorem minimumNormalizedSourceBodyDual_integrableOn {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    IntegrableOn (minimumNormalizedSourceBodyDual D)
      K.carrier (volume : Measure (Space n)) := by
  have hleg := sourceMomentLegendre_integrableOn D
  have hpair := sourceCenteredBody_pairing_integrableOn K
    (sourceMomentMinimumPoint D)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        D.potential (sourceMomentMinimumPoint D))
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  exact (hleg.sub hpair).add hconst
theorem minimumNormalizedSourceBodyDual_setIntegral {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
      ∂(volume : Measure (Space n))) =
      (∫ p in K.carrier, legendreTransform D.potential p
        ∂(volume : Measure (Space n))) +
      normalizedVolume K.carrier *
        D.potential (sourceMomentMinimumPoint D) := by
  have hleg := sourceMomentLegendre_integrableOn D
  have hpair := sourceCenteredBody_pairing_integrableOn K
    (sourceMomentMinimumPoint D)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        D.potential (sourceMomentMinimumPoint D))
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  calc
    (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
      ∂(volume : Measure (Space n))) =
        (∫ p in K.carrier,
          legendreTransform D.potential p -
            SupportFunction.pairing p
              (sourceMomentMinimumPoint D)
          ∂(volume : Measure (Space n))) +
        (∫ _p in K.carrier,
          D.potential (sourceMomentMinimumPoint D)
          ∂(volume : Measure (Space n))) := by
            simpa [minimumNormalizedSourceBodyDual] using
              MeasureTheory.integral_add (hleg.sub hpair) hconst
    _ = (∫ p in K.carrier, legendreTransform D.potential p
          ∂(volume : Measure (Space n))) +
        normalizedVolume K.carrier *
          D.potential (sourceMomentMinimumPoint D) := by
            rw [MeasureTheory.integral_sub hleg hpair,
              sourceCenteredBody_setIntegral_pairing_eq_zero,
              MeasureTheory.setIntegral_const]
            simp [normalizedVolume, measureReal_def,
              smul_eq_mul]
theorem minimumNormalizedSourceBodyDual_energy {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    (normalizedVolume K.carrier)⁻¹ *
      (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
        ∂(volume : Measure (Space n))) =
      sourceMomentBodyEnergy D +
        D.potential (sourceMomentMinimumPoint D) := by
  rw [minimumNormalizedSourceBodyDual_setIntegral]
  unfold sourceMomentBodyEnergy
  have hvol := K.volume_pos.ne'
  field_simp
theorem sourceMomentBodyEnergy_add_minimum_nonneg {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 ≤ sourceMomentBodyEnergy D +
      D.potential (sourceMomentMinimumPoint D) := by
  rw [← minimumNormalizedSourceBodyDual_energy]
  exact mul_nonneg
    (inv_nonneg.mpr K.volume_pos.le)
    (MeasureTheory.setIntegral_nonneg K.compact.measurableSet
      (fun p hp => minimumNormalizedSourceBodyDual_nonneg D hp))
end MomentCoercivityCompactness
namespace MomentFunctionalCoercivity
open Set Function Filter MeasureTheory TopologicalSpace
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentMinimizer
open MomentCoercivityCompactness
open scoped BigOperators ENNReal NNReal Topology
def sourceExtendedBodyLegendre {n : ℕ}
    (f : C(Space n, ℝ))
    (p : Space n) : ℝ≥0∞ :=
  ⨆ j : ℕ,
    ENNReal.ofReal
      (phase p f (TopologicalSpace.denseSeq (Space n) j))
theorem measurable_sourceExtendedBodyLegendre {n : ℕ}
    (f : C(Space n, ℝ)) :
    Measurable (sourceExtendedBodyLegendre f) := by
  unfold sourceExtendedBodyLegendre
  apply Measurable.iSup
  intro j
  have hcontinuous : Continuous
      (fun p : Space n =>
        phase p f (TopologicalSpace.denseSeq (Space n) j)) := by
    unfold phase
    simp_rw [← sourcePairingContinuousLinear_apply]
    exact (sourcePairingContinuousLinear
      (TopologicalSpace.denseSeq (Space n) j)).continuous.fun_sub
        continuous_const
  exact hcontinuous.measurable.ennreal_ofReal
theorem ofReal_phase_le_sourceExtendedBodyLegendre {n : ℕ}
    (f : C(Space n, ℝ))
    (p x : Space n) :
    ENNReal.ofReal (phase p f x) ≤
      sourceExtendedBodyLegendre f p := by
  refine (TopologicalSpace.denseRange_denseSeq
    (Space n)).induction_on x ?_ ?_
  · exact isClosed_le
      (ENNReal.continuous_ofReal.comp
        (continuous_phase p f.continuous))
      continuous_const
  · intro j
    exact le_iSup
      (fun k : ℕ =>
        ENNReal.ofReal
          (phase p f
            (TopologicalSpace.denseSeq (Space n) k))) j
theorem sourceExtendedBodyLegendre_eq_of_bddAbove {n : ℕ}
    (f : C(Space n, ℝ))
    (p : Space n)
    (hbdd : BddAbove (Set.range (phase p f))) :
    sourceExtendedBodyLegendre f p =
      ENNReal.ofReal (legendreTransform f p) := by
  apply le_antisymm
  · unfold sourceExtendedBodyLegendre
    apply iSup_le
    intro j
    apply ENNReal.ofReal_le_ofReal
    exact le_csSup hbdd
      ⟨TopologicalSpace.denseSeq (Space n) j, rfl⟩
  · by_cases htop : sourceExtendedBodyLegendre f p = ⊤
    · simp [htop]
    · have hreal :
          legendreTransform f p ≤
            (sourceExtendedBodyLegendre f p).toReal := by
        unfold legendreTransform
        apply csSup_le (Set.range_nonempty _)
        rintro _ ⟨x, rfl⟩
        apply (ENNReal.ofReal_le_ofReal_iff
          ENNReal.toReal_nonneg).mp
        rw [ENNReal.ofReal_toReal htop]
        exact ofReal_phase_le_sourceExtendedBodyLegendre f p x
      simpa [ENNReal.ofReal_toReal htop] using
        ENNReal.ofReal_le_ofReal hreal
theorem sourceExtendedBodyLegendre_limit_le_liminf {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f))
    {p : Space n}
    (hp : p ∈ K.carrier) :
    sourceExtendedBodyLegendre f p ≤
      Filter.liminf
        (fun j => ENNReal.ofReal
          (minimumNormalizedSourceBodyDual (D (φ j)) p))
        atTop := by
  unfold sourceExtendedBodyLegendre
  apply iSup_le
  intro k
  let q : Space n :=
    TopologicalSpace.denseSeq (Space n) k
  have hpoint :
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)) q)
        atTop (𝓝 (f q)) :=
    (continuous_eval_const q).continuousAt.tendsto.comp hconv
  have hphase :
      Tendsto
        (fun j => phase p
          (minimumNormalizedSourceContinuousMap (D (φ j))) q)
        atTop (𝓝 (phase p f q)) := by
    simpa only [phase] using
      (tendsto_const_nhds.sub hpoint)
  have hphaseENN :
      Tendsto
        (fun j => ENNReal.ofReal
          (phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q))
        atTop (𝓝 (ENNReal.ofReal (phase p f q))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hphase
  have hmono :
      Filter.liminf
          (fun j => ENNReal.ofReal
            (phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q))
          atTop ≤
        Filter.liminf
          (fun j => ENNReal.ofReal
            (minimumNormalizedSourceBodyDual (D (φ j)) p))
          atTop := by
    have hpointle : ∀ j : ℕ,
        ENNReal.ofReal
            (phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q) ≤
          ENNReal.ofReal
            (minimumNormalizedSourceBodyDual (D (φ j)) p) := by
      intro j
      apply ENNReal.ofReal_le_ofReal
      have h := le_csSup
        (minimumNormalizedSourcePhase_bddAbove (D (φ j)) hp)
        (show
          phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q ∈
            Set.range
              (phase p (minimumNormalizedSourceContinuousMap (D (φ j))))
          from ⟨q, rfl⟩)
      change
        phase p (minimumNormalizedSourceContinuousMap (D (φ j))) q ≤
          legendreTransform
            (minimumNormalizedSourceContinuousMap (D (φ j))) p at h
      rwa [← minimumNormalizedSourceBodyDual_eq_legendre (D (φ j)) hp]
        at h
    exact Filter.liminf_le_liminf (Eventually.of_forall hpointle)
  simpa only [q, hphaseENN.liminf_eq] using hmono
theorem sourceExtendedBodyLegendre_lintegral_le_liminf {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f)) :
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
      ∂(volume : Measure (Space n))) ≤
      Filter.liminf
        (fun j =>
          ∫⁻ p in K.carrier,
            ENNReal.ofReal
              (minimumNormalizedSourceBodyDual (D (φ j)) p)
            ∂(volume : Measure (Space n)))
        atTop := by
  calc
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
      ∂(volume : Measure (Space n))) ≤
        ∫⁻ p in K.carrier,
          Filter.liminf
            (fun j => ENNReal.ofReal
              (minimumNormalizedSourceBodyDual (D (φ j)) p))
            atTop
          ∂(volume : Measure (Space n)) := by
            apply MeasureTheory.lintegral_mono_ae
            filter_upwards
              [MeasureTheory.ae_restrict_mem
                K.compact.measurableSet] with p hp
            exact sourceExtendedBodyLegendre_limit_le_liminf
              D φ f hconv hp
    _ ≤ Filter.liminf
        (fun j =>
          ∫⁻ p in K.carrier,
            ENNReal.ofReal
              (minimumNormalizedSourceBodyDual (D (φ j)) p)
            ∂(volume : Measure (Space n)))
        atTop := by
          apply MeasureTheory.lintegral_liminf_le'
          intro j
          exact
            (minimumNormalizedSourceBodyDual_integrableOn
              (D (φ j))).aestronglyMeasurable.aemeasurable.ennreal_ofReal
theorem minimumNormalizedSourceBodyDual_lintegral {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    (∫⁻ p in K.carrier,
      ENNReal.ofReal (minimumNormalizedSourceBodyDual D p)
      ∂(volume : Measure (Space n))) =
      ENNReal.ofReal
        (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
          ∂(volume : Measure (Space n))) := by
  symm
  apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (minimumNormalizedSourceBodyDual_integrableOn D)
  filter_upwards
    [MeasureTheory.ae_restrict_mem K.compact.measurableSet]
    with p hp
  exact minimumNormalizedSourceBodyDual_nonneg D hp
theorem sourceExtendedBodyLegendre_lintegral_le_of_uniformEnergy
    {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f))
    (C : ℝ)
    (henergy : ∀ j : ℕ,
      sourceMomentBodyEnergy (D j) +
        (D j).potential
          (sourceMomentMinimumPoint (D j)) ≤ C) :
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
      ∂(volume : Measure (Space n))) ≤
      ENNReal.ofReal (normalizedVolume K.carrier * C) := by
  calc
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
      ∂(volume : Measure (Space n))) ≤
        Filter.liminf
          (fun j =>
            ∫⁻ p in K.carrier,
              ENNReal.ofReal
                (minimumNormalizedSourceBodyDual (D (φ j)) p)
              ∂(volume : Measure (Space n)))
          atTop :=
        sourceExtendedBodyLegendre_lintegral_le_liminf
          D φ f hconv
    _ ≤ ENNReal.ofReal (normalizedVolume K.carrier * C) := by
      have hterm : ∀ j : ℕ,
          (∫⁻ p in K.carrier,
            ENNReal.ofReal
              (minimumNormalizedSourceBodyDual (D (φ j)) p)
            ∂(volume : Measure (Space n))) ≤
            ENNReal.ofReal
              (normalizedVolume K.carrier * C) := by
        intro j
        rw [minimumNormalizedSourceBodyDual_lintegral]
        apply ENNReal.ofReal_le_ofReal
        calc
          (∫ p in K.carrier,
            minimumNormalizedSourceBodyDual (D (φ j)) p
            ∂(volume : Measure (Space n))) =
              normalizedVolume K.carrier *
                (sourceMomentBodyEnergy (D (φ j)) +
                  (D (φ j)).potential
                    (sourceMomentMinimumPoint (D (φ j)))) := by
                  have h :=
                    minimumNormalizedSourceBodyDual_energy (D (φ j))
                  have hvol := K.volume_pos.ne'
                  field_simp at h
                  linarith
          _ ≤ normalizedVolume K.carrier * C :=
            mul_le_mul_of_nonneg_left
              (henergy (φ j)) K.volume_pos.le
      have hmono := Filter.liminf_le_liminf
        (show
          ∀ᶠ j : ℕ in atTop,
            (∫⁻ p in K.carrier,
              ENNReal.ofReal
                (minimumNormalizedSourceBodyDual (D (φ j)) p)
              ∂(volume : Measure (Space n))) ≤
              (fun _ : ℕ =>
                ENNReal.ofReal
                  (normalizedVolume K.carrier * C)) j
          from Eventually.of_forall hterm)
      have hconst :
          Tendsto
            (fun _ : ℕ =>
              ENNReal.ofReal
                (normalizedVolume K.carrier * C))
            atTop
            (𝓝 (ENNReal.ofReal
              (normalizedVolume K.carrier * C))) :=
        tendsto_const_nhds
      simpa only [hconst.liminf_eq] using hmono
theorem exists_minimumNormalizedSourceFiniteEnergy_subsequence
    {n : ℕ}
    {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (C : ℝ)
    (henergy : ∀ j : ℕ,
      sourceMomentBodyEnergy (D j) +
        (D j).potential
          (sourceMomentMinimumPoint (D j)) ≤ C) :
    ∃ (f : C(Space n, ℝ))
      (φ : ℕ → ℕ),
      f 0 = 0 ∧
      LipschitzWith (sourceBodyLipschitzConstant K) f ∧
      ConvexOn ℝ Set.univ f ∧
      (∀ x : Space n,
        0 ≤ f x ∧
          f x ≤ SupportFunction.supportFunction K.carrier x) ∧
      StrictMono φ ∧
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
        atTop (𝓝 f) ∧
      (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
        ∂(volume : Measure (Space n))) ≤
        ENNReal.ofReal (normalizedVolume K.carrier * C) := by
  obtain ⟨f, φ, hzero, hlip, hconvex, hbounds,
    hφ, hconv⟩ :=
    exists_minimumNormalizedSourceConvex_subsequence D
  exact ⟨f, φ, hzero, hlip, hconvex, hbounds, hφ, hconv,
    sourceExtendedBodyLegendre_lintegral_le_of_uniformEnergy
      D φ f hconv C henergy⟩
end MomentFunctionalCoercivity
namespace MomentNonlinearTightness
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentCoercivityCompactness
open scoped BigOperators ENNReal NNReal Topology
theorem exists_uniform_inner_supportBall {n : ℕ}
    (K : CenteredBody n) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧
      ∀ x : Space n,
        ∃ c : Space n,
          Metric.ball c (ρ / 2) ⊆ K.carrier ∧
          ∀ p ∈ Metric.ball c (ρ / 2),
            δ * ‖x‖ ≤ SupportFunction.pairing p x := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior)
      (0 : Space n)
      (LatticeAsymptotics.zero_mem_interior K)
  obtain ⟨d, hd, hgap⟩ :=
    SupportFunction.interior_gap K.compact
      (LatticeAsymptotics.zero_mem_interior K)
  let ρ : ℝ := min (r / 2) (d / (4 * ((n : ℝ) + 1)))
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (half_pos hr)
      (div_pos hd (by positivity))
  have hρr : ρ < r :=
    (show ρ ≤ r / 2 from min_le_left _ _).trans_lt
      (half_lt_self hr)
  have hnrho : (n : ℝ) * ρ ≤ d / 4 := by
    have hfrac : ρ ≤ d / (4 * ((n : ℝ) + 1)) :=
      min_le_right _ _
    have hden : 0 < 4 * ((n : ℝ) + 1) := by
      positivity
    have hmul := (le_div_iff₀ hden).mp hfrac
    nlinarith [mul_nonneg (Nat.cast_nonneg n) hρ.le]
  refine ⟨ρ, d / 4, hρ, by positivity, ?_⟩
  intro x
  obtain ⟨v, hv, hmax⟩ :=
    SupportFunction.supportFunction_attained
      K.compact (K.fullDimensional.mono interior_subset) x
  refine ⟨(2 : ℝ)⁻¹ • v, ?_, ?_⟩
  · intro p hp
    have hdist :
        ‖p - (2 : ℝ)⁻¹ • v‖ < ρ / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hp
    let z : Space n := (2 : ℝ) • p - v
    have hzform :
        z = (2 : ℝ) • (p - (2 : ℝ)⁻¹ • v) := by
      ext i
      simp [z]
      ring
    have hznorm : ‖z‖ < ρ := by
      rw [hzform, norm_smul, Real.norm_eq_abs]
      norm_num
      nlinarith
    have hzball : z ∈ Metric.ball (0 : Space n) r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hznorm.trans hρr
    have hzK : z ∈ K.carrier :=
      interior_subset (hball hzball)
    have hpform :
        p = (2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • z := by
      ext i
      simp [z]
      ring
    rw [hpform]
    exact K.convex hv hzK (by norm_num) (by norm_num) (by norm_num)
  · intro p hp
    have hdist :
        ‖p - (2 : ℝ)⁻¹ • v‖ < ρ / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hp
    let z : Space n := (2 : ℝ) • p - v
    have hzform :
        z = (2 : ℝ) • (p - (2 : ℝ)⁻¹ • v) := by
      ext i
      simp [z]
      ring
    have hznorm : ‖z‖ < ρ := by
      rw [hzform, norm_smul, Real.norm_eq_abs]
      norm_num
      nlinarith
    have hzbound :
        |SupportFunction.pairing z x| ≤
          (d / 4) * ‖x‖ := by
      calc
        |SupportFunction.pairing z x| ≤
            ((n : ℝ) * ‖z‖) * ‖x‖ :=
          MonomialDivergence.abs_pairing_le_dimension_mul_norm
            z x
        _ ≤ ((n : ℝ) * ρ) * ‖x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hznorm.le
              (Nat.cast_nonneg n))
            (norm_nonneg x)
        _ ≤ (d / 4) * ‖x‖ :=
          mul_le_mul_of_nonneg_right hnrho (norm_nonneg x)
    have hvbound :
        d * ‖x‖ ≤ SupportFunction.pairing v x := by
      have hg := hgap x
      simpa [SupportFunction.pairing, hmax] using hg
    have hpform :
        p = (2 : ℝ)⁻¹ • v + (2 : ℝ)⁻¹ • z := by
      ext i
      simp [z]
      ring
    rw [hpform, SupportFunction.pairing_add_left,
      SupportFunction.pairing_smul_left,
      SupportFunction.pairing_smul_left]
    have hzlow := (abs_le.mp hzbound).1
    norm_num
    nlinarith [mul_nonneg hd.le (norm_nonneg x)]
theorem realVolume_uniformInnerBall {n : ℕ}
    (c : Space n)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    (volume : Measure (Space n)).real
        (Metric.ball c (ρ / 2)) = ρ ^ n := by
  have h := congrArg ENNReal.toReal
    (Real.volume_pi_ball c (half_pos hρ))
  have htwo : (2 : ℝ) * (ρ / 2) = ρ := by
    ring
  simpa [measureReal_def, htwo,
    ENNReal.toReal_ofReal (pow_nonneg hρ.le n)] using h
theorem minimumNormalizedSourceBodyFenchel_le {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K)
    {p : Space n}
    (hp : p ∈ K.carrier)
    (x : Space n) :
    SupportFunction.pairing p x -
        minimumNormalizedSourceContinuousMap D x ≤
      minimumNormalizedSourceBodyDual D p := by
  have h := le_csSup
    (minimumNormalizedSourcePhase_bddAbove D hp)
    (show
      phase p (minimumNormalizedSourceContinuousMap D) x ∈
        Set.range (phase p (minimumNormalizedSourceContinuousMap D))
      from ⟨x, rfl⟩)
  change
    SupportFunction.pairing p x -
        minimumNormalizedSourceContinuousMap D x ≤
      legendreTransform (minimumNormalizedSourceContinuousMap D) p at h
  rwa [← minimumNormalizedSourceBodyDual_eq_legendre D hp] at h
theorem exists_minimumNormalizedSource_linear_coercivity {n : ℕ}
    (K : CenteredBody n) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
      ∀ (D : SourceMomentPotential K)
        (x : Space n),
        δ * ‖x‖ ≤
          minimumNormalizedSourceContinuousMap D x +
            B *
              (sourceMomentBodyEnergy D +
                D.potential (sourceMomentMinimumPoint D)) := by
  obtain ⟨ρ, δ, hρ, hδ, hball⟩ :=
    exists_uniform_inner_supportBall K
  have hpow : 0 < ρ ^ n := pow_pos hρ n
  refine ⟨δ, normalizedVolume K.carrier / ρ ^ n,
    hδ, div_pos K.volume_pos hpow, ?_⟩
  intro D x
  obtain ⟨c, hsubset, hpair⟩ := hball x
  have hfinite :
      (volume : Measure (Space n))
          (Metric.ball c (ρ / 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top K.compact.measure_ne_top
      (measure_mono hsubset)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x)
      (Metric.ball c (ρ / 2))
      (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const hfinite
  have hdualK := minimumNormalizedSourceBodyDual_integrableOn D
  have hdualball : IntegrableOn
      (minimumNormalizedSourceBodyDual D)
      (Metric.ball c (ρ / 2))
      (volume : Measure (Space n)) :=
    hdualK.mono_set hsubset
  have hdualmass :
      (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
        ∂(volume : Measure (Space n))) =
        normalizedVolume K.carrier *
          (sourceMomentBodyEnergy D +
            D.potential (sourceMomentMinimumPoint D)) := by
    have h := minimumNormalizedSourceBodyDual_energy D
    have hvol := K.volume_pos.ne'
    field_simp at h
    linarith
  have hbound :
      ρ ^ n *
          (δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x) ≤
        normalizedVolume K.carrier *
          (sourceMomentBodyEnergy D +
            D.potential (sourceMomentMinimumPoint D)) := by
    calc
      ρ ^ n *
          (δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x) =
          (∫ _p in Metric.ball c (ρ / 2),
            δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x
            ∂(volume : Measure (Space n))) := by
              rw [MeasureTheory.setIntegral_const,
                realVolume_uniformInnerBall c hρ]
              simp [smul_eq_mul]
      _ ≤ (∫ p in Metric.ball c (ρ / 2),
          minimumNormalizedSourceBodyDual D p
          ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.setIntegral_mono_on
              hconst hdualball Metric.isOpen_ball.measurableSet
            intro p hp
            calc
              δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x ≤
                  SupportFunction.pairing p x -
                    minimumNormalizedSourceContinuousMap D x :=
                sub_le_sub_right (hpair p hp) _
              _ ≤ minimumNormalizedSourceBodyDual D p :=
                minimumNormalizedSourceBodyFenchel_le
                  D (hsubset hp) x
      _ ≤ (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
          ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.setIntegral_mono_set hdualK
            · filter_upwards
                [MeasureTheory.ae_restrict_mem
                  K.compact.measurableSet] with p hp
              exact minimumNormalizedSourceBodyDual_nonneg D hp
            · exact Filter.Eventually.of_forall hsubset
      _ = normalizedVolume K.carrier *
            (sourceMomentBodyEnergy D +
              D.potential (sourceMomentMinimumPoint D)) :=
          hdualmass
  have hdiv :
      δ * ‖x‖ - minimumNormalizedSourceContinuousMap D x ≤
        (normalizedVolume K.carrier *
          (sourceMomentBodyEnergy D +
            D.potential (sourceMomentMinimumPoint D))) /
          ρ ^ n := by
    apply (le_div_iff₀ hpow).mpr
    simpa [mul_comm] using hbound
  calc
    δ * ‖x‖ ≤
        minimumNormalizedSourceContinuousMap D x +
          (normalizedVolume K.carrier *
            (sourceMomentBodyEnergy D +
              D.potential (sourceMomentMinimumPoint D))) /
            ρ ^ n := by
          linarith
    _ = minimumNormalizedSourceContinuousMap D x +
          (normalizedVolume K.carrier / ρ ^ n) *
            (sourceMomentBodyEnergy D +
              D.potential (sourceMomentMinimumPoint D)) := by
          ring
theorem exists_minimumNormalizedSource_gibbs_decay {n : ℕ}
    (K : CenteredBody n) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
      ∀ (D : SourceMomentPotential K)
        (x : Space n),
        Real.exp (-minimumNormalizedSourceContinuousMap D x) ≤
          Real.exp
              (B *
                (sourceMomentBodyEnergy D +
                  D.potential (sourceMomentMinimumPoint D))) *
            Real.exp (-δ * ‖x‖) := by
  obtain ⟨δ, B, hδ, hB, hcoerce⟩ :=
    exists_minimumNormalizedSource_linear_coercivity K
  refine ⟨δ, B, hδ, hB, ?_⟩
  intro D x
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [hcoerce D x]
end MomentNonlinearTightness
namespace MomentMoserTrudinger
open Set Function Filter MeasureTheory
open MomentExistence MomentPotentialExistence MomentCoercivityCompactness MomentNonlinearTightness
open scoped BigOperators ENNReal NNReal Topology
theorem integrable_exp_neg_mul_norm_all {n : ℕ} {a : ℝ}
    (ha : 0 < a) :
    Integrable (fun x : Space n => Real.exp (-a * ‖x‖))
      (volume : Measure (Space n)) := by
  cases n with
  | zero =>
      rw [MeasureTheory.Measure.volume_pi_eq_dirac
        (0 : Space 0)]
      exact MeasureTheory.integrable_dirac (by simp)
  | succ n =>
      exact MonomialIntegrability.integrable_exp_neg_mul_norm
        (Nat.zero_lt_succ n) ha
def minimumNormalizedSourceBodyEnergy {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  sourceMomentBodyEnergy D +
    D.potential (sourceMomentMinimumPoint D)
def minimumNormalizedSourcePartition {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  ∫ x : Space n,
    Real.exp (-minimumNormalizedSourceContinuousMap D x)
    ∂(volume : Measure (Space n))
theorem minimumNormalizedSourceDensity_integrable {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    Integrable
      (fun x : Space n =>
        Real.exp (-minimumNormalizedSourceContinuousMap D x))
      (volume : Measure (Space n)) := by
  obtain ⟨δ, B, hδ, _hB, hdecay⟩ :=
    exists_minimumNormalizedSource_gibbs_decay K
  refine ((integrable_exp_neg_mul_norm_all hδ).const_mul
    (Real.exp (B * minimumNormalizedSourceBodyEnergy D))).mono'
    (Real.continuous_exp.comp
      (minimumNormalizedSourceContinuousMap D).continuous.neg).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hdecay D x
theorem minimumNormalizedSourcePartition_eq {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    minimumNormalizedSourcePartition D =
      Real.exp (D.potential (sourceMomentMinimumPoint D)) *
        sourceMomentPartition D := by
  unfold minimumNormalizedSourcePartition
  calc
    (∫ x : Space n,
      Real.exp (-minimumNormalizedSourceContinuousMap D x)
      ∂(volume : Measure (Space n))) =
        ∫ x : Space n,
          Real.exp (D.potential (sourceMomentMinimumPoint D)) *
            Real.exp
              (-D.potential (x + sourceMomentMinimumPoint D))
          ∂(volume : Measure (Space n)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [← Real.exp_add]
            congr 1
            change
              -(D.potential (x + sourceMomentMinimumPoint D) -
                D.potential (sourceMomentMinimumPoint D)) =
                D.potential (sourceMomentMinimumPoint D) +
                  -D.potential (x + sourceMomentMinimumPoint D)
            ring
    _ = Real.exp (D.potential (sourceMomentMinimumPoint D)) *
        (∫ x : Space n,
          Real.exp
            (-D.potential (x + sourceMomentMinimumPoint D))
          ∂(volume : Measure (Space n))) :=
        MeasureTheory.integral_const_mul _ _
    _ = Real.exp (D.potential (sourceMomentMinimumPoint D)) *
        sourceMomentPartition D := by
        rw [MeasureTheory.integral_add_right_eq_self
          (fun x : Space n => Real.exp (-D.potential x))
          (sourceMomentMinimumPoint D)]
        rfl
theorem minimumNormalizedSourcePartition_pos {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 < minimumNormalizedSourcePartition D := by
  rw [minimumNormalizedSourcePartition_eq]
  exact mul_pos (Real.exp_pos _)
    (sourceMomentPartition_pos D)
def minimumNormalizedSourceBermanFunctional {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) : ℝ :=
  Real.log (minimumNormalizedSourcePartition D) -
    minimumNormalizedSourceBodyEnergy D
theorem minimumNormalizedSourceBermanFunctional_eq {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    minimumNormalizedSourceBermanFunctional D =
      sourceMomentBermanFunctional D := by
  unfold minimumNormalizedSourceBermanFunctional
    minimumNormalizedSourceBodyEnergy sourceMomentBermanFunctional
  rw [minimumNormalizedSourcePartition_eq,
    Real.log_mul (Real.exp_pos _).ne'
      (sourceMomentPartition_pos D).ne',
    Real.log_exp]
  ring
theorem minimumNormalizedSourceBodyEnergy_nonneg {n : ℕ}
    {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    0 ≤ minimumNormalizedSourceBodyEnergy D :=
  sourceMomentBodyEnergy_add_minimum_nonneg D
theorem exists_minimumNormalizedSource_strong_moser_trudinger
    {n : ℕ} (K : CenteredBody n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ,
      ∀ D : SourceMomentPotential K,
        Real.log (minimumNormalizedSourcePartition D) ≤
          ε * minimumNormalizedSourceBodyEnergy D + A := by
  obtain ⟨δ, B, hδ, hB, hcoerce⟩ :=
    exists_minimumNormalizedSource_linear_coercivity K
  let t : ℝ := min 1 (ε / B)
  have ht : 0 < t := by
    dsimp [t]
    exact lt_min (by norm_num) (div_pos hε hB)
  have htone : t ≤ 1 := min_le_left _ _
  have htB : t * B ≤ ε := by
    calc
      t * B ≤ (ε / B) * B :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hB.le
      _ = ε := by field_simp
  let I : ℝ :=
    ∫ x : Space n,
      Real.exp (-(t * δ) * ‖x‖)
      ∂(volume : Measure (Space n))
  have hrad : Integrable
      (fun x : Space n => Real.exp (-(t * δ) * ‖x‖))
      (volume : Measure (Space n)) :=
    integrable_exp_neg_mul_norm_all (mul_pos ht hδ)
  have hI : 0 < I := by
    dsimp [I]
    exact MeasureTheory.integral_exp_pos hrad
  refine ⟨Real.log I, ?_⟩
  intro D
  have henergy := minimumNormalizedSourceBodyEnergy_nonneg D
  have hpoint (x : Space n) :
      Real.exp (-minimumNormalizedSourceContinuousMap D x) ≤
        Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) *
          Real.exp (-(t * δ) * ‖x‖) := by
    have hφ := minimumNormalizedSourceContinuousMap_nonneg D x
    have htφ :
        t * minimumNormalizedSourceContinuousMap D x ≤
          minimumNormalizedSourceContinuousMap D x := by
      calc
        t * minimumNormalizedSourceContinuousMap D x ≤
            1 * minimumNormalizedSourceContinuousMap D x :=
          mul_le_mul_of_nonneg_right htone hφ
        _ = minimumNormalizedSourceContinuousMap D x := one_mul _
    have hc := hcoerce D x
    change
      δ * ‖x‖ ≤ minimumNormalizedSourceContinuousMap D x +
        B * minimumNormalizedSourceBodyEnergy D at hc
    have hscaled := mul_le_mul_of_nonneg_left hc ht.le
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbound :
      minimumNormalizedSourcePartition D ≤
        Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) * I := by
    unfold minimumNormalizedSourcePartition
    calc
      (∫ x : Space n,
        Real.exp (-minimumNormalizedSourceContinuousMap D x)
        ∂(volume : Measure (Space n))) ≤
          ∫ x : Space n,
            Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) *
              Real.exp (-(t * δ) * ‖x‖)
            ∂(volume : Measure (Space n)) :=
              MeasureTheory.integral_mono
                (minimumNormalizedSourceDensity_integrable D)
                (hrad.const_mul
                  (Real.exp
                    (t * B * minimumNormalizedSourceBodyEnergy D)))
                hpoint
      _ = Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) *
          I := by
            rw [MeasureTheory.integral_const_mul]
  calc
    Real.log (minimumNormalizedSourcePartition D) ≤
        Real.log
          (Real.exp (t * B * minimumNormalizedSourceBodyEnergy D) * I) :=
      Real.log_le_log (minimumNormalizedSourcePartition_pos D) hbound
    _ = t * B * minimumNormalizedSourceBodyEnergy D + Real.log I := by
      rw [Real.log_mul (Real.exp_pos _).ne' hI.ne', Real.log_exp]
    _ ≤ ε * minimumNormalizedSourceBodyEnergy D + Real.log I :=
      add_le_add
        (mul_le_mul_of_nonneg_right htB henergy)
        (le_refl _)
theorem sourceMomentBermanFunctional_bddAbove {n : ℕ}
    (K : CenteredBody n) :
    BddAbove
      (Set.range
        (fun D : SourceMomentPotential K =>
          sourceMomentBermanFunctional D)) := by
  obtain ⟨A, hA⟩ :=
    exists_minimumNormalizedSource_strong_moser_trudinger
      K (1 / 2 : ℝ) (by norm_num)
  refine ⟨A, ?_⟩
  rintro _ ⟨D, rfl⟩
  change sourceMomentBermanFunctional D ≤ A
  rw [← minimumNormalizedSourceBermanFunctional_eq D]
  unfold minimumNormalizedSourceBermanFunctional
  linarith [hA D, minimumNormalizedSourceBodyEnergy_nonneg D]
theorem exists_sourceMomentBerman_superlevel_uniformEnergy
    {n : ℕ} (K : CenteredBody n) (L : ℝ) :
    ∃ C : ℝ,
      ∀ D : SourceMomentPotential K,
        L ≤ sourceMomentBermanFunctional D →
          minimumNormalizedSourceBodyEnergy D ≤ C := by
  obtain ⟨A, hA⟩ :=
    exists_minimumNormalizedSource_strong_moser_trudinger
      K (1 / 2 : ℝ) (by norm_num)
  refine ⟨2 * (A - L), ?_⟩
  intro D hL
  have hfunctional := minimumNormalizedSourceBermanFunctional_eq D
  unfold minimumNormalizedSourceBermanFunctional at hfunctional
  nlinarith [hA D]
theorem exists_sourceMomentBerman_maximizingSequence_uniformEnergy
    {n : ℕ} (K : CenteredBody n) :
    ∃ (D : ℕ → SourceMomentPotential K) (C : ℝ),
      (∀ j : ℕ, minimumNormalizedSourceBodyEnergy (D j) ≤ C) ∧
      Tendsto
        (fun j => sourceMomentBermanFunctional (D j))
        atTop
        (𝓝
          (sSup
            (Set.range
              (fun D : SourceMomentPotential K =>
                sourceMomentBermanFunctional D)))) := by
  obtain ⟨u, hmono, hlimit, hmem⟩ :=
    exists_seq_tendsto_sSup
      (show
        (Set.range
          (fun D : SourceMomentPotential K =>
            sourceMomentBermanFunctional D)).Nonempty from
        ⟨sourceMomentBermanFunctional
            (canonicalSourceMomentPotential K),
          canonicalSourceMomentPotential K, rfl⟩)
      (sourceMomentBermanFunctional_bddAbove K)
  have hchoose :
      ∀ j : ℕ, ∃ D : SourceMomentPotential K,
        sourceMomentBermanFunctional D = u j := by
    intro j
    exact hmem j
  choose D hD using hchoose
  obtain ⟨C, hC⟩ :=
    exists_sourceMomentBerman_superlevel_uniformEnergy K (u 0)
  refine ⟨D, C, ?_, ?_⟩
  · intro j
    apply hC
    rw [hD j]
    exact hmono (Nat.zero_le j)
  · have heq :
        (fun j => sourceMomentBermanFunctional (D j)) = u :=
      funext hD
    rw [heq]
    exact hlimit
end MomentMoserTrudinger
namespace MomentOptimizer
open Set Function Filter MeasureTheory
open MomentExistence MomentPotentialExistence MomentMinimizer MomentCoercivityCompactness
open MomentFunctionalCoercivity MomentNonlinearTightness MomentMoserTrudinger
open scoped BigOperators ENNReal NNReal Topology
theorem exists_minimumNormalizedSource_uniform_gibbs_majorant_all
    {n : ℕ} (K : CenteredBody n) (C : ℝ) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
      Integrable
        (fun x : Space n =>
          Real.exp (B * C) * Real.exp (-δ * ‖x‖))
        (volume : Measure (Space n)) ∧
      ∀ (D : SourceMomentPotential K),
        minimumNormalizedSourceBodyEnergy D ≤ C →
        ∀ x : Space n,
          Real.exp (-minimumNormalizedSourceContinuousMap D x) ≤
            Real.exp (B * C) * Real.exp (-δ * ‖x‖) := by
  obtain ⟨δ, B, hδ, hB, hdecay⟩ :=
    exists_minimumNormalizedSource_gibbs_decay K
  refine ⟨δ, B, hδ, hB,
    (integrable_exp_neg_mul_norm_all hδ).const_mul
      (Real.exp (B * C)), ?_⟩
  intro D henergy x
  calc
    Real.exp (-minimumNormalizedSourceContinuousMap D x) ≤
        Real.exp (B * minimumNormalizedSourceBodyEnergy D) *
          Real.exp (-δ * ‖x‖) := hdecay D x
    _ ≤ Real.exp (B * C) * Real.exp (-δ * ‖x‖) :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left henergy hB.le))
        (Real.exp_pos _).le
theorem tendsto_minimumNormalizedSourcePartition_of_uniformEnergy_all
    {n : ℕ} {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f))
    (C : ℝ)
    (henergy : ∀ j : ℕ,
      minimumNormalizedSourceBodyEnergy (D j) ≤ C) :
    Tendsto
      (fun j => minimumNormalizedSourcePartition (D (φ j)))
      atTop
      (𝓝
        (∫ x : Space n, Real.exp (-f x)
          ∂(volume : Measure (Space n)))) := by
  obtain ⟨δ, B, _hδ, _hB, hG, hmajor⟩ :=
    exists_minimumNormalizedSource_uniform_gibbs_majorant_all K C
  unfold minimumNormalizedSourcePartition
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : Space n =>
      Real.exp (B * C) * Real.exp (-δ * ‖x‖))
  · intro j
    exact (Real.continuous_exp.comp
      (minimumNormalizedSourceContinuousMap
        (D (φ j))).continuous.neg).aestronglyMeasurable
  · exact hG
  · intro j
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hmajor (D (φ j)) (henergy (φ j)) x
  · filter_upwards with x
    have hx :=
      (continuous_eval_const x).continuousAt.tendsto.comp hconv
    exact (Real.continuous_exp.tendsto _).comp hx.neg
structure SourceFiniteEnergyPotential {n : ℕ}
    (K : CenteredBody n) where
  potential : C(Space n, ℝ)
  normalized : potential 0 = 0
  lipschitz : LipschitzWith (sourceBodyLipschitzConstant K) potential
  convex : ConvexOn ℝ Set.univ potential
  nonnegative : ∀ x : Space n, 0 ≤ potential x
  supportUpper : ∀ x : Space n,
    potential x ≤ SupportFunction.supportFunction K.carrier x
  legendreFinite :
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre potential p
      ∂(volume : Measure (Space n))) < ⊤
  densityIntegrable :
    Integrable (fun x : Space n => Real.exp (-potential x))
      (volume : Measure (Space n))
def finiteEnergySourcePartition {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : ℝ :=
  ∫ x : Space n, Real.exp (-F.potential x)
    ∂(volume : Measure (Space n))
theorem finiteEnergySourcePartition_pos {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    0 < finiteEnergySourcePartition F :=
  MeasureTheory.integral_exp_pos F.densityIntegrable
def finiteEnergySourceBodyEnergy {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : ℝ :=
  (normalizedVolume K.carrier)⁻¹ *
    (∫⁻ p in K.carrier, sourceExtendedBodyLegendre F.potential p
      ∂(volume : Measure (Space n))).toReal
def finiteEnergySourceBermanFunctional {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : ℝ :=
  Real.log (finiteEnergySourcePartition F) -
    finiteEnergySourceBodyEnergy F
theorem integrable_limit_gibbs_of_uniformEnergy_all
    {n : ℕ} {K : CenteredBody n}
    (D : ℕ → SourceMomentPotential K)
    (φ : ℕ → ℕ)
    (f : C(Space n, ℝ))
    (hconv : Tendsto
      (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
      atTop (𝓝 f))
    (C : ℝ)
    (henergy : ∀ j : ℕ,
      minimumNormalizedSourceBodyEnergy (D j) ≤ C) :
    Integrable (fun x : Space n => Real.exp (-f x))
      (volume : Measure (Space n)) := by
  obtain ⟨δ, B, _hδ, _hB, hG, hmajor⟩ :=
    exists_minimumNormalizedSource_uniform_gibbs_majorant_all K C
  refine hG.mono'
    (Real.continuous_exp.comp f.continuous.neg).aestronglyMeasurable
    ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hx :=
    (continuous_eval_const x).continuousAt.tendsto.comp hconv
  have hexp :
      Tendsto
        (fun j => Real.exp
          (-minimumNormalizedSourceContinuousMap (D (φ j)) x))
        atTop (𝓝 (Real.exp (-f x))) :=
    (Real.continuous_exp.tendsto _).comp hx.neg
  exact le_of_tendsto hexp
    (Eventually.of_forall fun j =>
      hmajor (D (φ j)) (henergy (φ j)) x)
theorem minimumNormalizedSourceBodyDual_lintegral_eq_volume_mul_energy
    {n : ℕ} {K : CenteredBody n}
    (D : SourceMomentPotential K) :
    (∫⁻ p in K.carrier,
      ENNReal.ofReal (minimumNormalizedSourceBodyDual D p)
      ∂(volume : Measure (Space n))) =
      ENNReal.ofReal
        (normalizedVolume K.carrier *
          minimumNormalizedSourceBodyEnergy D) := by
  rw [minimumNormalizedSourceBodyDual_lintegral]
  congr 1
  have h := minimumNormalizedSourceBodyDual_energy D
  change
    (normalizedVolume K.carrier)⁻¹ *
      (∫ p in K.carrier, minimumNormalizedSourceBodyDual D p
        ∂(volume : Measure (Space n))) =
      minimumNormalizedSourceBodyEnergy D at h
  have hvol := K.volume_pos.ne'
  field_simp at h
  linarith
theorem exists_finiteEnergySourceBerman_optimizer {n : ℕ}
    (K : CenteredBody n) :
    ∃ (F : SourceFiniteEnergyPotential K)
      (D : ℕ → SourceMomentPotential K)
      (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto
        (fun j => minimumNormalizedSourceContinuousMap (D (φ j)))
        atTop (𝓝 F.potential) ∧
      Tendsto
        (fun j => sourceMomentBermanFunctional (D (φ j)))
        atTop
        (𝓝
          (sSup
            (Set.range
              (fun G : SourceMomentPotential K =>
                sourceMomentBermanFunctional G)))) ∧
      (∀ G : SourceMomentPotential K,
        sourceMomentBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F) ∧
      sSup
        (Set.range
          (fun G : SourceMomentPotential K =>
            sourceMomentBermanFunctional G)) ≤
        finiteEnergySourceBermanFunctional F := by
  obtain ⟨D, C, henergy, hmax⟩ :=
    exists_sourceMomentBerman_maximizingSequence_uniformEnergy K
  have holdenergy : ∀ j : ℕ,
      sourceMomentBodyEnergy (D j) +
        (D j).potential (sourceMomentMinimumPoint (D j)) ≤ C := by
    intro j
    exact henergy j
  obtain ⟨f, φ, hfzero, hflip, hfconvex, hfbounds,
    hφ, hconv, hfinite⟩ :=
    exists_minimumNormalizedSourceFiniteEnergy_subsequence
      D C holdenergy
  let F : SourceFiniteEnergyPotential K :=
    { potential := f
      normalized := hfzero
      lipschitz := hflip
      convex := hfconvex
      nonnegative := fun x => (hfbounds x).1
      supportUpper := fun x => (hfbounds x).2
      legendreFinite :=
        lt_of_le_of_lt hfinite ENNReal.ofReal_lt_top
      densityIntegrable :=
        integrable_limit_gibbs_of_uniformEnergy_all
          D φ f hconv C henergy }
  let S : ℝ :=
    sSup
      (Set.range
        (fun G : SourceMomentPotential K =>
          sourceMomentBermanFunctional G))
  have hmaxsub :
      Tendsto
        (fun j => sourceMomentBermanFunctional (D (φ j)))
        atTop (𝓝 S) := by
    change
      Tendsto
        (fun j => sourceMomentBermanFunctional (D (φ j)))
        atTop
        (𝓝
          (sSup
            (Set.range
              (fun G : SourceMomentPotential K =>
                sourceMomentBermanFunctional G))))
    exact (hmax.comp hφ.tendsto_atTop).congr'
      (Filter.Eventually.of_forall fun _ => rfl)
  have hpartition :
      Tendsto
        (fun j => minimumNormalizedSourcePartition (D (φ j)))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
    simpa [finiteEnergySourcePartition, F] using
      tendsto_minimumNormalizedSourcePartition_of_uniformEnergy_all
        D φ f hconv C henergy
  have hlog := hpartition.log (finiteEnergySourcePartition_pos F).ne'
  have henergyconv :
      Tendsto
        (fun j => minimumNormalizedSourceBodyEnergy (D (φ j)))
        atTop
        (𝓝 (Real.log (finiteEnergySourcePartition F) - S)) := by
    have hdiff := hlog.sub hmaxsub
    have heq :
        (fun j =>
          Real.log (minimumNormalizedSourcePartition (D (φ j))) -
            sourceMomentBermanFunctional (D (φ j))) =
        (fun j => minimumNormalizedSourceBodyEnergy (D (φ j))) := by
      funext j
      have h := minimumNormalizedSourceBermanFunctional_eq (D (φ j))
      unfold minimumNormalizedSourceBermanFunctional at h
      linarith
    rw [heq] at hdiff
    exact hdiff
  have hlimnonneg :
      0 ≤ Real.log (finiteEnergySourcePartition F) - S :=
    ge_of_tendsto henergyconv
      (Eventually.of_forall fun j =>
        minimumNormalizedSourceBodyEnergy_nonneg (D (φ j)))
  have hmassconv :
      Tendsto
        (fun j => ENNReal.ofReal
          (normalizedVolume K.carrier *
            minimumNormalizedSourceBodyEnergy (D (φ j))))
        atTop
        (𝓝
          (ENNReal.ofReal
            (normalizedVolume K.carrier *
              (Real.log (finiteEnergySourcePartition F) - S)))) := by
    exact ((ENNReal.continuous_ofReal.tendsto _).comp
      (henergyconv.const_mul (normalizedVolume K.carrier))).congr'
        (Filter.Eventually.of_forall fun _ => rfl)
  have hfatou :=
    sourceExtendedBodyLegendre_lintegral_le_liminf D φ f hconv
  have hmassfun :
      (fun j =>
        ∫⁻ p in K.carrier,
          ENNReal.ofReal
            (minimumNormalizedSourceBodyDual (D (φ j)) p)
          ∂(volume : Measure (Space n))) =
      (fun j => ENNReal.ofReal
        (normalizedVolume K.carrier *
          minimumNormalizedSourceBodyEnergy (D (φ j)))) := by
    funext j
    exact minimumNormalizedSourceBodyDual_lintegral_eq_volume_mul_energy
      (D (φ j))
  rw [hmassfun, hmassconv.liminf_eq] at hfatou
  have hreal :
      (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
        ∂(volume : Measure (Space n))).toReal ≤
        normalizedVolume K.carrier *
          (Real.log (finiteEnergySourcePartition F) - S) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfatou
    simpa only [ENNReal.toReal_ofReal
      (mul_nonneg K.volume_pos.le hlimnonneg)] using h
  have hFenergy :
      finiteEnergySourceBodyEnergy F ≤
        Real.log (finiteEnergySourcePartition F) - S := by
    unfold finiteEnergySourceBodyEnergy
    change
      (normalizedVolume K.carrier)⁻¹ *
          (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
            ∂(volume : Measure (Space n))).toReal ≤
        Real.log (finiteEnergySourcePartition F) - S
    calc
      (normalizedVolume K.carrier)⁻¹ *
          (∫⁻ p in K.carrier, sourceExtendedBodyLegendre f p
            ∂(volume : Measure (Space n))).toReal ≤
        (normalizedVolume K.carrier)⁻¹ *
          (normalizedVolume K.carrier *
            (Real.log (finiteEnergySourcePartition F) - S)) :=
          mul_le_mul_of_nonneg_left hreal
            (inv_nonneg.mpr K.volume_pos.le)
      _ = Real.log (finiteEnergySourcePartition F) - S := by
        have hvol := K.volume_pos.ne'
        field_simp
  have hS : S ≤ finiteEnergySourceBermanFunctional F := by
    unfold finiteEnergySourceBermanFunctional
    linarith
  refine ⟨F, D, φ, hφ, ?_, ?_, ?_, ?_⟩
  · simpa [F] using hconv
  · exact hmaxsub
  · intro G
    exact
      (le_csSup
        (sourceMomentBermanFunctional_bddAbove K)
        (show
          sourceMomentBermanFunctional G ∈
            Set.range
              (fun H : SourceMomentPotential K =>
                sourceMomentBermanFunctional H)
          from ⟨G, rfl⟩)).trans hS
  · exact hS
end MomentOptimizer
namespace WeightedBochner
open Set MeasureTheory Matrix Filter
open scoped BigOperators ENNReal InnerProductSpace
theorem continuous_normalizedDensity {n : ℕ}
    {a : Space n → ℝ} (ha : Continuous a) :
    Continuous (WeightedPoincare.normalizedDensity a) := by
  unfold WeightedPoincare.normalizedDensity
  exact (Real.continuous_exp.comp ha.neg).div_const _
theorem integral_normalizedMeasure {n : ℕ}
    {a : Space n → ℝ}
    (ha : Continuous a)
    (hpart : Integrable
      (fun x : Space n => Real.exp (-a x))
      (volume : Measure (Space n)))
    (f : Space n → ℝ) :
    (∫ x : Space n, f x
      ∂(WeightedPoincare.normalizedMeasure a)) =
      (∫ x : Space n, Real.exp (-a x) * f x
        ∂(volume : Measure (Space n))) /
        WeightedPoincare.partition a := by
  have hmeas : Measurable
      (fun x : Space n => ENNReal.ofReal
        (WeightedPoincare.normalizedDensity a x)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_normalizedDensity ha).measurable
  have hfinite :
      ∀ᵐ x ∂(volume : Measure (Space n)),
        ENNReal.ofReal
          (WeightedPoincare.normalizedDensity a x) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  unfold WeightedPoincare.normalizedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  simp_rw [smul_eq_mul,
    ENNReal.toReal_ofReal
      (WeightedPoincare.normalizedDensity_pos hpart _).le]
  calc
    (∫ x : Space n,
      WeightedPoincare.normalizedDensity a x * f x
        ∂(volume : Measure (Space n))) =
        ∫ x : Space n,
          (Real.exp (-a x) * f x) /
            WeightedPoincare.partition a
          ∂(volume : Measure (Space n)) := by
            congr 1
            funext x
            unfold WeightedPoincare.normalizedDensity
            ring
    _ = _ := MeasureTheory.integral_div _ _
theorem fderiv_coordinate_eval {n : ℕ}
    {f : Space n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (x v w : Space n) :
    (fderiv ℝ (fun y : Space n =>
      (fderiv ℝ f y) v) x) w =
      ((fderiv ℝ (fderiv ℝ f) x) w) v := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by simp) |>.differentiableAt
  have heq := fderiv_clm_apply hdf
    (differentiableAt_const (c := v))
  have happly := congrArg
    (fun L : Space n →L[ℝ] ℝ => L w) heq
  simpa [ContinuousLinearMap.flip_apply] using happly
end WeightedBochner
namespace MomentWeakFirstVariation
open Set Function Filter MeasureTheory Metric
open MomentOptimizer
open scoped ENNReal Topology
def finiteEnergySourceGibbsProbability {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Measure (Space n) :=
  WeightedPoincare.normalizedMeasure F.potential
theorem finiteEnergySourceGibbsProbability_isProbability {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    IsProbabilityMeasure (finiteEnergySourceGibbsProbability F) :=
  WeightedPoincare.normalizedMeasure_isProbability
    F.densityIntegrable
theorem integral_finiteEnergySourceGibbsProbability {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : Space n → ℝ) :
    (∫ x : Space n, v x
      ∂(finiteEnergySourceGibbsProbability F)) =
      (∫ x : Space n,
        v x * Real.exp (-F.potential x)
        ∂(volume : Measure (Space n))) /
        finiteEnergySourcePartition F := by
  unfold finiteEnergySourceGibbsProbability
  rw [WeightedBochner.integral_normalizedMeasure
    F.potential.continuous F.densityIntegrable v]
  congr 1
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
end MomentWeakFirstVariation
namespace MomentConvexRecovery
open Set Function Filter MeasureTheory Metric
open LaplaceAsymptotics ArbitraryBodySmoothConvexPotentialBridge MomentExistence
open MomentPotentialExistence MomentMinimizer MomentFunctionalCoercivity MomentMoserTrudinger
open MomentOptimizer
open scoped BigOperators Convolution ENNReal Topology ContDiff
def sourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (x : Space n) : ℝ :=
  max (F.potential x)
    (SupportFunction.supportFunction K.carrier x - R)
theorem continuous_sourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) (R : ℝ) :
    Continuous (sourceSupportClipping F R) := by
  unfold sourceSupportClipping
  exact F.potential.continuous.sup
    ((continuous_supportFunction K.compact
      (K.fullDimensional.mono interior_subset)).sub continuous_const)
theorem convexOn_sourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) (R : ℝ) :
    ConvexOn ℝ Set.univ (sourceSupportClipping F R) := by
  have hsupport := convexOn_supportFunction K.compact
    (K.fullDimensional.mono interior_subset)
  have hshift :
      ConvexOn ℝ Set.univ
        (fun x : Space n =>
          SupportFunction.supportFunction K.carrier x - R) := by
    refine ⟨hsupport.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have h := hsupport.2 hx hy ha hb hab
    change SupportFunction.supportFunction K.carrier
        (a • x + b • y) ≤
      a * SupportFunction.supportFunction K.carrier x +
        b * SupportFunction.supportFunction K.carrier y at h
    change SupportFunction.supportFunction K.carrier
        (a • x + b • y) - R ≤
      a * (SupportFunction.supportFunction K.carrier x - R) +
        b * (SupportFunction.supportFunction K.carrier y - R)
    calc
      SupportFunction.supportFunction K.carrier
          (a • x + b • y) - R ≤
          (a * SupportFunction.supportFunction K.carrier x +
            b * SupportFunction.supportFunction K.carrier y) - R :=
        sub_le_sub_right h R
      _ = (a * SupportFunction.supportFunction K.carrier x +
            b * SupportFunction.supportFunction K.carrier y) -
            (a + b) * R := by simp [hab]
      _ = a * (SupportFunction.supportFunction K.carrier x - R) +
            b * (SupportFunction.supportFunction K.carrier y - R) := by
        ring
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  change
    max (F.potential (a • x + b • y))
        (SupportFunction.supportFunction K.carrier
          (a • x + b • y) - R) ≤
      a * max (F.potential x)
        (SupportFunction.supportFunction K.carrier x - R) +
      b * max (F.potential y)
        (SupportFunction.supportFunction K.carrier y - R)
  apply max_le
  · calc
      F.potential (a • x + b • y) ≤
          a * F.potential x + b * F.potential y :=
        F.convex.2 hx hy ha hb hab
      _ ≤ a * max (F.potential x)
            (SupportFunction.supportFunction K.carrier x - R) +
          b * max (F.potential y)
            (SupportFunction.supportFunction K.carrier y - R) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
  · calc
      SupportFunction.supportFunction K.carrier
          (a • x + b • y) - R ≤
          a * (SupportFunction.supportFunction K.carrier x - R) +
            b * (SupportFunction.supportFunction K.carrier y - R) :=
        hshift.2 hx hy ha hb hab
      _ ≤ a * max (F.potential x)
            (SupportFunction.supportFunction K.carrier x - R) +
          b * max (F.potential y)
            (SupportFunction.supportFunction K.carrier y - R) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
theorem sourceSupportClipping_ge {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (x : Space n) :
    F.potential x ≤ sourceSupportClipping F R x :=
  le_max_left _ _
theorem sourceSupportClipping_le_support {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    (x : Space n) :
    sourceSupportClipping F R x ≤
      SupportFunction.supportFunction K.carrier x := by
  unfold sourceSupportClipping
  exact max_le (F.supportUpper x) (sub_le_self _ hR)
theorem sourceSupportClipping_supportBound {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    (x : Space n) :
    |sourceSupportClipping F R x -
      SupportFunction.supportFunction K.carrier x| ≤ R := by
  have hu := sourceSupportClipping_le_support F hR x
  have hl :
      SupportFunction.supportFunction K.carrier x - R ≤
        sourceSupportClipping F R x :=
    le_max_right _ _
  exact abs_le.mpr ⟨by linarith, by linarith⟩
theorem sourceSupportClipping_lipschitz {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (sourceSupportClipping F R) := by
  exact GlobalBergmanKernelBound.convex_supportCompatible_lipschitz
    K (convexOn_sourceSupportClipping F R)
    (sourceSupportClipping_supportBound F hR)
def mollifiedSourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (ρ : ContDiffBump (0 : Space n)) :
    Space n → ℝ :=
  ρ.normed (volume : Measure (Space n)) ⋆
    sourceSupportClipping F R
theorem contDiff_mollifiedSourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (ρ : ContDiffBump (0 : Space n)) :
    ContDiff ℝ ∞ (mollifiedSourceSupportClipping F R ρ) := by
  unfold mollifiedSourceSupportClipping
  exact ρ.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ρ.contDiff_normed
    (continuous_sourceSupportClipping F R).locallyIntegrable
theorem convexOn_mollifiedSourceSupportClipping {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (ρ : ContDiffBump (0 : Space n)) :
    ConvexOn ℝ Set.univ
      (mollifiedSourceSupportClipping F R ρ) := by
  change ConvexOn ℝ Set.univ
    (fun x : Space n =>
      ∫ y : Space n,
        ρ.normed (volume : Measure (Space n)) y *
          sourceSupportClipping F R (x - y)
        ∂(volume : Measure (Space n)))
  apply MeasureTheory.integral_convexOn_of_integrand_ae convex_univ
  · filter_upwards with y
    have htranslate :
        ConvexOn ℝ Set.univ
          (fun x : Space n =>
            sourceSupportClipping F R (x - y)) := by
      simpa [Function.comp_def, sub_eq_add_neg, add_comm] using
        (convexOn_sourceSupportClipping F R).translate_right (-y)
    simpa [smul_eq_mul] using
      htranslate.smul
        (ρ.nonneg_normed (μ := (volume : Measure (Space n))) y)
  · intro x _hx
    simpa [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (ρ.hasCompactSupport_normed.convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        ρ.continuous_normed
        (continuous_sourceSupportClipping F R).locallyIntegrable
        x).integrable
theorem dist_mollifiedSourceSupportClipping_le {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    (ρ : ContDiffBump (0 : Space n))
    (x : Space n) :
    dist (mollifiedSourceSupportClipping F R ρ x)
      (sourceSupportClipping F R x) ≤
      ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
        ρ.rOut := by
  unfold mollifiedSourceSupportClipping
  apply ρ.dist_normed_convolution_le
    (continuous_sourceSupportClipping F R).aestronglyMeasurable
  intro y hy
  have h := (sourceSupportClipping_lipschitz F hR).dist_le_mul y x
  have hcoe :
      (sourceBodyLipschitzConstant K : ℝ) =
        (n : ℝ) * LaurentJetSeparatedness.bodyRadius K := by
    unfold sourceBodyLipschitzConstant
    rw [Real.coe_toNNReal]
    exact mul_nonneg (Nat.cast_nonneg n)
      (LaurentJetSeparatedness.bodyRadius_pos K).le
  rw [hcoe] at h
  exact h.trans
    (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp hy).le
      (mul_nonneg (Nat.cast_nonneg n)
        (LaurentJetSeparatedness.bodyRadius_pos K).le))
theorem mollifiedSourceSupportClipping_supportBound {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    (ρ : ContDiffBump (0 : Space n))
    (x : Space n) :
    |mollifiedSourceSupportClipping F R ρ x -
      SupportFunction.supportFunction K.carrier x| ≤
      R +
        ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
          ρ.rOut := by
  have hdist := dist_mollifiedSourceSupportClipping_le F hR ρ x
  rw [Real.dist_eq] at hdist
  have hclip := sourceSupportClipping_supportBound F hR x
  calc
    |mollifiedSourceSupportClipping F R ρ x -
      SupportFunction.supportFunction K.carrier x| ≤
        |mollifiedSourceSupportClipping F R ρ x -
            sourceSupportClipping F R x| +
          |sourceSupportClipping F R x -
            SupportFunction.supportFunction K.carrier x| := by
            simpa only [sub_add_sub_cancel] using abs_add_le
              (mollifiedSourceSupportClipping F R ρ x -
                sourceSupportClipping F R x)
              (sourceSupportClipping F R x -
                SupportFunction.supportFunction K.carrier x)
    _ ≤ ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
          ρ.rOut + R := add_le_add hdist hclip
    _ = R +
          ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
            ρ.rOut := add_comm _ _
def sourceClippedMollificationMoment {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) (hR : 0 ≤ R)
    (ρ : ContDiffBump (0 : Space n)) :
    SourceMomentPotential K where
  potential := mollifiedSourceSupportClipping F R ρ
  smooth := (contDiff_mollifiedSourceSupportClipping F R ρ).of_le
    (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  convex := convexOn_mollifiedSourceSupportClipping F R ρ
  supportError := R +
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) *
      ρ.rOut
  supportBound := mollifiedSourceSupportClipping_supportBound F hR ρ
theorem sourceSupportClippingDensity_integrable {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (R : ℝ) :
    Integrable
      (fun x : Space n =>
        Real.exp (-sourceSupportClipping F R x))
      (volume : Measure (Space n)) := by
  refine F.densityIntegrable.mono'
    (Real.continuous_exp.comp
      (continuous_sourceSupportClipping F R).neg).aestronglyMeasurable
    ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr
    (neg_le_neg (sourceSupportClipping_ge F R x))
theorem eventually_sourceSupportClipping_nat_eq {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) :
    ∀ᶠ j : ℕ in atTop,
      sourceSupportClipping F (j : ℝ) x = F.potential x := by
  have hlarge :
      ∀ᶠ j : ℕ in atTop,
        SupportFunction.supportFunction K.carrier x -
            F.potential x ≤ (j : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (Filter.eventually_ge_atTop
        (SupportFunction.supportFunction K.carrier x -
          F.potential x))
  filter_upwards [hlarge] with j hj
  unfold sourceSupportClipping
  exact max_eq_left (by linarith)
theorem tendsto_sourceSupportClippingPartition {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Tendsto
      (fun j : ℕ =>
        ∫ x : Space n,
          Real.exp (-sourceSupportClipping F (j : ℝ) x)
          ∂(volume : Measure (Space n)))
      atTop (𝓝 (finiteEnergySourcePartition F)) := by
  unfold finiteEnergySourcePartition
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : Space n => Real.exp (-F.potential x))
  · intro j
    exact (Real.continuous_exp.comp
      (continuous_sourceSupportClipping
        F (j : ℝ)).neg).aestronglyMeasurable
  · exact F.densityIntegrable
  · intro j
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (neg_le_neg (sourceSupportClipping_ge F (j : ℝ) x))
  · filter_upwards with x
    have heq := eventually_sourceSupportClipping_nat_eq F x
    exact tendsto_const_nhds.congr'
      (heq.mono fun j hj => by
        change
          Real.exp (-F.potential x) =
            Real.exp (-sourceSupportClipping F (j : ℝ) x)
        rw [hj])
theorem finiteEnergySourceExtendedLegendre_integrableOn {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    IntegrableOn
      (fun p : Space n =>
        (sourceExtendedBodyLegendre F.potential p).toReal)
      K.carrier (volume : Measure (Space n)) := by
  apply MeasureTheory.integrable_toReal_of_lintegral_ne_top
  · exact (measurable_sourceExtendedBodyLegendre
      F.potential).aemeasurable
  · exact F.legendreFinite.ne
theorem finiteEnergySourceBodyEnergy_eq_setIntegral {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    finiteEnergySourceBodyEnergy F =
      (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier,
          (sourceExtendedBodyLegendre F.potential p).toReal
          ∂(volume : Measure (Space n))) := by
  unfold finiteEnergySourceBodyEnergy
  congr 1
  symm
  apply MeasureTheory.integral_toReal
    (measurable_sourceExtendedBodyLegendre F.potential).aemeasurable
  exact MeasureTheory.ae_lt_top'
    (measurable_sourceExtendedBodyLegendre F.potential).aemeasurable
    F.legendreFinite.ne
theorem recoveryLegendre_le_extended {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (D : SourceMomentPotential K)
    (ε : ℝ)
    (hlower : ∀ x : Space n,
      F.potential x - ε ≤ D.potential x)
    (p : Space n)
    (hpfinite : sourceExtendedBodyLegendre F.potential p ≠ ⊤) :
    legendreTransform D.potential p ≤
      (sourceExtendedBodyLegendre F.potential p).toReal + ε := by
  unfold legendreTransform
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  have hphaseENN :=
    ofReal_phase_le_sourceExtendedBodyLegendre F.potential p x
  rw [← ENNReal.ofReal_toReal hpfinite] at hphaseENN
  have hphase :=
    (ENNReal.ofReal_le_ofReal_iff
      ENNReal.toReal_nonneg).mp hphaseENN
  change
    SupportFunction.pairing p x - F.potential x ≤
      (sourceExtendedBodyLegendre F.potential p).toReal at hphase
  change
    SupportFunction.pairing p x - D.potential x ≤
      (sourceExtendedBodyLegendre F.potential p).toReal + ε
  linarith [hlower x]
theorem sourceMomentBodyEnergy_le_finiteEnergy_add {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (D : SourceMomentPotential K)
    (ε : ℝ)
    (hlower : ∀ x : Space n,
      F.potential x - ε ≤ D.potential x) :
    sourceMomentBodyEnergy D ≤
      finiteEnergySourceBodyEnergy F + ε := by
  have hdual := finiteEnergySourceExtendedLegendre_integrableOn F
  have hconst : IntegrableOn
      (fun _ : Space n => ε)
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  have hfinite :
      ∀ᵐ p : Space n
          ∂((volume : Measure (Space n)).restrict K.carrier),
        sourceExtendedBodyLegendre F.potential p < ⊤ :=
    MeasureTheory.ae_lt_top'
      (measurable_sourceExtendedBodyLegendre F.potential).aemeasurable
      F.legendreFinite.ne
  have hmono :
      (∫ p in K.carrier, legendreTransform D.potential p
        ∂(volume : Measure (Space n))) ≤
      ∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal + ε
        ∂(volume : Measure (Space n)) := by
    apply MeasureTheory.integral_mono_ae
      (sourceMomentLegendre_integrableOn D)
      (hdual.add hconst)
    filter_upwards [hfinite] with p hp
    exact recoveryLegendre_le_extended F D ε hlower p hp.ne
  unfold sourceMomentBodyEnergy
  calc
    (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier, legendreTransform D.potential p
          ∂(volume : Measure (Space n))) ≤
      (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier,
          (sourceExtendedBodyLegendre F.potential p).toReal + ε
          ∂(volume : Measure (Space n))) :=
        mul_le_mul_of_nonneg_left hmono
          (inv_nonneg.mpr K.volume_pos.le)
    _ = finiteEnergySourceBodyEnergy F + ε := by
      rw [MeasureTheory.integral_add hdual hconst,
        MeasureTheory.setIntegral_const,
        finiteEnergySourceBodyEnergy_eq_setIntegral]
      simp [normalizedVolume, measureReal_def, smul_eq_mul]
      have hvol :
          ((volume : Measure (Space n)) K.carrier).toReal ≠ 0 := by
        simpa [normalizedVolume] using K.volume_pos.ne'
      field_simp [hvol]
theorem exists_smooth_sourceSupportClipping_recovery {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ D : SourceMomentPotential K,
      (∀ x : Space n,
        |D.potential x - sourceSupportClipping F R x| < ε) ∧
      sourceMomentBodyEnergy D ≤
        finiteEnergySourceBodyEnergy F + ε := by
  let L : ℝ :=
    (n : ℝ) * LaurentJetSeparatedness.bodyRadius K
  have hL : 0 ≤ L :=
    mul_nonneg (Nat.cast_nonneg n)
      (LaurentJetSeparatedness.bodyRadius_pos K).le
  let δ : ℝ := ε / (L + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  let ρ : ContDiffBump (0 : Space n) :=
    ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let D := sourceClippedMollificationMoment F R hR ρ
  have hsmall : L * δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0 < L + 1)).mpr
    nlinarith
  have hclose : ∀ x : Space n,
      |D.potential x - sourceSupportClipping F R x| < ε := by
    intro x
    have hdist := dist_mollifiedSourceSupportClipping_le F hR ρ x
    rw [Real.dist_eq] at hdist
    exact hdist.trans_lt (by simpa [L, ρ] using hsmall)
  refine ⟨D, hclose, ?_⟩
  apply sourceMomentBodyEnergy_le_finiteEnergy_add F D ε
  intro x
  have hclip := sourceSupportClipping_ge F R x
  have hnear := (abs_lt.mp (hclose x)).1
  linarith
theorem sourceClippingRecovery_partition_bounds {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (D : SourceMomentPotential K)
    (R ε : ℝ)
    (hclose : ∀ x : Space n,
      |D.potential x - sourceSupportClipping F R x| ≤ ε) :
    Real.exp (-ε) *
        (∫ x : Space n,
          Real.exp (-sourceSupportClipping F R x)
          ∂(volume : Measure (Space n))) ≤
      sourceMomentPartition D ∧
    sourceMomentPartition D ≤
      Real.exp ε *
        (∫ x : Space n,
          Real.exp (-sourceSupportClipping F R x)
          ∂(volume : Measure (Space n))) := by
  have hclip := sourceSupportClippingDensity_integrable F R
  have hsource := sourceMomentDensity_integrable D
  constructor
  · calc
      Real.exp (-ε) *
          (∫ x : Space n,
            Real.exp (-sourceSupportClipping F R x)
            ∂(volume : Measure (Space n))) =
          ∫ x : Space n,
            Real.exp (-ε) *
              Real.exp (-sourceSupportClipping F R x)
            ∂(volume : Measure (Space n)) :=
            (MeasureTheory.integral_const_mul _ _).symm
      _ ≤ (∫ x : Space n,
            Real.exp (-D.potential x)
            ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.integral_mono
              (hclip.const_mul (Real.exp (-ε))) hsource
            intro x
            change
              Real.exp (-ε) *
                  Real.exp (-sourceSupportClipping F R x) ≤
                Real.exp (-D.potential x)
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have h := (abs_le.mp (hclose x)).2
            linarith
      _ = sourceMomentPartition D := rfl
  · calc
      sourceMomentPartition D =
          (∫ x : Space n,
            Real.exp (-D.potential x)
            ∂(volume : Measure (Space n))) := rfl
      _ ≤ ∫ x : Space n,
            Real.exp ε *
              Real.exp (-sourceSupportClipping F R x)
            ∂(volume : Measure (Space n)) := by
            apply MeasureTheory.integral_mono hsource
              (hclip.const_mul (Real.exp ε))
            intro x
            change
              Real.exp (-D.potential x) ≤
                Real.exp ε *
                  Real.exp (-sourceSupportClipping F R x)
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have h := (abs_le.mp (hclose x)).1
            linarith
      _ = Real.exp ε *
          (∫ x : Space n,
            Real.exp (-sourceSupportClipping F R x)
            ∂(volume : Measure (Space n))) :=
          MeasureTheory.integral_const_mul _ _
theorem exists_smooth_finiteEnergySource_recovery_sequence {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    ∃ D : ℕ → SourceMomentPotential K,
      (∀ (j : ℕ) (x : Space n),
        |(D j).potential x - sourceSupportClipping F (j : ℝ) x| <
          1 / ((j : ℝ) + 1)) ∧
      (∀ j : ℕ,
        sourceMomentBodyEnergy (D j) ≤
          finiteEnergySourceBodyEnergy F + 1 / ((j : ℝ) + 1)) ∧
      Tendsto
        (fun j => sourceMomentPartition (D j))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε : ∀ j : ℕ, 0 < ε j := by
    intro j
    dsimp [ε]
    positivity
  have hchoose :
      ∀ j : ℕ, ∃ D : SourceMomentPotential K,
        (∀ x : Space n,
          |D.potential x - sourceSupportClipping F (j : ℝ) x| <
            ε j) ∧
        sourceMomentBodyEnergy D ≤
          finiteEnergySourceBodyEnergy F + ε j := by
    intro j
    exact exists_smooth_sourceSupportClipping_recovery
      F (Nat.cast_nonneg j) (hε j)
  choose D hclose henergy using hchoose
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hclip := tendsto_sourceSupportClippingPartition F
  have hnegexp :
      Tendsto (fun j => Real.exp (-ε j)) atTop (𝓝 1) := by
    have hnegzero :
        Tendsto (fun j => -ε j) atTop (𝓝 (0 : ℝ)) := by
      simpa using hεzero.neg
    have h := (Real.continuous_exp.tendsto (0 : ℝ)).comp hnegzero
    rw [Real.exp_zero] at h
    exact h.congr'
      (Filter.Eventually.of_forall fun _ => rfl)
  have hposexp :
      Tendsto (fun j => Real.exp (ε j)) atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto (0 : ℝ)).comp hεzero
    rw [Real.exp_zero] at h
    exact h.congr'
      (Filter.Eventually.of_forall fun _ => rfl)
  have hlower :
      Tendsto
        (fun j =>
          Real.exp (-ε j) *
            (∫ x : Space n,
              Real.exp (-sourceSupportClipping F (j : ℝ) x)
              ∂(volume : Measure (Space n))))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
    simpa using hnegexp.mul hclip
  have hupper :
      Tendsto
        (fun j =>
          Real.exp (ε j) *
            (∫ x : Space n,
              Real.exp (-sourceSupportClipping F (j : ℝ) x)
              ∂(volume : Measure (Space n))))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
    simpa using hposexp.mul hclip
  have hpart :
      Tendsto
        (fun j => sourceMomentPartition (D j))
        atTop (𝓝 (finiteEnergySourcePartition F)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlower hupper
    · intro j
      exact
        (sourceClippingRecovery_partition_bounds F (D j)
          (j : ℝ) (ε j) (fun x => (hclose j x).le)).1
    · intro j
      exact
        (sourceClippingRecovery_partition_bounds F (D j)
          (j : ℝ) (ε j) (fun x => (hclose j x).le)).2
  refine ⟨D, ?_, ?_, hpart⟩
  · intro j x
    exact hclose j x
  · intro j
    exact henergy j
theorem finiteEnergySourceBermanFunctional_le_sSup {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    finiteEnergySourceBermanFunctional F ≤
      sSup
        (Set.range
          (fun D : SourceMomentPotential K =>
            sourceMomentBermanFunctional D)) := by
  obtain ⟨D, _hclose, henergy, hpartition⟩ :=
    exists_smooth_finiteEnergySource_recovery_sequence F
  let S : ℝ :=
    sSup
      (Set.range
        (fun G : SourceMomentPotential K =>
          sourceMomentBermanFunctional G))
  have hεzero :
      Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1))
        atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlog :=
    hpartition.log (finiteEnergySourcePartition_pos F).ne'
  have hlower :
      Tendsto
        (fun j =>
          Real.log (sourceMomentPartition (D j)) -
            (finiteEnergySourceBodyEnergy F +
              1 / ((j : ℝ) + 1)))
        atTop (𝓝 (finiteEnergySourceBermanFunctional F)) := by
    simpa [finiteEnergySourceBermanFunctional] using
      hlog.sub (tendsto_const_nhds.add hεzero)
  change finiteEnergySourceBermanFunctional F ≤ S
  apply le_of_tendsto hlower
  filter_upwards with j
  have hsup : sourceMomentBermanFunctional (D j) ≤ S :=
    le_csSup
      (sourceMomentBermanFunctional_bddAbove K)
      (show
        sourceMomentBermanFunctional (D j) ∈
          Set.range
            (fun G : SourceMomentPotential K =>
              sourceMomentBermanFunctional G)
        from ⟨D j, rfl⟩)
  unfold sourceMomentBermanFunctional at hsup
  linarith [henergy j]
theorem exists_finiteEnergySourceBerman_exact_optimizer {n : ℕ}
    (K : CenteredBody n) :
    ∃ F : SourceFiniteEnergyPotential K,
      finiteEnergySourceBermanFunctional F =
        sSup
          (Set.range
            (fun D : SourceMomentPotential K =>
              sourceMomentBermanFunctional D)) ∧
      ∀ G : SourceFiniteEnergyPotential K,
        finiteEnergySourceBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F := by
  obtain ⟨F, _D, _φ, _hmono, _hconv, _hmax, _hdom, hupper⟩ :=
    exists_finiteEnergySourceBerman_optimizer K
  have heq := le_antisymm
    (finiteEnergySourceBermanFunctional_le_sSup F) hupper
  refine ⟨F, heq, ?_⟩
  intro G
  rw [heq]
  exact finiteEnergySourceBermanFunctional_le_sSup G
end MomentConvexRecovery
namespace MomentFirstVariation
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentFunctionalCoercivity MomentOptimizer MomentWeakFirstVariation
open scoped BigOperators ENNReal NNReal Topology
theorem finiteEnergySourcePhase_actualGradient_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (z : Space n) :
    phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        F.potential z ≤
      phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        F.potential x := by
  let line : ℝ →ᵃ[ℝ] Space n := AffineMap.lineMap x z
  have hconv : ConvexOn ℝ Set.univ
      (fun t : ℝ => F.potential (line t)) := by
    simpa [Function.comp_def] using F.convex.comp_affineMap line
  have hline : HasDerivAt
      (fun t : ℝ => line t) (z - x) 0 := by
    simpa [line, AffineMap.lineMap_apply, Function.comp_def] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (z - x)).add_const x
  have hlinezero : line (0 : ℝ) = x := by
    simp [line]
  have hderiv : HasDerivAt
      (fun t : ℝ => F.potential (line t))
      ((fderiv ℝ F.potential x) (z - x)) 0 := by
    simpa [Function.comp_def] using
      hx.hasFDerivAt.comp_hasDerivAt_of_eq
        (0 : ℝ) hline hlinezero.symm
  have hslope := hconv.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hderiv
  have htangent :
      (fderiv ℝ F.potential x) (z - x) ≤
        F.potential z - F.potential x := by
    simpa [slope_def_field, line] using hslope
  rw [← SpatialBergmanFatouScheffe.pairing_actualGradient_eq_fderiv]
    at htangent
  unfold phase
  have hpair :
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) (z - x) =
        SupportFunction.pairing
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) z -
        SupportFunction.pairing
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) x := by
    simp [SupportFunction.pairing, mul_sub,
      Finset.sum_sub_distrib]
  rw [hpair] at htangent
  linarith
theorem finiteEnergySourceGradient_pairing_le_support
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (v : Space n) :
    SupportFunction.pairing
      (SpatialBergmanFatouScheffe.actualGradient
        F.potential x) v ≤
      SupportFunction.supportFunction K.carrier v := by
  by_contra hnot
  have hgap : 0 <
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) v -
        SupportFunction.supportFunction K.carrier v := by
    linarith [lt_of_not_ge hnot]
  let gap : ℝ :=
    SupportFunction.pairing
      (SpatialBergmanFatouScheffe.actualGradient
        F.potential x) v -
      SupportFunction.supportFunction K.carrier v
  let C : ℝ :=
    SupportFunction.supportFunction K.carrier x -
      F.potential x
  have hgap' : 0 < gap := hgap
  have hC : 0 ≤ C := sub_nonneg.mpr (F.supportUpper x)
  let t : ℝ := 1 + (C + 1) / gap
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hphase :=
    finiteEnergySourcePhase_actualGradient_le F x hx (x + t • v)
  have hpair :
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) (x + t • v) =
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) x +
        t * SupportFunction.pairing
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) v := by
    rw [MonomialDivergence.pairing_add_right,
      MonomialDivergence.pairing_smul_right]
  unfold phase at hphase
  rw [hpair] at hphase
  have hsupp := GlobalBergmanKernelBound.supportFunction_add_smul_le
    K x v ht
  have hupper := F.supportUpper (x + t • v)
  have hbound : t * gap ≤ C := by
    dsimp [gap, C]
    linarith
  have heq : t * gap = gap + (C + 1) := by
    dsimp [t]
    field_simp
  linarith
theorem finiteEnergySourceGradient_mem_carrier
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x ∈ K.carrier := by
  classical
  by_contra hnot
  obtain ⟨f, c, hbody, hpoint⟩ :=
    geometric_hahn_banach_closed_point
      K.convex K.compact.isClosed hnot
  let v : Space n := MonomialDivergence.dualVector f
  have hnonempty : K.carrier.Nonempty :=
    K.fullDimensional.mono interior_subset
  have hsupport :
      SupportFunction.supportFunction K.carrier v ≤ c := by
    apply SupportFunction.supportFunction_le hnonempty v
    intro y hy
    have hf := hbody y hy
    rw [MonomialDivergence.dual_apply_eq_pairing] at hf
    exact hf.le
  have hgradient :=
    finiteEnergySourceGradient_pairing_le_support F x hx v
  rw [MonomialDivergence.dual_apply_eq_pairing] at hpoint
  exact (not_lt_of_ge (hgradient.trans hsupport)) hpoint
theorem ae_differentiableAt_finiteEnergySource
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)),
      DifferentiableAt ℝ
        (F.potential : Space n → ℝ) x := by
  exact F.lipschitz.ae_differentiableAt
theorem measurable_finiteEnergySourceGradient
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Measurable
      (SpatialBergmanFatouScheffe.actualGradient
        (F.potential : Space n → ℝ)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_fderiv_apply_const ℝ
    (F.potential : Space n → ℝ)
    (Pi.single i (1 : ℝ))
theorem finiteEnergySourceGibbs_ae_of_volume
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (P : Space n → Prop)
    (hP : ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)), P x) :
    ∀ᵐ x : Space n
      ∂(finiteEnergySourceGibbsProbability F), P x := by
  change ∀ᵐ x : Space n
    ∂((volume : Measure (Space n)).withDensity
      (fun y => ENNReal.ofReal
        (WeightedPoincare.normalizedDensity F.potential y))), P x
  exact (MeasureTheory.withDensity_absolutelyContinuous
    (volume : Measure (Space n))
    (fun y => ENNReal.ofReal
      (WeightedPoincare.normalizedDensity F.potential y))).ae_le hP
def finiteEnergySourceGradientPushforward
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Measure (Space n) :=
  Measure.map
    (SpatialBergmanFatouScheffe.actualGradient
      (F.potential : Space n → ℝ))
    (finiteEnergySourceGibbsProbability F)
theorem finiteEnergySourceGradientPushforward_univ
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    finiteEnergySourceGradientPushforward F Set.univ = 1 := by
  let : IsProbabilityMeasure
      (finiteEnergySourceGibbsProbability F) :=
    finiteEnergySourceGibbsProbability_isProbability F
  unfold finiteEnergySourceGradientPushforward
  rw [Measure.map_apply (measurable_finiteEnergySourceGradient F)
    MeasurableSet.univ]
  simp
theorem finiteEnergySourceGradientPushforward_isProbability
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    IsProbabilityMeasure
      (finiteEnergySourceGradientPushforward F) :=
  ⟨finiteEnergySourceGradientPushforward_univ F⟩
theorem finiteEnergySourceExtendedLegendre_actualGradient
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    sourceExtendedBodyLegendre F.potential
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) =
      ENNReal.ofReal
        (phase
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x)
          F.potential x) := by
  let p : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have hmax : ∀ z : Space n,
      phase p F.potential z ≤ phase p F.potential x :=
    fun z => finiteEnergySourcePhase_actualGradient_le F x hx z
  have hbdd : BddAbove (Set.range (phase p F.potential)) := by
    refine ⟨phase p F.potential x, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hmax z
  rw [sourceExtendedBodyLegendre_eq_of_bddAbove
    F.potential p hbdd]
  congr 1
  unfold legendreTransform
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨z, rfl⟩
    exact hmax z
  · exact le_csSup hbdd ⟨x, rfl⟩
theorem finiteEnergySourcePhase_actualGradient_nonneg
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    0 ≤ phase
      (SpatialBergmanFatouScheffe.actualGradient
        F.potential x)
      F.potential x := by
  have h := finiteEnergySourcePhase_actualGradient_le
    F x hx (0 : Space n)
  simpa [phase, SupportFunction.pairing,
    F.normalized] using h
theorem finiteEnergySourceExtendedLegendre_actualGradient_toReal
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    (sourceExtendedBodyLegendre F.potential
      (SpatialBergmanFatouScheffe.actualGradient
        F.potential x)).toReal =
      phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        F.potential x := by
  rw [finiteEnergySourceExtendedLegendre_actualGradient F x hx,
    ENNReal.toReal_ofReal
      (finiteEnergySourcePhase_actualGradient_nonneg F x hx)]
end MomentFirstVariation
namespace MomentTargetGeodesic
open Set Function Filter MeasureTheory TopologicalSpace
open LaplaceAsymptotics MomentFunctionalCoercivity MomentMinimizer MomentOptimizer
open MomentWeakFirstVariation MomentFirstVariation
open scoped BigOperators ENNReal NNReal Topology
def normalizedTargetBodyMeasure {n : ℕ}
    (K : CenteredBody n) : Measure (Space n) :=
  ((volume : Measure (Space n)) K.carrier)⁻¹ •
    ((volume : Measure (Space n)).restrict K.carrier)
theorem centeredBody_volume_ne_zero_top {n : ℕ}
    (K : CenteredBody n) :
    (volume : Measure (Space n)) K.carrier ≠ 0 ∧
      (volume : Measure (Space n)) K.carrier ≠ ⊤ := by
  refine ⟨?_, K.compact.measure_ne_top⟩
  intro hzero
  have hpos := K.volume_pos
  simp [normalizedVolume, hzero] at hpos
theorem normalizedTargetBodyMeasure_univ {n : ℕ}
    (K : CenteredBody n) :
    normalizedTargetBodyMeasure K Set.univ = 1 := by
  unfold normalizedTargetBodyMeasure
  rw [Measure.smul_apply, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel
    (centeredBody_volume_ne_zero_top K).1
    (centeredBody_volume_ne_zero_top K).2
theorem normalizedTargetBodyMeasure_isProbability {n : ℕ}
    (K : CenteredBody n) :
    IsProbabilityMeasure (normalizedTargetBodyMeasure K) :=
  ⟨normalizedTargetBodyMeasure_univ K⟩
theorem integral_normalizedTargetBodyMeasure {n : ℕ}
    (K : CenteredBody n)
    (v : Space n → ℝ) :
    (∫ p : Space n, v p
      ∂(normalizedTargetBodyMeasure K)) =
      (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier, v p
          ∂(volume : Measure (Space n))) := by
  unfold normalizedTargetBodyMeasure
  rw [MeasureTheory.integral_smul_measure]
  simp [normalizedVolume, smul_eq_mul]
theorem integral_finiteEnergySourceGradientPushforward {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ)) :
    (∫ p : Space n, v p
      ∂(finiteEnergySourceGradientPushforward F)) =
      (∫ x : Space n,
        v (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        ∂(finiteEnergySourceGibbsProbability F)) := by
  unfold finiteEnergySourceGradientPushforward
  exact MeasureTheory.integral_map
    (measurable_finiteEnergySourceGradient F).aemeasurable
    v.continuous.aestronglyMeasurable
theorem finiteEnergySourceExtendedLegendre_zero {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    sourceExtendedBodyLegendre F.potential
      (0 : Space n) = 0 := by
  apply le_antisymm
  · unfold sourceExtendedBodyLegendre
    apply iSup_le
    intro j
    have hphase :
        phase (0 : Space n) F.potential
          (TopologicalSpace.denseSeq (Space n) j) ≤ 0 := by
      simpa [phase, SupportFunction.pairing] using
        neg_nonpos.mpr
          (F.nonnegative
            (TopologicalSpace.denseSeq (Space n) j))
    rw [ENNReal.ofReal_eq_zero.mpr hphase]
  · exact bot_le
def finiteEnergyFiniteTargetSet {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Set (Space n) :=
  {p | p ∈ K.carrier ∧
    sourceExtendedBodyLegendre F.potential p ≠ ⊤}
theorem zero_mem_finiteEnergyFiniteTargetSet {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    (0 : Space n) ∈ finiteEnergyFiniteTargetSet F := by
  refine ⟨interior_subset
    (LatticeAsymptotics.zero_mem_interior K), ?_⟩
  rw [finiteEnergySourceExtendedLegendre_zero F]
  exact ENNReal.zero_ne_top
theorem finiteEnergyFiniteTargetSet_nonempty {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    (finiteEnergyFiniteTargetSet F).Nonempty :=
  ⟨0, zero_mem_finiteEnergyFiniteTargetSet F⟩
theorem ae_mem_finiteEnergyFiniteTargetSet {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    ∀ᵐ p : Space n
      ∂((volume : Measure (Space n)).restrict K.carrier),
      p ∈ finiteEnergyFiniteTargetSet F := by
  have hfinite := MeasureTheory.ae_lt_top'
    (measurable_sourceExtendedBodyLegendre F.potential).aemeasurable
    F.legendreFinite.ne
  filter_upwards
    [MeasureTheory.ae_restrict_mem K.compact.measurableSet, hfinite]
    with p hp htop
  exact ⟨hp, ne_of_lt htop⟩
theorem finiteEnergyFiniteTarget_fenchel {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F)
    (x : Space n) :
    SupportFunction.pairing p x -
        (sourceExtendedBodyLegendre F.potential p).toReal ≤
      F.potential x := by
  have hphase :=
    ofReal_phase_le_sourceExtendedBodyLegendre F.potential p x
  rw [← ENNReal.ofReal_toReal hp.2] at hphase
  have hreal :=
    (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hphase
  change
    SupportFunction.pairing p x - F.potential x ≤
      (sourceExtendedBodyLegendre F.potential p).toReal at hreal
  linarith
def finiteEnergyTargetTestBound {n : ℕ}
    (K : CenteredBody n)
    (v : C(Space n, ℝ)) : ℝ :=
  max 0 (sSup ((fun p : Space n => |v p|) '' K.carrier))
theorem finiteEnergyTargetTestBound_nonneg {n : ℕ}
    (K : CenteredBody n)
    (v : C(Space n, ℝ)) :
    0 ≤ finiteEnergyTargetTestBound K v :=
  le_max_left _ _
theorem abs_targetTest_le_finiteEnergyTargetTestBound {n : ℕ}
    (K : CenteredBody n)
    (v : C(Space n, ℝ))
    {p : Space n} (hp : p ∈ K.carrier) :
    |v p| ≤ finiteEnergyTargetTestBound K v := by
  have hbdd : BddAbove
      ((fun q : Space n => |v q|) '' K.carrier) :=
    K.compact.bddAbove_image v.continuous.abs.continuousOn
  exact (le_csSup hbdd ⟨p, hp, rfl⟩).trans
    (le_max_right 0 _)
def finiteEnergyTargetDualPhase {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (p x : Space n) : ℝ :=
  SupportFunction.pairing p x -
    (sourceExtendedBodyLegendre F.potential p).toReal - t * v p
theorem finiteEnergyTargetDualPhase_le {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F)
    (x : Space n) :
    finiteEnergyTargetDualPhase F v t p x ≤
      SupportFunction.supportFunction K.carrier x +
        |t| * finiteEnergyTargetTestBound K v := by
  have hpair := SupportFunction.pairing_le_supportFunction
    K.compact hp.1 x
  have htest := abs_targetTest_le_finiteEnergyTargetTestBound
    K v hp.1
  have ht : -t * v p ≤ |t| * finiteEnergyTargetTestBound K v := by
    calc
      -t * v p = -(t * v p) := by ring
      _ ≤ |t * v p| := neg_le_abs _
      _ = |t| * |v p| := abs_mul _ _
      _ ≤ |t| * finiteEnergyTargetTestBound K v :=
        mul_le_mul_of_nonneg_left htest (abs_nonneg t)
  have hdual := ENNReal.toReal_nonneg
    (a := sourceExtendedBodyLegendre F.potential p)
  unfold finiteEnergyTargetDualPhase
  linarith
def finiteEnergyTargetGeodesic {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) : ℝ :=
  sSup
    ((fun p : Space n =>
      finiteEnergyTargetDualPhase F v t p x) ''
        finiteEnergyFiniteTargetSet F)
theorem finiteEnergyTargetDualPhase_bddAbove {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    BddAbove
      ((fun p : Space n =>
        finiteEnergyTargetDualPhase F v t p x) ''
          finiteEnergyFiniteTargetSet F) := by
  refine ⟨SupportFunction.supportFunction K.carrier x +
    |t| * finiteEnergyTargetTestBound K v, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact finiteEnergyTargetDualPhase_le F v t hp x
theorem finiteEnergyTargetDualPhase_le_geodesic {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F)
    (x : Space n) :
    finiteEnergyTargetDualPhase F v t p x ≤
      finiteEnergyTargetGeodesic F v t x := by
  exact le_csSup
    (finiteEnergyTargetDualPhase_bddAbove F v t x)
    ⟨p, hp, rfl⟩
theorem finiteEnergyTargetGeodesic_zero_le {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n) :
    finiteEnergyTargetGeodesic F v 0 x ≤ F.potential x := by
  unfold finiteEnergyTargetGeodesic
  apply csSup_le
    ((finiteEnergyFiniteTargetSet_nonempty F).image _)
  rintro _ ⟨p, hp, rfl⟩
  simpa [finiteEnergyTargetDualPhase] using
    finiteEnergyFiniteTarget_fenchel F hp x
theorem finiteEnergyTargetGeodesic_lipschitz {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (finiteEnergyTargetGeodesic F v t) := by
  unfold sourceBodyLipschitzConstant
  apply LipschitzWith.of_le_add_mul'
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K)
  intro x y
  unfold finiteEnergyTargetGeodesic
  apply csSup_le
    ((finiteEnergyFiniteTargetSet_nonempty F).image _)
  rintro _ ⟨p, hp, rfl⟩
  have hy := le_csSup
    (finiteEnergyTargetDualPhase_bddAbove F v t y)
    (show finiteEnergyTargetDualPhase F v t p y ∈
      (fun q : Space n =>
        finiteEnergyTargetDualPhase F v t q y) ''
          finiteEnergyFiniteTargetSet F
      from ⟨p, hp, rfl⟩)
  have hpair :
      SupportFunction.pairing p x -
          SupportFunction.pairing p y ≤
        ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) *
            dist x y := by
    have hpbound :=
      LaurentJetSeparatedness.norm_le_bodyRadius
        K p hp.1
    have h :=
      MonomialDivergence.abs_pairing_le_dimension_mul_norm
        p (x - y)
    rw [dist_eq_norm]
    calc
      SupportFunction.pairing p x -
          SupportFunction.pairing p y =
        SupportFunction.pairing p (x - y) := by
          simp [SupportFunction.pairing, mul_sub,
            Finset.sum_sub_distrib]
      _ ≤ |SupportFunction.pairing p (x - y)| :=
        le_abs_self _
      _ ≤ ((n : ℝ) * ‖p‖) * ‖x - y‖ := h
      _ ≤ ((n : ℝ) *
          LaurentJetSeparatedness.bodyRadius K) *
            ‖x - y‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpbound
            (Nat.cast_nonneg n)) (norm_nonneg _)
  unfold finiteEnergyTargetDualPhase at hy ⊢
  linarith
theorem continuous_finiteEnergyTargetGeodesic {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    Continuous (finiteEnergyTargetGeodesic F v t) :=
  (finiteEnergyTargetGeodesic_lipschitz F v t).continuous
theorem convexOn_finiteEnergyTargetGeodesic {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    ConvexOn ℝ Set.univ (finiteEnergyTargetGeodesic F v t) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  unfold finiteEnergyTargetGeodesic
  apply csSup_le
    ((finiteEnergyFiniteTargetSet_nonempty F).image _)
  rintro _ ⟨p, hp, rfl⟩
  have hpx := le_csSup
    (finiteEnergyTargetDualPhase_bddAbove F v t x)
    (show finiteEnergyTargetDualPhase F v t p x ∈
      (fun q : Space n =>
        finiteEnergyTargetDualPhase F v t q x) ''
          finiteEnergyFiniteTargetSet F from ⟨p, hp, rfl⟩)
  have hpy := le_csSup
    (finiteEnergyTargetDualPhase_bddAbove F v t y)
    (show finiteEnergyTargetDualPhase F v t p y ∈
      (fun q : Space n =>
        finiteEnergyTargetDualPhase F v t q y) ''
          finiteEnergyFiniteTargetSet F from ⟨p, hp, rfl⟩)
  have hphase :
      finiteEnergyTargetDualPhase F v t p (a • x + b • y) =
        a * finiteEnergyTargetDualPhase F v t p x +
          b * finiteEnergyTargetDualPhase F v t p y := by
    unfold finiteEnergyTargetDualPhase
    rw [MonomialDivergence.pairing_add_right,
      MonomialDivergence.pairing_smul_right,
      MonomialDivergence.pairing_smul_right]
    linear_combination
      ((sourceExtendedBodyLegendre F.potential p).toReal +
        t * v p) * hab
  change
    finiteEnergyTargetDualPhase F v t p (a • x + b • y) ≤
      a * sSup
        ((fun q : Space n =>
          finiteEnergyTargetDualPhase F v t q x) ''
            finiteEnergyFiniteTargetSet F) +
      b * sSup
        ((fun q : Space n =>
          finiteEnergyTargetDualPhase F v t q y) ''
            finiteEnergyFiniteTargetSet F)
  rw [hphase]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hpx ha)
    (mul_le_mul_of_nonneg_left hpy hb)
theorem finiteEnergyTargetGeodesic_zero_eq_of_differentiableAt
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    finiteEnergyTargetGeodesic F v 0 x = F.potential x := by
  apply le_antisymm (finiteEnergyTargetGeodesic_zero_le F v x)
  let p : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have hpbody : p ∈ K.carrier :=
    finiteEnergySourceGradient_mem_carrier F x hx
  have hpfinite :
      sourceExtendedBodyLegendre F.potential p ≠ ⊤ := by
    rw [finiteEnergySourceExtendedLegendre_actualGradient F x hx]
    exact ENNReal.ofReal_ne_top
  have hgeodesic := finiteEnergyTargetDualPhase_le_geodesic
    F v 0 (show p ∈ finiteEnergyFiniteTargetSet F
      from ⟨hpbody, hpfinite⟩) x
  have hleg :=
    finiteEnergySourceExtendedLegendre_actualGradient_toReal
      F x hx
  change
    SupportFunction.pairing p x -
      (sourceExtendedBodyLegendre F.potential p).toReal -
        0 * v p ≤ finiteEnergyTargetGeodesic F v 0 x at hgeodesic
  change
    (sourceExtendedBodyLegendre F.potential p).toReal =
      SupportFunction.pairing p x - F.potential x at hleg
  linarith
theorem finiteEnergyTargetGeodesic_zero_eq {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n) :
    finiteEnergyTargetGeodesic F v 0 x = F.potential x := by
  apply le_antisymm (finiteEnergyTargetGeodesic_zero_le F v x)
  have hdense : Dense
      {y : Space n |
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) y} :=
    MeasureTheory.Measure.dense_of_ae
      (ae_differentiableAt_finiteEnergySource F)
  have hclosed : IsClosed
      {y : Space n |
        F.potential y ≤ finiteEnergyTargetGeodesic F v 0 y} :=
    isClosed_le F.potential.continuous
      (continuous_finiteEnergyTargetGeodesic F v 0)
  have hsubset :
      {y : Space n |
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) y} ⊆
      {y : Space n |
        F.potential y ≤ finiteEnergyTargetGeodesic F v 0 y} := by
    intro y hy
    exact le_of_eq
      (finiteEnergyTargetGeodesic_zero_eq_of_differentiableAt
        F v y hy).symm
  exact (closure_minimal hsubset hclosed) (hdense x)
theorem finiteEnergyTargetGeodesic_uniform_error {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    |finiteEnergyTargetGeodesic F v t x - F.potential x| ≤
      |t| * finiteEnergyTargetTestBound K v := by
  apply abs_le.mpr
  constructor
  · have hzero : F.potential x ≤
        finiteEnergyTargetGeodesic F v t x +
          |t| * finiteEnergyTargetTestBound K v := by
      rw [← finiteEnergyTargetGeodesic_zero_eq F v x]
      change
        sSup
            ((fun p : Space n =>
              finiteEnergyTargetDualPhase F v 0 p x) ''
                finiteEnergyFiniteTargetSet F) ≤
          finiteEnergyTargetGeodesic F v t x +
            |t| * finiteEnergyTargetTestBound K v
      apply csSup_le
        ((finiteEnergyFiniteTargetSet_nonempty F).image _)
      rintro _ ⟨p, hp, rfl⟩
      have hphase := finiteEnergyTargetDualPhase_le_geodesic
        F v t hp x
      have htest := abs_targetTest_le_finiteEnergyTargetTestBound
        K v hp.1
      have ht : t * v p ≤
          |t| * finiteEnergyTargetTestBound K v := by
        calc
          t * v p ≤ |t * v p| := le_abs_self _
          _ = |t| * |v p| := abs_mul _ _
          _ ≤ |t| * finiteEnergyTargetTestBound K v :=
            mul_le_mul_of_nonneg_left htest (abs_nonneg t)
      unfold finiteEnergyTargetDualPhase at hphase
      change
        SupportFunction.pairing p x -
          (sourceExtendedBodyLegendre F.potential p).toReal -
            0 * v p ≤
          finiteEnergyTargetGeodesic F v t x +
            |t| * finiteEnergyTargetTestBound K v
      linarith
    linarith
  · have hupper :
        finiteEnergyTargetGeodesic F v t x ≤
          F.potential x +
            |t| * finiteEnergyTargetTestBound K v := by
      unfold finiteEnergyTargetGeodesic
      apply csSup_le
        ((finiteEnergyFiniteTargetSet_nonempty F).image _)
      rintro _ ⟨p, hp, rfl⟩
      have hfenchel := finiteEnergyFiniteTarget_fenchel F hp x
      have htest := abs_targetTest_le_finiteEnergyTargetTestBound
        K v hp.1
      have ht : -t * v p ≤
          |t| * finiteEnergyTargetTestBound K v := by
        calc
          -t * v p = -(t * v p) := by ring
          _ ≤ |t * v p| := neg_le_abs _
          _ = |t| * |v p| := abs_mul _ _
          _ ≤ |t| * finiteEnergyTargetTestBound K v :=
            mul_le_mul_of_nonneg_left htest (abs_nonneg t)
      unfold finiteEnergyTargetDualPhase
      linarith
    linarith
theorem finiteEnergyTargetGeodesic_densityIntegrable {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    Integrable
      (fun x : Space n =>
        Real.exp (-finiteEnergyTargetGeodesic F v t x))
      (volume : Measure (Space n)) := by
  let A : ℝ := |t| * finiteEnergyTargetTestBound K v
  have hmeas : AEStronglyMeasurable
      (fun x : Space n =>
        Real.exp (-finiteEnergyTargetGeodesic F v t x))
      (volume : Measure (Space n)) :=
    (Real.continuous_exp.comp
      (continuous_finiteEnergyTargetGeodesic F v t).neg).aestronglyMeasurable
  refine (F.densityIntegrable.const_mul
    (Real.exp A)).mono' hmeas ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := (abs_le.mp
    (finiteEnergyTargetGeodesic_uniform_error F v t x)).1
  dsimp [A]
  linarith
end MomentTargetGeodesic
namespace MomentTargetGeodesicVariation
open Set Function Filter MeasureTheory Metric
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentMinimizer
open MomentCoercivityCompactness MomentFunctionalCoercivity MomentNonlinearTightness MomentOptimizer
open MomentConvexRecovery MomentTargetGeodesic
open scoped BigOperators ENNReal NNReal Topology
theorem exists_finiteEnergySource_linear_coercivity
    {n : ℕ} (K : CenteredBody n) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 < B ∧
      ∀ (F : SourceFiniteEnergyPotential K)
        (x : Space n),
        δ * ‖x‖ ≤ F.potential x +
          B * finiteEnergySourceBodyEnergy F := by
  obtain ⟨ρ, δ, hρ, hδ, hball⟩ :=
    exists_uniform_inner_supportBall K
  have hpow : 0 < ρ ^ n := pow_pos hρ n
  refine ⟨δ, normalizedVolume K.carrier / ρ ^ n,
    hδ, div_pos K.volume_pos hpow, ?_⟩
  intro F x
  obtain ⟨c, hsubset, hpair⟩ := hball x
  have hfinite :
      (volume : Measure (Space n))
          (Metric.ball c (ρ / 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top K.compact.measure_ne_top
      (measure_mono hsubset)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        δ * ‖x‖ - F.potential x)
      (Metric.ball c (ρ / 2))
      (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const hfinite
  have hdualK :=
    finiteEnergySourceExtendedLegendre_integrableOn F
  have hdualball : IntegrableOn
      (fun p : Space n =>
        (sourceExtendedBodyLegendre F.potential p).toReal)
      (Metric.ball c (ρ / 2))
      (volume : Measure (Space n)) :=
    hdualK.mono_set hsubset
  have haeBall :
      ∀ᵐ p : Space n
        ∂((volume : Measure (Space n)).restrict
          (Metric.ball c (ρ / 2))),
        p ∈ finiteEnergyFiniteTargetSet F :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      hsubset (ae_mem_finiteEnergyFiniteTargetSet F)
  have hdualmass :
      (∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal
        ∂(volume : Measure (Space n))) =
      normalizedVolume K.carrier *
        finiteEnergySourceBodyEnergy F := by
    have h := finiteEnergySourceBodyEnergy_eq_setIntegral F
    have hvol := K.volume_pos.ne'
    field_simp at h
    linarith
  have hbound :
      ρ ^ n * (δ * ‖x‖ - F.potential x) ≤
        normalizedVolume K.carrier *
          finiteEnergySourceBodyEnergy F := by
    calc
      ρ ^ n * (δ * ‖x‖ - F.potential x) =
          (∫ _p in Metric.ball c (ρ / 2),
            δ * ‖x‖ - F.potential x
            ∂(volume : Measure (Space n))) := by
            rw [MeasureTheory.setIntegral_const,
              realVolume_uniformInnerBall c hρ]
            simp [smul_eq_mul]
      _ ≤ (∫ p in Metric.ball c (ρ / 2),
            (sourceExtendedBodyLegendre F.potential p).toReal
            ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.integral_mono_ae
              hconst hdualball
            filter_upwards
              [MeasureTheory.ae_restrict_mem
                Metric.isOpen_ball.measurableSet, haeBall]
              with p hp hpfinite
            have hpfenchel :=
              finiteEnergyFiniteTarget_fenchel F hpfinite x
            linarith [hpair p hp]
      _ ≤ (∫ p in K.carrier,
            (sourceExtendedBodyLegendre F.potential p).toReal
            ∂(volume : Measure (Space n))) := by
            apply MeasureTheory.setIntegral_mono_set hdualK
            · filter_upwards with p
              exact ENNReal.toReal_nonneg
            · exact Filter.Eventually.of_forall hsubset
      _ = normalizedVolume K.carrier *
            finiteEnergySourceBodyEnergy F := hdualmass
  have hdiv :
      δ * ‖x‖ - F.potential x ≤
        (normalizedVolume K.carrier *
          finiteEnergySourceBodyEnergy F) / ρ ^ n := by
    apply (le_div_iff₀ hpow).mpr
    simpa [mul_comm] using hbound
  calc
    δ * ‖x‖ ≤
        F.potential x +
          (normalizedVolume K.carrier *
            finiteEnergySourceBodyEnergy F) / ρ ^ n := by
          linarith
    _ = F.potential x +
        (normalizedVolume K.carrier / ρ ^ n) *
          finiteEnergySourceBodyEnergy F := by
          ring
theorem exists_finiteEnergyTargetGeodesic_linear_coercivity
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    ∃ δ C : ℝ, 0 < δ ∧
      ∀ x : Space n,
        δ * ‖x‖ ≤ finiteEnergyTargetGeodesic F v t x + C := by
  obtain ⟨δ, B, hδ, _hB, hcoerc⟩ :=
    exists_finiteEnergySource_linear_coercivity K
  refine ⟨δ,
    B * finiteEnergySourceBodyEnergy F +
      |t| * finiteEnergyTargetTestBound K v,
    hδ, ?_⟩
  intro x
  have hF := hcoerc F x
  have ht := (abs_le.mp
    (finiteEnergyTargetGeodesic_uniform_error F v t x)).1
  linarith
theorem exists_finiteEnergyTargetGeodesic_minimum
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    ∃ m : Space n,
      ∀ x : Space n,
        finiteEnergyTargetGeodesic F v t m ≤
          finiteEnergyTargetGeodesic F v t x := by
  obtain ⟨δ, C, hδ, hcoerc⟩ :=
    exists_finiteEnergyTargetGeodesic_linear_coercivity F v t
  let R : ℝ := max 0
    ((finiteEnergyTargetGeodesic F v t 0 + C) / δ)
  have hR : 0 ≤ R := le_max_left _ _
  have hzero :
      (0 : Space n) ∈
        Metric.closedBall (0 : Space n) R := by
    simpa [Metric.mem_closedBall] using hR
  obtain ⟨m, hm, hmin⟩ :=
    (isCompact_closedBall (0 : Space n) R).exists_isMinOn
      ⟨0, hzero⟩
      (continuous_finiteEnergyTargetGeodesic F v t).continuousOn
  refine ⟨m, ?_⟩
  intro x
  by_cases hx : x ∈ Metric.closedBall (0 : Space n) R
  · exact hmin hx
  · have hnorm : R < ‖x‖ := by
      have h := lt_of_not_ge
        (show ¬dist x (0 : Space n) ≤ R from
          (Metric.mem_closedBall.not.mp hx))
      simpa [dist_zero_right] using h
    have hthreshold :
        finiteEnergyTargetGeodesic F v t 0 + C ≤ δ * R := by
      have hmax :
          (finiteEnergyTargetGeodesic F v t 0 + C) / δ ≤ R :=
        le_max_right 0 _
      have h := (div_le_iff₀ hδ).mp hmax
      nlinarith
    have hxcoerc := hcoerc x
    have hzeroMin := hmin hzero
    change
      finiteEnergyTargetGeodesic F v t m ≤
        finiteEnergyTargetGeodesic F v t 0 at hzeroMin
    nlinarith [mul_lt_mul_of_pos_left hnorm hδ]
def finiteEnergyTargetGeodesicMinimumPoint
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) : Space n :=
  (exists_finiteEnergyTargetGeodesic_minimum F v t).choose
theorem finiteEnergyTargetGeodesicMinimumPoint_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    finiteEnergyTargetGeodesic F v t
        (finiteEnergyTargetGeodesicMinimumPoint F v t) ≤
      finiteEnergyTargetGeodesic F v t x :=
  (exists_finiteEnergyTargetGeodesic_minimum F v t).choose_spec x
theorem finiteEnergyTargetGeodesic_sub_le_support
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x y : Space n) :
    finiteEnergyTargetGeodesic F v t (x + y) -
        finiteEnergyTargetGeodesic F v t y ≤
      SupportFunction.supportFunction K.carrier x := by
  have hle :
      finiteEnergyTargetGeodesic F v t (x + y) ≤
        finiteEnergyTargetGeodesic F v t y +
          SupportFunction.supportFunction K.carrier x := by
    unfold finiteEnergyTargetGeodesic
    apply csSup_le
      ((finiteEnergyFiniteTargetSet_nonempty F).image _)
    rintro _ ⟨p, hp, rfl⟩
    have hphase := le_csSup
      (finiteEnergyTargetDualPhase_bddAbove F v t y)
      (show finiteEnergyTargetDualPhase F v t p y ∈
        (fun q : Space n =>
          finiteEnergyTargetDualPhase F v t q y) ''
            finiteEnergyFiniteTargetSet F
        from ⟨p, hp, rfl⟩)
    have hpair := SupportFunction.pairing_le_supportFunction
      K.compact hp.1 x
    unfold finiteEnergyTargetDualPhase at hphase ⊢
    change
      SupportFunction.pairing p (x + y) -
        (sourceExtendedBodyLegendre F.potential p).toReal -
          t * v p ≤
        sSup
          ((fun q : Space n =>
            SupportFunction.pairing q y -
              (sourceExtendedBodyLegendre F.potential q).toReal -
                t * v q) '' finiteEnergyFiniteTargetSet F) +
          SupportFunction.supportFunction K.carrier x
    rw [MonomialDivergence.pairing_add_right]
    linarith
  linarith
def minimumNormalizedTargetGeodesicContinuousMap
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) : C(Space n, ℝ) where
  toFun x :=
    finiteEnergyTargetGeodesic F v t
        (x + finiteEnergyTargetGeodesicMinimumPoint F v t) -
      finiteEnergyTargetGeodesic F v t
        (finiteEnergyTargetGeodesicMinimumPoint F v t)
  continuous_toFun :=
    ((continuous_finiteEnergyTargetGeodesic F v t).comp
      (continuous_id.add continuous_const)).sub continuous_const
theorem minimumNormalizedTargetGeodesicContinuousMap_zero
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    minimumNormalizedTargetGeodesicContinuousMap F v t 0 = 0 := by
  simp [minimumNormalizedTargetGeodesicContinuousMap]
theorem minimumNormalizedTargetGeodesicContinuousMap_nonneg
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    0 ≤ minimumNormalizedTargetGeodesicContinuousMap F v t x := by
  change
    0 ≤ finiteEnergyTargetGeodesic F v t
        (x + finiteEnergyTargetGeodesicMinimumPoint F v t) -
      finiteEnergyTargetGeodesic F v t
        (finiteEnergyTargetGeodesicMinimumPoint F v t)
  exact sub_nonneg.mpr
    (finiteEnergyTargetGeodesicMinimumPoint_le
      F v t (x + finiteEnergyTargetGeodesicMinimumPoint F v t))
theorem minimumNormalizedTargetGeodesicContinuousMap_le_support
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) :
    minimumNormalizedTargetGeodesicContinuousMap F v t x ≤
      SupportFunction.supportFunction K.carrier x := by
  exact finiteEnergyTargetGeodesic_sub_le_support F v t x
    (finiteEnergyTargetGeodesicMinimumPoint F v t)
theorem minimumNormalizedTargetGeodesicContinuousMap_lipschitz
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (minimumNormalizedTargetGeodesicContinuousMap F v t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h :=
    (finiteEnergyTargetGeodesic_lipschitz F v t).dist_le_mul
      (x + finiteEnergyTargetGeodesicMinimumPoint F v t)
      (y + finiteEnergyTargetGeodesicMinimumPoint F v t)
  simpa [minimumNormalizedTargetGeodesicContinuousMap,
    Real.dist_eq] using h
theorem convexOn_minimumNormalizedTargetGeodesicContinuousMap
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    ConvexOn ℝ Set.univ
      (minimumNormalizedTargetGeodesicContinuousMap F v t) := by
  let g := finiteEnergyTargetGeodesic F v t
  let z := finiteEnergyTargetGeodesicMinimumPoint F v t
  change ConvexOn ℝ Set.univ (fun x => g (x + z) - g z)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcombo :
      a • (x + z) + b • (y + z) =
        (a • x + b • y) + z := by
    calc
      a • (x + z) + b • (y + z) =
          (a • x + b • y) + (a • z + b • z) := by
        rw [smul_add, smul_add]
        abel
      _ = (a • x + b • y) + z := by
        rw [← add_smul, hab, one_smul]
  have h := (convexOn_finiteEnergyTargetGeodesic F v t).2
    (Set.mem_univ (x + z)) (Set.mem_univ (y + z)) ha hb hab
  rw [hcombo] at h
  change g ((a • x + b • y) + z) ≤
    a * g (x + z) + b * g (y + z) at h
  change g ((a • x + b • y) + z) - g z ≤
    a * (g (x + z) - g z) + b * (g (y + z) - g z)
  calc
    g ((a • x + b • y) + z) - g z ≤
        (a * g (x + z) + b * g (y + z)) - g z :=
      sub_le_sub_right h _
    _ = (a * g (x + z) + b * g (y + z)) -
        (a + b) * g z := by simp [hab]
    _ = a * (g (x + z) - g z) +
        b * (g (y + z) - g z) := by ring
theorem minimumNormalizedTargetGeodesic_densityIntegrable
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    Integrable
      (fun x : Space n =>
        Real.exp
          (-minimumNormalizedTargetGeodesicContinuousMap F v t x))
      (volume : Measure (Space n)) := by
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  have htranslate :=
    (finiteEnergyTargetGeodesic_densityIntegrable F v t).comp_add_right m
  have hscaled := htranslate.const_mul
    (Real.exp (finiteEnergyTargetGeodesic F v t m))
  have hfun :
      (fun x : Space n =>
        Real.exp
          (-minimumNormalizedTargetGeodesicContinuousMap F v t x)) =
      (fun x : Space n =>
        Real.exp (finiteEnergyTargetGeodesic F v t m) *
          Real.exp (-finiteEnergyTargetGeodesic F v t (x + m))) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    change
      -(finiteEnergyTargetGeodesic F v t (x + m) -
        finiteEnergyTargetGeodesic F v t m) =
      finiteEnergyTargetGeodesic F v t m +
        -finiteEnergyTargetGeodesic F v t (x + m)
    ring
  rw [hfun]
  exact hscaled
def minimumNormalizedTargetGeodesicDualMajorant
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (p : Space n) : ℝ :=
  (sourceExtendedBodyLegendre F.potential p).toReal + t * v p -
    SupportFunction.pairing p
      (finiteEnergyTargetGeodesicMinimumPoint F v t) +
    finiteEnergyTargetGeodesic F v t
      (finiteEnergyTargetGeodesicMinimumPoint F v t)
theorem minimumNormalizedTargetGeodesicDualMajorant_nonneg
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F) :
    0 ≤ minimumNormalizedTargetGeodesicDualMajorant F v t p := by
  have hphase := finiteEnergyTargetDualPhase_le_geodesic
    F v t hp (finiteEnergyTargetGeodesicMinimumPoint F v t)
  unfold finiteEnergyTargetDualPhase at hphase
  unfold minimumNormalizedTargetGeodesicDualMajorant
  linarith
theorem minimumNormalizedTargetGeodesic_phase_le_majorant
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F)
    (x : Space n) :
    phase p (minimumNormalizedTargetGeodesicContinuousMap F v t) x ≤
      minimumNormalizedTargetGeodesicDualMajorant F v t p := by
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  have hphase := finiteEnergyTargetDualPhase_le_geodesic
    F v t hp (x + m)
  unfold finiteEnergyTargetDualPhase at hphase
  change
    SupportFunction.pairing p x -
      (finiteEnergyTargetGeodesic F v t (x + m) -
        finiteEnergyTargetGeodesic F v t m) ≤
      (sourceExtendedBodyLegendre F.potential p).toReal +
        t * v p - SupportFunction.pairing p m +
          finiteEnergyTargetGeodesic F v t m
  rw [MonomialDivergence.pairing_add_right] at hphase
  linarith
theorem minimumNormalizedTargetGeodesic_extendedLegendre_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F) :
    sourceExtendedBodyLegendre
        (minimumNormalizedTargetGeodesicContinuousMap F v t) p ≤
      ENNReal.ofReal
        (minimumNormalizedTargetGeodesicDualMajorant F v t p) := by
  unfold sourceExtendedBodyLegendre
  apply iSup_le
  intro j
  exact ENNReal.ofReal_le_ofReal
    (minimumNormalizedTargetGeodesic_phase_le_majorant
      F v t hp (TopologicalSpace.denseSeq (Space n) j))
theorem minimumNormalizedTargetGeodesicDualMajorant_integrableOn
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    IntegrableOn
      (minimumNormalizedTargetGeodesicDualMajorant F v t)
      K.carrier (volume : Measure (Space n)) := by
  have hdual := finiteEnergySourceExtendedLegendre_integrableOn F
  have hv : IntegrableOn
      (fun p : Space n => v p)
      K.carrier (volume : Measure (Space n)) :=
    v.continuous.continuousOn.integrableOn_compact K.compact
  have hpair := sourceCenteredBody_pairing_integrableOn K
    (finiteEnergyTargetGeodesicMinimumPoint F v t)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t))
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  exact ((hdual.add (hv.const_mul t)).sub hpair).add hconst
theorem minimumNormalizedTargetGeodesic_legendreFinite
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    (∫⁻ p in K.carrier,
      sourceExtendedBodyLegendre
        (minimumNormalizedTargetGeodesicContinuousMap F v t) p
      ∂(volume : Measure (Space n))) < ⊤ := by
  have hnonneg :
      ∀ᵐ p : Space n
        ∂((volume : Measure (Space n)).restrict K.carrier),
        0 ≤ minimumNormalizedTargetGeodesicDualMajorant F v t p := by
    filter_upwards [ae_mem_finiteEnergyFiniteTargetSet F]
      with p hp
    exact minimumNormalizedTargetGeodesicDualMajorant_nonneg F v t hp
  have hmono :
      (∫⁻ p in K.carrier,
        sourceExtendedBodyLegendre
          (minimumNormalizedTargetGeodesicContinuousMap F v t) p
        ∂(volume : Measure (Space n))) ≤
      ∫⁻ p in K.carrier,
        ENNReal.ofReal
          (minimumNormalizedTargetGeodesicDualMajorant F v t p)
        ∂(volume : Measure (Space n)) := by
    apply MeasureTheory.lintegral_mono_ae
    filter_upwards [ae_mem_finiteEnergyFiniteTargetSet F]
      with p hp
    exact minimumNormalizedTargetGeodesic_extendedLegendre_le
      F v t hp
  have hmajor :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (minimumNormalizedTargetGeodesicDualMajorant_integrableOn
        F v t) hnonneg
  exact lt_of_le_of_lt hmono
    (by rw [← hmajor]; exact ENNReal.ofReal_lt_top)
def finiteEnergySourceOfTargetGeodesic
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) : SourceFiniteEnergyPotential K where
  potential := minimumNormalizedTargetGeodesicContinuousMap F v t
  normalized := minimumNormalizedTargetGeodesicContinuousMap_zero
    F v t
  lipschitz := minimumNormalizedTargetGeodesicContinuousMap_lipschitz
    F v t
  convex := convexOn_minimumNormalizedTargetGeodesicContinuousMap
    F v t
  nonnegative := minimumNormalizedTargetGeodesicContinuousMap_nonneg
    F v t
  supportUpper := minimumNormalizedTargetGeodesicContinuousMap_le_support
    F v t
  legendreFinite := minimumNormalizedTargetGeodesic_legendreFinite
    F v t
  densityIntegrable := minimumNormalizedTargetGeodesic_densityIntegrable
    F v t
def finiteEnergyTargetGeodesicPartition
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) : ℝ :=
  ∫ x : Space n,
    Real.exp (-finiteEnergyTargetGeodesic F v t x)
    ∂(volume : Measure (Space n))
theorem finiteEnergyTargetGeodesicPartition_pos
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    0 < finiteEnergyTargetGeodesicPartition F v t := by
  exact MeasureTheory.integral_exp_pos
    (finiteEnergyTargetGeodesic_densityIntegrable F v t)
theorem finiteEnergySourcePartition_ofTargetGeodesic
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    finiteEnergySourcePartition
        (finiteEnergySourceOfTargetGeodesic F v t) =
      Real.exp
        (finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t)) *
      finiteEnergyTargetGeodesicPartition F v t := by
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  unfold finiteEnergySourcePartition
  change
    (∫ x : Space n,
      Real.exp
        (-(finiteEnergyTargetGeodesic F v t (x + m) -
          finiteEnergyTargetGeodesic F v t m))
      ∂(volume : Measure (Space n))) =
      Real.exp (finiteEnergyTargetGeodesic F v t m) *
        finiteEnergyTargetGeodesicPartition F v t
  calc
    (∫ x : Space n,
      Real.exp
        (-(finiteEnergyTargetGeodesic F v t (x + m) -
          finiteEnergyTargetGeodesic F v t m))
      ∂(volume : Measure (Space n))) =
      ∫ x : Space n,
        Real.exp (finiteEnergyTargetGeodesic F v t m) *
          Real.exp (-finiteEnergyTargetGeodesic F v t (x + m))
        ∂(volume : Measure (Space n)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [← Real.exp_add]
        congr 1
        ring
    _ = Real.exp (finiteEnergyTargetGeodesic F v t m) *
        (∫ x : Space n,
          Real.exp (-finiteEnergyTargetGeodesic F v t (x + m))
          ∂(volume : Measure (Space n))) :=
      MeasureTheory.integral_const_mul _ _
    _ = Real.exp (finiteEnergyTargetGeodesic F v t m) *
        finiteEnergyTargetGeodesicPartition F v t := by
      rw [MeasureTheory.integral_add_right_eq_self
        (fun x : Space n =>
          Real.exp (-finiteEnergyTargetGeodesic F v t x)) m]
      rfl
theorem minimumNormalizedTargetGeodesic_extendedLegendre_toReal_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) {p : Space n}
    (hp : p ∈ finiteEnergyFiniteTargetSet F) :
    (sourceExtendedBodyLegendre
      (minimumNormalizedTargetGeodesicContinuousMap F v t) p).toReal ≤
      minimumNormalizedTargetGeodesicDualMajorant F v t p := by
  calc
    (sourceExtendedBodyLegendre
      (minimumNormalizedTargetGeodesicContinuousMap F v t) p).toReal ≤
      (ENNReal.ofReal
        (minimumNormalizedTargetGeodesicDualMajorant F v t p)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (minimumNormalizedTargetGeodesic_extendedLegendre_le
          F v t hp)
    _ = minimumNormalizedTargetGeodesicDualMajorant F v t p :=
      ENNReal.toReal_ofReal
        (minimumNormalizedTargetGeodesicDualMajorant_nonneg F v t hp)
theorem setIntegral_minimumNormalizedTargetGeodesicDualMajorant
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    (∫ p in K.carrier,
      minimumNormalizedTargetGeodesicDualMajorant F v t p
      ∂(volume : Measure (Space n))) =
      (∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal
        ∂(volume : Measure (Space n))) +
      t * (∫ p in K.carrier, v p
        ∂(volume : Measure (Space n))) +
      normalizedVolume K.carrier *
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t) := by
  have hdual := finiteEnergySourceExtendedLegendre_integrableOn F
  have hv : IntegrableOn
      (fun p : Space n => v p)
      K.carrier (volume : Measure (Space n)) :=
    v.continuous.continuousOn.integrableOn_compact K.compact
  have hpair := sourceCenteredBody_pairing_integrableOn K
    (finiteEnergyTargetGeodesicMinimumPoint F v t)
  have hconst : IntegrableOn
      (fun _ : Space n =>
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t))
      K.carrier (volume : Measure (Space n)) :=
    MeasureTheory.integrableOn_const K.compact.measure_ne_top
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  calc
    (∫ p in K.carrier,
      minimumNormalizedTargetGeodesicDualMajorant F v t p
      ∂(volume : Measure (Space n))) =
      (∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal +
          t * v p - SupportFunction.pairing p m
        ∂(volume : Measure (Space n))) +
      (∫ _p in K.carrier,
        finiteEnergyTargetGeodesic F v t m
        ∂(volume : Measure (Space n))) := by
      simpa [minimumNormalizedTargetGeodesicDualMajorant, m] using
        MeasureTheory.integral_add
          ((hdual.add (hv.const_mul t)).sub hpair) hconst
    _ =
      ((∫ p in K.carrier,
        (sourceExtendedBodyLegendre F.potential p).toReal
        ∂(volume : Measure (Space n))) +
        t * (∫ p in K.carrier, v p
          ∂(volume : Measure (Space n))) -
        (∫ p in K.carrier,
          SupportFunction.pairing p m
          ∂(volume : Measure (Space n)))) +
      (∫ _p in K.carrier,
        finiteEnergyTargetGeodesic F v t m
        ∂(volume : Measure (Space n))) := by
      congr 1
      calc
        (∫ p in K.carrier,
          (sourceExtendedBodyLegendre F.potential p).toReal +
            t * v p - SupportFunction.pairing p m
          ∂(volume : Measure (Space n))) =
          (∫ p in K.carrier,
            (sourceExtendedBodyLegendre F.potential p).toReal +
              t * v p
            ∂(volume : Measure (Space n))) -
          (∫ p in K.carrier,
            SupportFunction.pairing p m
            ∂(volume : Measure (Space n))) := by
          simpa [m] using
            MeasureTheory.integral_sub
              (hdual.add (hv.const_mul t)) hpair
        _ = _ := by
          rw [MeasureTheory.integral_add hdual (hv.const_mul t),
            MeasureTheory.integral_const_mul]
    _ = _ := by
      rw [sourceCenteredBody_setIntegral_pairing_eq_zero,
        MeasureTheory.setIntegral_const]
      simp [normalizedVolume, measureReal_def,
        smul_eq_mul, m]
theorem finiteEnergySourceBodyEnergy_ofTargetGeodesic_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) :
    finiteEnergySourceBodyEnergy
        (finiteEnergySourceOfTargetGeodesic F v t) ≤
      finiteEnergySourceBodyEnergy F +
        t * (∫ p : Space n, v p
          ∂(normalizedTargetBodyMeasure K)) +
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t) := by
  have hdualNormalized :=
    finiteEnergySourceExtendedLegendre_integrableOn
      (finiteEnergySourceOfTargetGeodesic F v t)
  have hmajor :=
    minimumNormalizedTargetGeodesicDualMajorant_integrableOn F v t
  have hmono :
      (∫ p in K.carrier,
        (sourceExtendedBodyLegendre
          (finiteEnergySourceOfTargetGeodesic F v t).potential p).toReal
        ∂(volume : Measure (Space n))) ≤
      ∫ p in K.carrier,
        minimumNormalizedTargetGeodesicDualMajorant F v t p
        ∂(volume : Measure (Space n)) := by
    apply MeasureTheory.integral_mono_ae hdualNormalized hmajor
    filter_upwards [ae_mem_finiteEnergyFiniteTargetSet F]
      with p hp
    exact minimumNormalizedTargetGeodesic_extendedLegendre_toReal_le
      F v t hp
  rw [finiteEnergySourceBodyEnergy_eq_setIntegral
    (finiteEnergySourceOfTargetGeodesic F v t)]
  calc
    (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier,
          (sourceExtendedBodyLegendre
            (finiteEnergySourceOfTargetGeodesic F v t).potential p).toReal
          ∂(volume : Measure (Space n))) ≤
      (normalizedVolume K.carrier)⁻¹ *
        (∫ p in K.carrier,
          minimumNormalizedTargetGeodesicDualMajorant F v t p
          ∂(volume : Measure (Space n))) :=
        mul_le_mul_of_nonneg_left hmono
          (inv_nonneg.mpr K.volume_pos.le)
    _ = finiteEnergySourceBodyEnergy F +
        t * (∫ p : Space n, v p
          ∂(normalizedTargetBodyMeasure K)) +
        finiteEnergyTargetGeodesic F v t
          (finiteEnergyTargetGeodesicMinimumPoint F v t) := by
        rw [setIntegral_minimumNormalizedTargetGeodesicDualMajorant,
          finiteEnergySourceBodyEnergy_eq_setIntegral,
          integral_normalizedTargetBodyMeasure]
        have hvol := K.volume_pos.ne'
        field_simp
theorem exists_exact_optimizer_targetGeodesic_logPartition_le
    {n : ℕ} (K : CenteredBody n) :
    ∃ F : SourceFiniteEnergyPotential K,
      finiteEnergySourceBermanFunctional F =
        sSup
          (Set.range
            (fun D : SourceMomentPotential K =>
              sourceMomentBermanFunctional D)) ∧
      (∀ G : SourceFiniteEnergyPotential K,
        finiteEnergySourceBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F) ∧
      ∀ (v : C(Space n, ℝ)) (t : ℝ),
        Real.log (finiteEnergyTargetGeodesicPartition F v t) ≤
          Real.log (finiteEnergySourcePartition F) +
            t * (∫ p : Space n, v p
              ∂(normalizedTargetBodyMeasure K)) := by
  obtain ⟨F, heq, hmax⟩ :=
    exists_finiteEnergySourceBerman_exact_optimizer K
  refine ⟨F, heq, hmax, ?_⟩
  intro v t
  let G : SourceFiniteEnergyPotential K :=
    finiteEnergySourceOfTargetGeodesic F v t
  let m : Space n :=
    finiteEnergyTargetGeodesicMinimumPoint F v t
  have hG := hmax G
  have henergy := finiteEnergySourceBodyEnergy_ofTargetGeodesic_le
    F v t
  have hpart := finiteEnergySourcePartition_ofTargetGeodesic F v t
  have hpos := finiteEnergyTargetGeodesicPartition_pos F v t
  have hlog :
      Real.log (finiteEnergySourcePartition G) =
        finiteEnergyTargetGeodesic F v t m +
          Real.log (finiteEnergyTargetGeodesicPartition F v t) := by
    change
      Real.log
        (finiteEnergySourcePartition
          (finiteEnergySourceOfTargetGeodesic F v t)) = _
    rw [hpart,
      Real.log_mul
        (Real.exp_pos
          (finiteEnergyTargetGeodesic F v t m)).ne'
        hpos.ne', Real.log_exp]
  unfold finiteEnergySourceBermanFunctional at hG
  change
    finiteEnergySourceBodyEnergy G ≤
      finiteEnergySourceBodyEnergy F +
        t * (∫ p : Space n, v p
          ∂(normalizedTargetBodyMeasure K)) +
        finiteEnergyTargetGeodesic F v t m at henergy
  rw [hlog] at hG
  linarith
end MomentTargetGeodesicVariation
namespace MomentTargetDanskin
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentFunctionalCoercivity
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentTargetGeodesicVariation
open scoped BigOperators ENNReal NNReal Topology
theorem finiteEnergySourceGradient_eq_of_phase_maximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (p x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (hmax : ∀ z : Space n,
      phase p F.potential z ≤ phase p F.potential x) :
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x = p := by
  classical
  ext i
  let w : Space n := Pi.single i (1 : ℝ)
  have hline : HasDerivAt
      (fun t : ℝ => x + t • w) w 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hpair : HasDerivAt
      (fun t : ℝ =>
        SupportFunction.pairing p (x + t • w))
      (SupportFunction.pairing p w) 0 := by
    simpa [MonomialDivergence.pairing_add_right,
      MonomialDivergence.pairing_smul_right] using
      ((hasDerivAt_id (0 : ℝ)).mul_const
        (SupportFunction.pairing p w)).const_add
          (SupportFunction.pairing p x)
  have hpot : HasDerivAt
      (fun t : ℝ => F.potential (x + t • w))
      ((fderiv ℝ F.potential x) w) 0 := by
    have hzero : x = (fun t : ℝ => x + t • w) 0 := by
      simp
    simpa [Function.comp_def] using
      hx.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline hzero
  have hphase : HasDerivAt
      (fun t : ℝ => phase p F.potential (x + t • w))
      (SupportFunction.pairing p w -
        (fderiv ℝ F.potential x) w) 0 := by
    change HasDerivAt
      (fun t : ℝ =>
        SupportFunction.pairing p (x + t • w) -
          F.potential (x + t • w))
      (SupportFunction.pairing p w -
        (fderiv ℝ F.potential x) w) 0
    exact hpair.fun_sub hpot
  have hlocal : IsLocalMax
      (fun t : ℝ => phase p F.potential (x + t • w)) 0 :=
    Filter.Eventually.of_forall
      (fun t => by simpa using hmax (x + t • w))
  have hzero :
      SupportFunction.pairing p w -
        (fderiv ℝ F.potential x) w = 0 := by
    have hd := hphase.deriv
    rw [hlocal.deriv_eq_zero] at hd
    linarith
  have hpairing :
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) w =
        SupportFunction.pairing p w := by
    rw [SpatialBergmanFatouScheffe.pairing_actualGradient_eq_fderiv]
    linarith
  simpa [w, SupportFunction.pairing, Pi.single_apply]
    using hpairing
theorem exists_finiteEnergyTargetGeodesic_approximateMaximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (t ε : ℝ) (hε : 0 < ε) :
    ∃ p ∈ finiteEnergyFiniteTargetSet F,
      finiteEnergyTargetGeodesic F v t x - ε <
        finiteEnergyTargetDualPhase F v t p x := by
  have hlt :
      finiteEnergyTargetGeodesic F v t x - ε <
        finiteEnergyTargetGeodesic F v t x :=
    sub_lt_self _ hε
  change
    finiteEnergyTargetGeodesic F v t x - ε <
      sSup
        ((fun p : Space n =>
          finiteEnergyTargetDualPhase F v t p x) ''
            finiteEnergyFiniteTargetSet F) at hlt
  obtain ⟨_, ⟨p, hp, rfl⟩, happrox⟩ :=
    exists_lt_of_lt_csSup
      ((finiteEnergyFiniteTargetSet_nonempty F).image _) hlt
  exact ⟨p, hp, happrox⟩
def finiteEnergyTargetQuadraticApproximateMaximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (t : ℝ) : Space n :=
  if ht : t = 0 then 0 else
    (exists_finiteEnergyTargetGeodesic_approximateMaximizer
      F v x t (t ^ 2) (sq_pos_of_ne_zero ht)).choose
theorem finiteEnergyTargetQuadraticApproximateMaximizer_mem
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (t : ℝ) :
    finiteEnergyTargetQuadraticApproximateMaximizer F v x t ∈
      finiteEnergyFiniteTargetSet F := by
  classical
  unfold finiteEnergyTargetQuadraticApproximateMaximizer
  split_ifs with ht
  · exact zero_mem_finiteEnergyFiniteTargetSet F
  · exact
      (exists_finiteEnergyTargetGeodesic_approximateMaximizer
        F v x t (t ^ 2) (sq_pos_of_ne_zero ht)).choose_spec.1
theorem finiteEnergyTargetQuadraticApproximateMaximizer_phase
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    {t : ℝ} (ht : t ≠ 0) :
    finiteEnergyTargetGeodesic F v t x - t ^ 2 <
      finiteEnergyTargetDualPhase F v t
        (finiteEnergyTargetQuadraticApproximateMaximizer
          F v x t) x := by
  classical
  unfold finiteEnergyTargetQuadraticApproximateMaximizer
  simp only [dif_neg ht]
  exact
    (exists_finiteEnergyTargetGeodesic_approximateMaximizer
      F v x t (t ^ 2) (sq_pos_of_ne_zero ht)).choose_spec.2
theorem finiteEnergyTargetQuadraticApproximateMaximizer_phase_defect
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x z : Space n)
    {t : ℝ} (ht : t ≠ 0) :
    phase
        (finiteEnergyTargetQuadraticApproximateMaximizer
          F v x t)
        F.potential z -
      phase
        (finiteEnergyTargetQuadraticApproximateMaximizer
          F v x t)
        F.potential x ≤
      2 * |t| * finiteEnergyTargetTestBound K v + t ^ 2 := by
  let p : Space n :=
    finiteEnergyTargetQuadraticApproximateMaximizer F v x t
  have hp := finiteEnergyTargetQuadraticApproximateMaximizer_mem
    F v x t
  have happrox :=
    finiteEnergyTargetQuadraticApproximateMaximizer_phase
      F v x ht
  have hfenchel := finiteEnergyFiniteTarget_fenchel F hp z
  have hclose := (abs_le.mp
    (finiteEnergyTargetGeodesic_uniform_error F v t x)).1
  have htest := abs_targetTest_le_finiteEnergyTargetTestBound
    K v hp.1
  have htbound : -t * v p ≤
      |t| * finiteEnergyTargetTestBound K v := by
    calc
      -t * v p = -(t * v p) := by ring
      _ ≤ |t * v p| := neg_le_abs _
      _ = |t| * |v p| := abs_mul _ _
      _ ≤ |t| * finiteEnergyTargetTestBound K v :=
        mul_le_mul_of_nonneg_left htest (abs_nonneg t)
  unfold finiteEnergyTargetDualPhase at happrox
  unfold phase
  change
    SupportFunction.pairing p z - F.potential z -
      (SupportFunction.pairing p x - F.potential x) ≤ _
  change
    SupportFunction.pairing p z -
      (sourceExtendedBodyLegendre F.potential p).toReal ≤
        F.potential z at hfenchel
  change
    finiteEnergyTargetGeodesic F v t x - t ^ 2 <
      SupportFunction.pairing p x -
        (sourceExtendedBodyLegendre F.potential p).toReal -
          t * v p at happrox
  linarith
theorem tendsto_finiteEnergyTargetQuadraticApproximateMaximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    Tendsto
      (finiteEnergyTargetQuadraticApproximateMaximizer F v x)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (SpatialBergmanFatouScheffe.actualGradient
        F.potential x)) := by
  have herror :
      Tendsto
        (fun t : ℝ =>
          2 * |t| * finiteEnergyTargetTestBound K v + t ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hcont : Continuous
        (fun t : ℝ =>
          2 * |t| * finiteEnergyTargetTestBound K v + t ^ 2) :=
      ((continuous_const.mul continuous_id.abs).mul
        continuous_const).add (continuous_id.pow 2)
    simpa using
      (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)), t ≠ 0 := by
    change ({0}ᶜ : Set ℝ) ∈ 𝓝[({0}ᶜ : Set ℝ)] (0 : ℝ)
    exact self_mem_nhdsWithin
  refine K.compact.tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · exact Filter.Eventually.of_forall fun t =>
      (finiteEnergyTargetQuadraticApproximateMaximizer_mem
        F v x t).1
  · intro q _hq hcluster
    symm
    apply finiteEnergySourceGradient_eq_of_phase_maximizer
      F q x hx
    intro z
    by_contra hnot
    have hgap :
        0 < phase q F.potential z - phase q F.potential x := by
      linarith [lt_of_not_ge hnot]
    have hsmall : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)),
        2 * |t| * finiteEnergyTargetTestBound K v + t ^ 2 <
          (phase q F.potential z -
            phase q F.potential x) / 2 :=
      herror.eventually (gt_mem_nhds (half_pos hgap))
    have hevent : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)),
        phase (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t) F.potential z -
          phase (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t) F.potential x ≤
          (phase q F.potential z -
            phase q F.potential x) / 2 := by
      filter_upwards [hne, hsmall] with t ht hlt
      exact
        (finiteEnergyTargetQuadraticApproximateMaximizer_phase_defect
          F v x z ht).trans hlt.le
    have hmap :
        ∀ᶠ p : Space n in
          Filter.map
            (finiteEnergyTargetQuadraticApproximateMaximizer F v x)
            (𝓝[≠] (0 : ℝ)),
          phase p F.potential z - phase p F.potential x ≤
            (phase q F.potential z -
              phase q F.potential x) / 2 := by
      exact hevent
    let l : Filter (Space n) :=
      𝓝 q ⊓ Filter.map
        (finiteEnergyTargetQuadraticApproximateMaximizer F v x)
        (𝓝[≠] (0 : ℝ))
    have : l.NeBot := hcluster
    have hphasez : Continuous
        (fun p : Space n => phase p F.potential z) := by
      unfold phase
      exact (SupportFunction.continuous_pairing_left z).fun_sub
        continuous_const
    have hphasex : Continuous
        (fun p : Space n => phase p F.potential x) := by
      unfold phase
      exact (SupportFunction.continuous_pairing_left x).fun_sub
        continuous_const
    have hlimit :
        Tendsto
          (fun p : Space n =>
            phase p F.potential z - phase p F.potential x)
          l
          (𝓝 (phase q F.potential z - phase q F.potential x)) :=
      (hphasez.sub hphasex).continuousAt.tendsto.mono_left
        inf_le_left
    have hle := le_of_tendsto hlimit
      (hmap.filter_mono inf_le_right)
    linarith
theorem finiteEnergyTargetGeodesic_gradient_support
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (t : ℝ) :
    F.potential x -
        t * v
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) ≤
      finiteEnergyTargetGeodesic F v t x := by
  let p : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have hp : p ∈ finiteEnergyFiniteTargetSet F := by
    refine ⟨finiteEnergySourceGradient_mem_carrier F x hx, ?_⟩
    rw [finiteEnergySourceExtendedLegendre_actualGradient F x hx]
    exact ENNReal.ofReal_ne_top
  have h := finiteEnergyTargetDualPhase_le_geodesic
    F v t hp x
  have hleg :=
    finiteEnergySourceExtendedLegendre_actualGradient_toReal
      F x hx
  unfold finiteEnergyTargetDualPhase at h
  change
    (sourceExtendedBodyLegendre F.potential p).toReal =
      SupportFunction.pairing p x - F.potential x at hleg
  linarith
theorem finiteEnergyTargetGeodesic_le_quadraticApproximate
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    {t : ℝ} (ht : t ≠ 0) :
    finiteEnergyTargetGeodesic F v t x ≤
      F.potential x -
        t * v
          (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t) + t ^ 2 := by
  let p : Space n :=
    finiteEnergyTargetQuadraticApproximateMaximizer F v x t
  have hp := finiteEnergyTargetQuadraticApproximateMaximizer_mem
    F v x t
  have happrox :=
    finiteEnergyTargetQuadraticApproximateMaximizer_phase
      F v x ht
  have hfenchel := finiteEnergyFiniteTarget_fenchel F hp x
  unfold finiteEnergyTargetDualPhase at happrox
  change
    SupportFunction.pairing p x -
      (sourceExtendedBodyLegendre F.potential p).toReal ≤
        F.potential x at hfenchel
  change
    finiteEnergyTargetGeodesic F v t x - t ^ 2 <
      SupportFunction.pairing p x -
        (sourceExtendedBodyLegendre F.potential p).toReal -
          t * v p at happrox
  linarith
theorem finiteEnergyTargetGeodesic_differenceQuotient_error
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    {t : ℝ} (ht : t ≠ 0) :
    |(finiteEnergyTargetGeodesic F v t x - F.potential x) / t +
        v (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)| ≤
      |v (finiteEnergyTargetQuadraticApproximateMaximizer
        F v x t) -
        v (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)| + |t| := by
  let p : Space n :=
    finiteEnergyTargetQuadraticApproximateMaximizer F v x t
  let q : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have hlower := finiteEnergyTargetGeodesic_gradient_support
    F v x hx t
  have hupper := finiteEnergyTargetGeodesic_le_quadraticApproximate
    F v x ht
  have hnum :
      0 ≤ finiteEnergyTargetGeodesic F v t x - F.potential x +
        t * v q := by
    linarith
  have hterm :
      t * (v q - v p) ≤ |t| * |v p - v q| := by
    calc
      t * (v q - v p) ≤ |t * (v q - v p)| := le_abs_self _
      _ = |t| * |v p - v q| := by
        rw [abs_mul, abs_sub_comm]
  have hnumupper :
      finiteEnergyTargetGeodesic F v t x - F.potential x +
          t * v q ≤
        |t| * (|v p - v q| + |t|) := by
    have habssq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith
  have hfrac :
      (finiteEnergyTargetGeodesic F v t x - F.potential x) / t +
        v q =
      (finiteEnergyTargetGeodesic F v t x - F.potential x +
        t * v q) / t := by
    field_simp
  rw [hfrac, abs_div, abs_of_nonneg hnum]
  exact (div_le_iff₀ (abs_pos.mpr ht)).mpr (by
    simpa [p, q, mul_comm] using hnumupper)
theorem hasDerivAt_finiteEnergyTargetGeodesic
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    HasDerivAt
      (fun t : ℝ => finiteEnergyTargetGeodesic F v t x)
      (-(v (SpatialBergmanFatouScheffe.actualGradient
        F.potential x))) 0 := by
  let q : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have happrox :=
    tendsto_finiteEnergyTargetQuadraticApproximateMaximizer
      F v x hx
  have htarget :
      Tendsto
        (fun t : ℝ =>
          v (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t))
        (𝓝[≠] (0 : ℝ)) (𝓝 (v q)) :=
    v.continuous.continuousAt.tendsto.comp happrox
  have htzero : Tendsto (fun t : ℝ => |t|)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using
      (continuous_id.abs.tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
  have hbound :
      Tendsto
        (fun t : ℝ =>
          |v (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t) - v q| + |t|)
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hconst : Tendsto (fun _ : ℝ => v q)
        (𝓝[≠] (0 : ℝ)) (𝓝 (v q)) :=
      tendsto_const_nhds
    simpa using (htarget.sub hconst).abs.add htzero
  have hne : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)), t ≠ 0 := by
    change ({0}ᶜ : Set ℝ) ∈ 𝓝[({0}ᶜ : Set ℝ)] (0 : ℝ)
    exact self_mem_nhdsWithin
  have herr :
      Tendsto
        (fun t : ℝ =>
          |(finiteEnergyTargetGeodesic F v t x -
              F.potential x) / t + v q|)
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun t => abs_nonneg _)
    · filter_upwards [hne] with t ht
      exact finiteEnergyTargetGeodesic_differenceQuotient_error
        F v x hx ht
    · exact hbound
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  rw [finiteEnergyTargetGeodesic_zero_eq F v x]
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa [Real.dist_eq, smul_eq_mul, inv_mul_eq_div,
    sub_neg_eq_add, q] using herr
theorem abs_exp_sub_one_le_mul_exp_abs (z : ℝ) :
    |Real.exp z - 1| ≤ |z| * Real.exp |z| := by
  by_cases hz : 0 ≤ z
  · have he : 0 < Real.exp z := Real.exp_pos z
    have hfirst : 0 ≤ Real.exp z - 1 :=
      sub_nonneg.mpr (Real.one_le_exp hz)
    have htan := Real.add_one_le_exp (-z)
    have hmul := mul_le_mul_of_nonneg_right htan he.le
    have hinverse : Real.exp (-z) * Real.exp z = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hinverse] at hmul
    rw [abs_of_nonneg hfirst, abs_of_nonneg hz]
    nlinarith
  · have hz' : z ≤ 0 := le_of_not_ge hz
    have he : 0 < Real.exp (-z) := Real.exp_pos (-z)
    have hfirst : Real.exp z - 1 ≤ 0 := by
      have h := Real.exp_le_exp.mpr hz'
      simpa using h
    have htan := Real.add_one_le_exp z
    have hunit : 1 ≤ Real.exp (-z) :=
      Real.one_le_exp (neg_nonneg.mpr hz')
    rw [abs_of_nonpos hfirst, abs_of_nonpos hz']
    have hnonneg : 0 ≤ -z := neg_nonneg.mpr hz'
    have hscaled := mul_le_mul_of_nonneg_left hunit hnonneg
    nlinarith
def finiteEnergyTargetDensityDifferenceQuotient
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) : ℝ :=
  (Real.exp (-finiteEnergyTargetGeodesic F v t x) -
    Real.exp (-F.potential x)) / t
theorem finiteEnergyTargetDensityDifferenceQuotient_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    {t : ℝ} (ht : t ≠ 0) (htsmall : |t| ≤ 1)
    (x : Space n) :
    |finiteEnergyTargetDensityDifferenceQuotient F v t x| ≤
      finiteEnergyTargetTestBound K v *
        (Real.exp (finiteEnergyTargetTestBound K v) *
          Real.exp (-F.potential x)) := by
  let M : ℝ := finiteEnergyTargetTestBound K v
  let d : ℝ :=
    -(finiteEnergyTargetGeodesic F v t x - F.potential x)
  have hM : 0 ≤ M := finiteEnergyTargetTestBound_nonneg K v
  have hd : |d| ≤ |t| * M := by
    simpa [d, M, abs_sub_comm] using
      finiteEnergyTargetGeodesic_uniform_error F v t x
  have hdM : |d| ≤ M := by
    calc
      |d| ≤ |t| * M := hd
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right htsmall hM
      _ = M := one_mul M
  have he : Real.exp |d| ≤ Real.exp M :=
    Real.exp_le_exp.mpr hdM
  have hfactor :
      Real.exp (-finiteEnergyTargetGeodesic F v t x) -
          Real.exp (-F.potential x) =
        Real.exp (-F.potential x) * (Real.exp d - 1) := by
    have harg :
        -finiteEnergyTargetGeodesic F v t x =
          -F.potential x + d := by
      dsimp [d]
      ring
    rw [harg, Real.exp_add, mul_sub, mul_one]
  unfold finiteEnergyTargetDensityDifferenceQuotient
  rw [hfactor, abs_div, abs_mul,
    abs_of_pos (Real.exp_pos (-F.potential x))]
  calc
    Real.exp (-F.potential x) * |Real.exp d - 1| / |t| ≤
        Real.exp (-F.potential x) *
          (|d| * Real.exp |d|) / |t| := by
      apply (div_le_div_iff_of_pos_right (abs_pos.mpr ht)).mpr
      exact mul_le_mul_of_nonneg_left
        (abs_exp_sub_one_le_mul_exp_abs d)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-F.potential x) *
          ((|t| * M) * Real.exp M) / |t| := by
      apply (div_le_div_iff_of_pos_right (abs_pos.mpr ht)).mpr
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul hd he (Real.exp_pos _).le
        (mul_nonneg (abs_nonneg _) hM)
    _ = finiteEnergyTargetTestBound K v *
        (Real.exp (finiteEnergyTargetTestBound K v) *
          Real.exp (-F.potential x)) := by
      dsimp [M]
      field_simp [abs_ne_zero.mpr ht]
theorem finiteEnergyTargetGeodesicPartition_zero
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ)) :
    finiteEnergyTargetGeodesicPartition F v 0 =
      finiteEnergySourcePartition F := by
  unfold finiteEnergyTargetGeodesicPartition
    finiteEnergySourcePartition
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [finiteEnergyTargetGeodesic_zero_eq F v x]
theorem tendsto_finiteEnergyTargetDensityDifferenceQuotient
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    Tendsto
      (fun t : ℝ =>
        finiteEnergyTargetDensityDifferenceQuotient F v t x)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Real.exp (-F.potential x) *
        v (SpatialBergmanFatouScheffe.actualGradient
          F.potential x))) := by
  have hd :
      HasDerivAt
        (fun t : ℝ =>
          Real.exp (-finiteEnergyTargetGeodesic F v t x))
        (Real.exp (-F.potential x) *
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x)) 0 := by
    simpa [finiteEnergyTargetGeodesic_zero_eq F v x] using
      (hasDerivAt_finiteEnergyTargetGeodesic F v x hx).neg.exp
  simpa [finiteEnergyTargetDensityDifferenceQuotient,
    finiteEnergyTargetGeodesic_zero_eq F v x,
    smul_eq_mul, inv_mul_eq_div] using hd.tendsto_slope_zero
theorem hasDerivAt_finiteEnergyTargetGeodesicPartition
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ)) :
    HasDerivAt
      (finiteEnergyTargetGeodesicPartition F v)
      (∫ x : Space n,
        Real.exp (-F.potential x) *
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x)
        ∂(volume : Measure (Space n))) 0 := by
  let M : ℝ := finiteEnergyTargetTestBound K v
  have hmajor : Integrable
      (fun x : Space n =>
        M * (Real.exp M * Real.exp (-F.potential x)))
      (volume : Measure (Space n)) :=
    (F.densityIntegrable.const_mul (Real.exp M)).const_mul M
  have hne : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)), t ≠ 0 := by
    change ({0}ᶜ : Set ℝ) ∈ 𝓝[({0}ᶜ : Set ℝ)] (0 : ℝ)
    exact self_mem_nhdsWithin
  have htlim : Tendsto (fun t : ℝ => |t|)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using
      (continuous_id.abs.tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)), |t| ≤ 1 := by
    exact
      (htlim.eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
        (fun _ ht => le_of_lt ht)
  have hmeas :
      ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)),
        AEStronglyMeasurable
          (finiteEnergyTargetDensityDifferenceQuotient F v t)
          (volume : Measure (Space n)) := by
    filter_upwards with t
    unfold finiteEnergyTargetDensityDifferenceQuotient
    exact
      ((Real.continuous_exp.comp
        (continuous_finiteEnergyTargetGeodesic F v t).neg).sub
        (Real.continuous_exp.comp
          F.potential.continuous.neg)).div_const t
        |>.aestronglyMeasurable
  have hbound :
      ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)),
        ∀ᵐ x : Space n
          ∂(volume : Measure (Space n)),
          ‖finiteEnergyTargetDensityDifferenceQuotient F v t x‖ ≤
            M * (Real.exp M * Real.exp (-F.potential x)) := by
    filter_upwards [hne, hsmall] with t ht htsmall
    filter_upwards with x
    simpa [Real.norm_eq_abs, M] using
      finiteEnergyTargetDensityDifferenceQuotient_le
        F v ht htsmall x
  have hlim :
      ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
        Tendsto
          (fun t : ℝ =>
            finiteEnergyTargetDensityDifferenceQuotient F v t x)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (Real.exp (-F.potential x) *
            v (SpatialBergmanFatouScheffe.actualGradient
              F.potential x))) := by
    filter_upwards [ae_differentiableAt_finiteEnergySource F]
      with x hx
    exact tendsto_finiteEnergyTargetDensityDifferenceQuotient
      F v x hx
  have hdct :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (Space n)))
      (F := fun t x =>
        finiteEnergyTargetDensityDifferenceQuotient F v t x)
      (f := fun x : Space n =>
        Real.exp (-F.potential x) *
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x))
      (fun x : Space n =>
        M * (Real.exp M * Real.exp (-F.potential x)))
      hmeas hbound hmajor hlim
  have hquot (t : ℝ) :
      (∫ x : Space n,
        finiteEnergyTargetDensityDifferenceQuotient F v t x
        ∂(volume : Measure (Space n))) =
        (finiteEnergyTargetGeodesicPartition F v t -
          finiteEnergySourcePartition F) / t := by
    unfold finiteEnergyTargetDensityDifferenceQuotient
    rw [MeasureTheory.integral_div,
      MeasureTheory.integral_sub
        (finiteEnergyTargetGeodesic_densityIntegrable F v t)
        F.densityIntegrable]
    rfl
  have hslope :
      Tendsto
        (fun t : ℝ =>
          (finiteEnergyTargetGeodesicPartition F v t -
            finiteEnergySourcePartition F) / t)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (∫ x : Space n,
          Real.exp (-F.potential x) *
            v (SpatialBergmanFatouScheffe.actualGradient
              F.potential x)
          ∂(volume : Measure (Space n)))) := by
    convert hdct using 1
    funext t
    exact (hquot t).symm
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa [finiteEnergyTargetGeodesicPartition_zero F v,
    smul_eq_mul, inv_mul_eq_div] using hslope
theorem hasDerivAt_finiteEnergyTargetGeodesicLogPartition
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ)) :
    HasDerivAt
      (fun t : ℝ =>
        Real.log (finiteEnergyTargetGeodesicPartition F v t))
      (∫ p : Space n, v p
        ∂(finiteEnergySourceGradientPushforward F)) 0 := by
  have hpart := hasDerivAt_finiteEnergyTargetGeodesicPartition F v
  have hzero := finiteEnergyTargetGeodesicPartition_zero F v
  have hpos := finiteEnergySourcePartition_pos F
  have hlog := hpart.log (hzero.trans_ne hpos.ne')
  have hmoment :
      (∫ x : Space n,
        Real.exp (-F.potential x) *
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x)
        ∂(volume : Measure (Space n))) /
          finiteEnergySourcePartition F =
        ∫ p : Space n, v p
          ∂(finiteEnergySourceGradientPushforward F) := by
    rw [integral_finiteEnergySourceGradientPushforward F v,
      integral_finiteEnergySourceGibbsProbability F
        (fun x : Space n =>
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x))]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  rw [← hmoment]
  simpa [finiteEnergyTargetGeodesicPartition_zero F v] using hlog
theorem exists_exact_optimizer_gradientPushforward_integral_eq
    {n : ℕ} (K : CenteredBody n) :
    ∃ F : SourceFiniteEnergyPotential K,
      finiteEnergySourceBermanFunctional F =
        sSup
          (Set.range
            (fun D : SourceMomentPotential K =>
              sourceMomentBermanFunctional D)) ∧
      (∀ G : SourceFiniteEnergyPotential K,
        finiteEnergySourceBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F) ∧
      ∀ v : C(Space n, ℝ),
        (∫ p : Space n, v p
          ∂(finiteEnergySourceGradientPushforward F)) =
        ∫ p : Space n, v p
          ∂(normalizedTargetBodyMeasure K) := by
  obtain ⟨F, hsup, hmax, hineq⟩ :=
    exists_exact_optimizer_targetGeodesic_logPartition_le K
  refine ⟨F, hsup, hmax, ?_⟩
  intro v
  let A : ℝ :=
    ∫ p : Space n, v p
      ∂(normalizedTargetBodyMeasure K)
  let H : ℝ → ℝ := fun t =>
    Real.log (finiteEnergyTargetGeodesicPartition F v t) -
      t * A
  have hlocal : IsLocalMax H 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    dsimp [H, A]
    simp only [zero_mul, sub_zero,
      finiteEnergyTargetGeodesicPartition_zero F v]
    linarith [hineq v t]
  have hd :=
    (hasDerivAt_finiteEnergyTargetGeodesicLogPartition F v).fun_sub
      ((hasDerivAt_id (0 : ℝ)).mul_const A)
  have hderiv :
      deriv
        (fun t : ℝ =>
          Real.log (finiteEnergyTargetGeodesicPartition F v t) -
            t * A) 0 =
        (∫ p : Space n, v p
          ∂(finiteEnergySourceGradientPushforward F)) - A := by
    simpa only [id, one_mul] using hd.deriv
  have hzero :
      deriv
        (fun t : ℝ =>
          Real.log (finiteEnergyTargetGeodesicPartition F v t) -
            t * A) 0 = 0 := by
    simpa [H] using hlocal.deriv_eq_zero
  change
    (∫ p : Space n, v p
      ∂(finiteEnergySourceGradientPushforward F)) = A
  linarith
theorem exists_exact_optimizer_gradientPushforward_eq
    {n : ℕ} (K : CenteredBody n) :
    ∃ F : SourceFiniteEnergyPotential K,
      finiteEnergySourceBermanFunctional F =
        sSup
          (Set.range
            (fun D : SourceMomentPotential K =>
              sourceMomentBermanFunctional D)) ∧
      (∀ G : SourceFiniteEnergyPotential K,
        finiteEnergySourceBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F) ∧
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K := by
  obtain ⟨F, hsup, hmax, htest⟩ :=
    exists_exact_optimizer_gradientPushforward_integral_eq K
  refine ⟨F, hsup, hmax, ?_⟩
  let : IsProbabilityMeasure
      (finiteEnergySourceGradientPushforward F) :=
    finiteEnergySourceGradientPushforward_isProbability F
  let : IsProbabilityMeasure (normalizedTargetBodyMeasure K) :=
    normalizedTargetBodyMeasure_isProbability K
  let μ : MeasureTheory.FiniteMeasure (Space n) :=
    ⟨finiteEnergySourceGradientPushforward F, inferInstance⟩
  let ν : MeasureTheory.FiniteMeasure (Space n) :=
    ⟨normalizedTargetBodyMeasure K, inferInstance⟩
  have heq : μ = ν := by
    apply MeasureTheory.FiniteMeasure.ext_of_forall_integral_eq
    intro v
    exact htest v.toContinuousMap
  exact congrArg (fun q : MeasureTheory.FiniteMeasure
    (Space n) => (q : Measure (Space n))) heq
end MomentTargetDanskin
namespace MomentRegularity
open Set Function Filter MeasureTheory
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open scoped ENNReal Topology
theorem finiteEnergySourceGradient_mem_carrier_everywhere
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) :
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x ∈ K.carrier := by
  by_cases hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x
  · exact finiteEnergySourceGradient_mem_carrier F x hx
  · have hzero :
        SpatialBergmanFatouScheffe.actualGradient
          F.potential x = 0 := by
      ext i
      change
        (fderiv ℝ (F.potential : Space n → ℝ) x)
          (Pi.single i (1 : ℝ)) = 0
      rw [fderiv_zero_of_not_differentiableAt hx]
      simp
    rw [hzero]
    exact interior_subset (LatticeAsymptotics.zero_mem_interior K)
theorem normalizedTargetBodyMeasure_open_pos_of_inter_interior
    {n : ℕ} (K : CenteredBody n)
    {U : Set (Space n)} (hU : IsOpen U)
    (hinter : (U ∩ interior K.carrier).Nonempty) :
    0 < normalizedTargetBodyMeasure K U := by
  have hinner :
      0 < (volume : Measure (Space n))
        (U ∩ interior K.carrier) :=
    (hU.inter isOpen_interior).measure_pos
      (volume : Measure (Space n)) hinter
  have hbody :
      0 < (volume : Measure (Space n))
        (U ∩ K.carrier) :=
    lt_of_lt_of_le hinner
      (measure_mono (inter_subset_inter_right U interior_subset))
  have hscale :
      0 < ((volume : Measure (Space n))
        K.carrier)⁻¹ :=
    ENNReal.inv_pos.mpr K.compact.measure_ne_top
  unfold normalizedTargetBodyMeasure
  rw [Measure.smul_apply,
    Measure.restrict_apply hU.measurableSet]
  exact ENNReal.mul_pos hscale.ne' hbody.ne'
def momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) : ℝ :=
  F.potential x +
    Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier)
theorem exp_neg_momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) :
    Real.exp (-momentNormalizedPotential F x) =
      (normalizedVolume K.carrier /
        finiteEnergySourcePartition F) *
          Real.exp (-F.potential x) := by
  have hratio :
      0 < finiteEnergySourcePartition F /
        normalizedVolume K.carrier :=
    div_pos (finiteEnergySourcePartition_pos F) K.volume_pos
  unfold momentNormalizedPotential
  calc
    Real.exp
        (-(F.potential x +
          Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier))) =
        Real.exp
          (-Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) *
          Real.exp (-F.potential x) := by
            rw [← Real.exp_add]
            congr 1
            ring
    _ =
        (normalizedVolume K.carrier /
          finiteEnergySourcePartition F) *
            Real.exp (-F.potential x) := by
          rw [Real.exp_neg, Real.exp_log hratio, inv_div]
theorem integral_exp_neg_momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    (∫ x : Space n,
      Real.exp (-momentNormalizedPotential F x)
      ∂(volume : Measure (Space n))) =
        normalizedVolume K.carrier := by
  calc
    (∫ x : Space n,
      Real.exp (-momentNormalizedPotential F x)
      ∂(volume : Measure (Space n))) =
        ∫ x : Space n,
          (normalizedVolume K.carrier /
            finiteEnergySourcePartition F) *
              Real.exp (-F.potential x)
          ∂(volume : Measure (Space n)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact exp_neg_momentNormalizedPotential F x
    _ = (normalizedVolume K.carrier /
          finiteEnergySourcePartition F) *
        finiteEnergySourcePartition F := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = normalizedVolume K.carrier := by
      field_simp [(finiteEnergySourcePartition_pos F).ne']
end MomentRegularity
namespace MomentMonotoneTransport
open Set Function Filter MeasureTheory
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentRegularity
open scoped BigOperators ENNReal Topology
def finiteEnergyDifferentiableGradientImage
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : Set (Space n) :=
  SpatialBergmanFatouScheffe.actualGradient F.potential ''
    {x : Space n |
      DifferentiableAt ℝ
        (F.potential : Space n → ℝ) x}
theorem interior_subset_closure_finiteEnergyDifferentiableGradientImage
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    interior K.carrier ⊆
      closure (finiteEnergyDifferentiableGradientImage F) := by
  intro p hp
  apply mem_closure_iff.mpr
  intro U hU hpU
  by_contra hnonempty
  have hno :
      ∀ x : Space n,
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) x →
        SpatialBergmanFatouScheffe.actualGradient
          F.potential x ∉ U := by
    intro x hx hgrad
    apply hnonempty
    exact ⟨SpatialBergmanFatouScheffe.actualGradient
      F.potential x, hgrad, ⟨x, hx, rfl⟩⟩
  have hae_diff :
      ∀ᵐ x : Space n
        ∂(finiteEnergySourceGibbsProbability F),
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) x :=
    finiteEnergySourceGibbs_ae_of_volume F _
      (ae_differentiableAt_finiteEnergySource F)
  have hae_not :
      ∀ᵐ x : Space n
        ∂(finiteEnergySourceGibbsProbability F),
        x ∉
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential) ⁻¹' U := by
    filter_upwards [hae_diff] with x hx
    exact hno x hx
  have hzero :
      finiteEnergySourceGibbsProbability F
        ((SpatialBergmanFatouScheffe.actualGradient
          F.potential) ⁻¹' U) = 0 := by
    exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr hae_not
  have htarget : normalizedTargetBodyMeasure K U = 0 := by
    rw [← htransport]
    unfold finiteEnergySourceGradientPushforward
    rw [Measure.map_apply
      (measurable_finiteEnergySourceGradient F)
      hU.measurableSet]
    exact hzero
  exact
    (ne_of_gt
      (normalizedTargetBodyMeasure_open_pos_of_inter_interior
        K hU ⟨p, hpU, hp⟩)) htarget
theorem closure_finiteEnergyDifferentiableGradientImage_eq_carrier
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    closure (finiteEnergyDifferentiableGradientImage F) =
      K.carrier := by
  apply le_antisymm
  · apply closure_minimal _ K.compact.isClosed
    rintro p ⟨x, _hx, rfl⟩
    exact finiteEnergySourceGradient_mem_carrier_everywhere F x
  · have hsubset :=
      closure_mono
        (interior_subset_closure_finiteEnergyDifferentiableGradientImage
          F htransport)
    have hbody : closure (interior K.carrier) = K.carrier := by
      simpa [K.compact.isClosed.closure_eq] using
        K.convex.closure_interior_eq_closure_of_nonempty_interior
          K.fullDimensional
    rw [hbody, closure_closure] at hsubset
    exact hsubset
end MomentMonotoneTransport
namespace MomentInteriorLegendre
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentFunctionalCoercivity MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentMonotoneTransport
open scoped BigOperators ENNReal Topology
theorem finiteEnergySourcePhase_affine_target
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (p q x : Space n) (a b : ℝ)
    (hab : a + b = 1) :
    phase (a • p + b • q) F.potential x =
      a * phase p F.potential x +
        b * phase q F.potential x := by
  simp only [phase, SupportFunction.pairing_add_left,
    SupportFunction.pairing_smul_left]
  linear_combination F.potential x * hab
theorem convex_finiteEnergyFiniteTargetSet
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Convex ℝ (finiteEnergyFiniteTargetSet F) := by
  intro p hp q hq a b ha hb hab
  refine ⟨K.convex hp.1 hq.1 ha hb hab, ?_⟩
  have hbdd :
      BddAbove
        (Set.range
          (phase (a • p + b • q) F.potential)) := by
    refine ⟨a * (sourceExtendedBodyLegendre F.potential p).toReal +
      b * (sourceExtendedBodyLegendre F.potential q).toReal, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [finiteEnergySourcePhase_affine_target F p q x a b hab]
    have hpfen := finiteEnergyFiniteTarget_fenchel F hp x
    have hqfen := finiteEnergyFiniteTarget_fenchel F hq x
    have hpbound :
        phase p F.potential x ≤
          (sourceExtendedBodyLegendre F.potential p).toReal := by
      unfold phase
      linarith
    have hqbound :
        phase q F.potential x ≤
          (sourceExtendedBodyLegendre F.potential q).toReal := by
      unfold phase
      linarith
    exact add_le_add
      (mul_le_mul_of_nonneg_left hpbound ha)
      (mul_le_mul_of_nonneg_left hqbound hb)
  rw [sourceExtendedBodyLegendre_eq_of_bddAbove
    F.potential (a • p + b • q) hbdd]
  exact ENNReal.ofReal_ne_top
theorem finiteEnergyDifferentiableGradientImage_subset_finiteTarget
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    finiteEnergyDifferentiableGradientImage F ⊆
      finiteEnergyFiniteTargetSet F := by
  rintro p ⟨x, hx, rfl⟩
  refine ⟨finiteEnergySourceGradient_mem_carrier F x hx, ?_⟩
  rw [finiteEnergySourceExtendedLegendre_actualGradient F x hx]
  exact ENNReal.ofReal_ne_top
theorem closure_finiteEnergyFiniteTargetSet_eq_carrier
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    closure (finiteEnergyFiniteTargetSet F) = K.carrier := by
  apply le_antisymm
  · apply closure_minimal _ K.compact.isClosed
    intro p hp
    exact hp.1
  · have hsubset :=
      closure_mono
        (finiteEnergyDifferentiableGradientImage_subset_finiteTarget F)
    rw [closure_finiteEnergyDifferentiableGradientImage_eq_carrier
      F htransport] at hsubset
    exact hsubset
theorem affineSpan_finiteEnergyFiniteTargetSet_eq_top
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    affineSpan ℝ (finiteEnergyFiniteTargetSet F) = ⊤ := by
  have hbody :
      K.carrier ⊆
        (affineSpan ℝ
          (finiteEnergyFiniteTargetSet F) :
            Set (Space n)) := by
    rw [← closure_finiteEnergyFiniteTargetSet_eq_carrier
      F htransport]
    exact closure_minimal
      (subset_affineSpan ℝ (finiteEnergyFiniteTargetSet F))
      (affineSpan ℝ (finiteEnergyFiniteTargetSet F)).closed_of_finiteDimensional
  apply top_unique
  rw [← isOpen_interior.affineSpan_eq_top K.fullDimensional]
  exact affineSpan_le.mpr (interior_subset.trans hbody)
theorem interior_finiteEnergyFiniteTargetSet_eq
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    interior (finiteEnergyFiniteTargetSet F) =
      interior K.carrier := by
  have hconv := convex_finiteEnergyFiniteTargetSet F
  have hnonempty :
      (interior (finiteEnergyFiniteTargetSet F)).Nonempty :=
    hconv.interior_nonempty_iff_affineSpan_eq_top.mpr
      (affineSpan_finiteEnergyFiniteTargetSet_eq_top
        F htransport)
  have hinter :=
    hconv.interior_closure_eq_interior_of_nonempty_interior
      hnonempty
  rw [closure_finiteEnergyFiniteTargetSet_eq_carrier
    F htransport] at hinter
  exact hinter.symm
theorem finiteEnergySourceExtendedLegendre_ne_top_of_mem_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K)
    {p : Space n} (hp : p ∈ interior K.carrier) :
    sourceExtendedBodyLegendre F.potential p ≠ ⊤ := by
  have hinter :
      p ∈ interior (finiteEnergyFiniteTargetSet F) := by
    rw [interior_finiteEnergyFiniteTargetSet_eq F htransport]
    exact hp
  exact (interior_subset hinter).2
theorem finiteEnergySourcePhase_bddAbove_of_mem_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K)
    {p : Space n} (hp : p ∈ interior K.carrier) :
    BddAbove (Set.range (phase p F.potential)) := by
  have hfinite : p ∈ finiteEnergyFiniteTargetSet F := by
    refine ⟨interior_subset hp, ?_⟩
    exact finiteEnergySourceExtendedLegendre_ne_top_of_mem_interior
      F htransport hp
  refine ⟨(sourceExtendedBodyLegendre F.potential p).toReal, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hfen := finiteEnergyFiniteTarget_fenchel F hfinite x
  unfold phase
  linarith
theorem convexOn_finiteEnergySourceLegendre_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    ConvexOn ℝ (interior K.carrier)
      (legendreTransform F.potential) := by
  refine ⟨K.convex.interior, ?_⟩
  intro p hp q hq a b ha hb hab
  unfold legendreTransform
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  have hpmax :
      phase p F.potential x ≤
        sSup (Set.range (phase p F.potential)) :=
    le_csSup
      (finiteEnergySourcePhase_bddAbove_of_mem_interior
        F htransport hp)
      ⟨x, rfl⟩
  have hqmax :
      phase q F.potential x ≤
        sSup (Set.range (phase q F.potential)) :=
    le_csSup
      (finiteEnergySourcePhase_bddAbove_of_mem_interior
        F htransport hq)
      ⟨x, rfl⟩
  rw [finiteEnergySourcePhase_affine_target F p q x a b hab]
  simpa [smul_eq_mul] using
    add_le_add
      (mul_le_mul_of_nonneg_left hpmax ha)
      (mul_le_mul_of_nonneg_left hqmax hb)
theorem continuousOn_finiteEnergySourceLegendre_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    ContinuousOn (legendreTransform F.potential)
      (interior K.carrier) :=
  (convexOn_finiteEnergySourceLegendre_interior F htransport)
    |>.continuousOn isOpen_interior
end MomentInteriorLegendre
namespace MomentWeakBergman
open Set Function Filter MeasureTheory
open SupportFunction LaplaceAsymptotics MonomialIntegrability WeightedTorusHilbert MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentInteriorLegendre
open MomentMoserTrudinger
open scoped BigOperators ENNReal InnerProductSpace Topology
theorem continuous_momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentNormalizedPotential F) := by
  exact F.potential.continuous.add continuous_const
theorem exists_finiteEnergySource_interior_phase_linear_coercivity
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∃ δ C : ℝ, 0 < δ ∧
      ∀ x : Space n,
        δ * ‖x‖ ≤
          F.potential x - pairing u x + C := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) u hu
  let δ : ℝ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hclosed : Metric.closedBall u δ ⊆ interior K.carrier := by
    intro p hp
    apply hball
    apply Metric.mem_ball.mpr
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hp)
      (half_lt_self hr)
  have hdual : ContinuousOn
      (legendreTransform F.potential)
      (Metric.closedBall u δ) :=
    (continuousOn_finiteEnergySourceLegendre_interior
      F htransport).mono hclosed
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall u δ).bddAbove_image hdual
  refine ⟨δ, C, hδ, ?_⟩
  intro x
  let p : Space n := u + δ • signVector x
  have hp : p ∈ Metric.closedBall u δ := by
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    have hscaled : ‖δ • signVector x‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      exact mul_le_of_le_one_right hδ.le
        (norm_signVector_le_one x)
    simpa [p] using hscaled
  have hpi : p ∈ interior K.carrier := hclosed hp
  have hphase :
      pairing p x - F.potential x ≤
        legendreTransform F.potential p := by
    exact le_csSup
      (finiteEnergySourcePhase_bddAbove_of_mem_interior
        F htransport hpi)
      ⟨x, rfl⟩
  have hbound : legendreTransform F.potential p ≤ C :=
    hC ⟨p, hp, rfl⟩
  change
    pairing (u + δ • signVector x) x -
        F.potential x ≤
      legendreTransform F.potential p at hphase
  rw [pairing_add_left, pairing_smul_left,
    pairing_signVector] at hphase
  have hnorm := SupportFunction.norm_le_sum_abs x
  have hscaled := mul_le_mul_of_nonneg_left hnorm hδ.le
  linarith
theorem integrable_monomialWeight_finiteEnergySource_of_mem_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {k : ℝ} (hk : 0 < k) :
    Integrable
      (monomialWeight k u F.potential)
      (volume : Measure (Space n)) := by
  obtain ⟨δ, C, hδ, hcoerc⟩ :=
    exists_finiteEnergySource_interior_phase_linear_coercivity
      F htransport hu
  have hdecay :=
    integrable_exp_neg_mul_norm_all (n := n) (mul_pos hk hδ)
  have hmajor := hdecay.const_mul (Real.exp (k * C))
  have hmeas :
      AEStronglyMeasurable (monomialWeight k u F.potential)
        (volume : Measure (Space n)) :=
    (continuous_monomialWeight k u F.potential.continuous).aestronglyMeasurable
  refine hmajor.mono' hmeas ?_
  filter_upwards [] with x
  unfold monomialWeight
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := hcoerc x
  nlinarith
theorem monomialWeight_momentNormalizedPotential_eq
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (k : ℝ) (u x : Space n) :
    monomialWeight k u (momentNormalizedPotential F) x =
      Real.exp
        (-k * Real.log
          (finiteEnergySourcePartition F /
            normalizedVolume K.carrier)) *
        monomialWeight k u F.potential x := by
  unfold monomialWeight momentNormalizedPotential
  rw [← Real.exp_add]
  congr 1
  ring
theorem integrable_monomialWeight_momentNormalized_of_mem_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {k : ℝ} (hk : 0 < k) :
    Integrable
      (monomialWeight k u (momentNormalizedPotential F))
      (volume : Measure (Space n)) := by
  refine
    ((integrable_monomialWeight_finiteEnergySource_of_mem_interior
      F htransport hu hk).const_mul
        (Real.exp
          (-k * Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)))).congr ?_
  filter_upwards [] with x
  exact (monomialWeight_momentNormalizedPotential_eq
    F k u x).symm
theorem monomialIntegral_momentNormalized_pos
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {k : ℝ} (hk : 0 < k) :
    0 < monomialIntegral k u (momentNormalizedPotential F) := by
  unfold monomialIntegral monomialWeight
  exact MeasureTheory.integral_exp_pos
    (integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu hk)
theorem radial_exp_integrable_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable
      (fun x : Space n =>
        Real.exp (pairing (integerPoint n m) x))
      (radialMeasure k (momentNormalizedPotential F)) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hφ := continuous_momentNormalizedPotential F
  have hfinite : ∀ᵐ x ∂(volume : Measure (Space n)),
      radialWeight k (momentNormalizedPotential F) x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold radialMeasure
  apply (MeasureTheory.integrable_withDensity_iff_integrable_smul'
    (radialWeight_measurable k hφ) hfinite).2
  have hmono :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu hkreal
  refine hmono.congr (Filter.Eventually.of_forall fun x => ?_)
  simpa only [smul_eq_mul] using
    (radialWeight_mul_exp_pairing k
      (momentNormalizedPotential F) m u hm x).symm
theorem torusMonomial_sq_integrable_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable
      (fun z : LogTorus n => ‖torusMonomial m z‖ ^ 2)
      (weightedTorusMeasure k (momentNormalizedPotential F)) := by
  have hradial := radial_exp_integrable_momentNormalized
    K hk F htransport m u hu hm
  have hangular : Integrable
      (fun _ : TorusCharacters.AngularTorus n => (1 : ℝ))
      (angularMeasure n) := integrable_const _
  have hproduct := hradial.mul_prod hangular
  unfold weightedTorusMeasure
  convert hproduct using 1
  funext z
  simp [torusMonomial_norm_sq]
theorem torusMonomial_memLp_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    MemLp (torusMonomial m) 2
      (weightedTorusMeasure k (momentNormalizedPotential F)) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (continuous_torusMonomial m).aestronglyMeasurable).2
  exact torusMonomial_sq_integrable_momentNormalized
    K hk F htransport m u hu hm
end MomentWeakBergman
namespace BergmanJetBasis
open Set Function Filter MeasureTheory Module
open BergmanMonomials LatticeAsymptotics WeightedTorusHilbert AdaptedBergmanBasis MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology
def momentIndexedMonomialLp
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    weightedHilbert k (momentNormalizedPotential F) :=
  (torusMonomial_memLp_momentNormalized K hk F htransport
    (integerExponent K hk u) (u : Space n)
    u.property.1 (integerPoint_integerExponent K hk u)).toLp
      (torusMonomial (integerExponent K hk u))
theorem momentIndexedMonomialLp_ae
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    (momentIndexedMonomialLp K hk F htransport u :
      LogTorus n → ℂ) =ᵐ[
        weightedTorusMeasure k (momentNormalizedPotential F)]
      torusMonomial (integerExponent K hk u) := by
  unfold momentIndexedMonomialLp
  exact MeasureTheory.MemLp.coeFn_toLp _
theorem momentMonomialNormSquared_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    0 < monomialNormSquared k (u : Space n)
      (momentNormalizedPotential F) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  exact monomialIntegral_momentNormalized_pos
    F htransport u.property.1 hkreal
theorem inner_momentIndexedMonomialLp
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u v : monomialIndex K k) :
    @inner ℂ
      (weightedHilbert k (momentNormalizedPotential F)) _
      (momentIndexedMonomialLp K hk F htransport u)
      (momentIndexedMonomialLp K hk F htransport v) =
      if u = v then
        (monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) : ℂ)
      else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hu := momentIndexedMonomialLp_ae K hk F htransport u
  have hv := momentIndexedMonomialLp_ae K hk F htransport v
  calc
    (∫ z : LogTorus n,
      @inner ℂ ℂ _
        (momentIndexedMonomialLp K hk F htransport u z)
        (momentIndexedMonomialLp K hk F htransport v z)
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
        ∫ z : LogTorus n,
          conj (torusMonomial (integerExponent K hk u) z) *
            torusMonomial (integerExponent K hk v) z
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hu, hv] with z huz hvz
            rw [huz, hvz, RCLike.inner_apply, mul_comm]
    _ = _ := by
      by_cases huv : u = v
      · subst v
        simp only [ite_true]
        calc
          (∫ z : LogTorus n,
            conj (torusMonomial (integerExponent K hk u) z) *
              torusMonomial (integerExponent K hk u) z
            ∂(weightedTorusMeasure k
              (momentNormalizedPotential F))) =
              ∫ z : LogTorus n,
                ((‖torusMonomial (integerExponent K hk u) z‖ ^ 2 : ℝ) : ℂ)
                ∂(weightedTorusMeasure k
                  (momentNormalizedPotential F)) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards [] with z
                  rw [← Complex.normSq_eq_conj_mul_self,
                    Complex.normSq_eq_norm_sq]
          _ = ((∫ z : LogTorus n,
                ‖torusMonomial (integerExponent K hk u) z‖ ^ 2
                ∂(weightedTorusMeasure k
                  (momentNormalizedPotential F)) : ℝ) : ℂ) :=
                integral_ofReal
          _ = (monomialNormSquared k (u : Space n)
                (momentNormalizedPotential F) : ℂ) := by
                rw [integral_torusMonomial_norm_sq_eq_monomialIntegral
                  k (continuous_momentNormalizedPotential F)
                  (integerExponent K hk u) (u : Space n)
                  (integerPoint_integerExponent K hk u)]
                rfl
      · have hmne : integerExponent K hk u ≠
            integerExponent K hk v := by
          intro heq
          exact huv ((integerExponent_injective K hk) heq)
        rw [torusMonomial_inner_eq_zero_of_ne
          k (momentNormalizedPotential F)
          (integerExponent K hk u)
          (integerExponent K hk v) hmne]
        simp [huv]
def momentNormalizedMonomialLp
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    weightedHilbert k (momentNormalizedPotential F) :=
  ((Real.sqrt
    (monomialNormSquared k (u : Space n)
      (momentNormalizedPotential F)) : ℂ)⁻¹) •
    momentIndexedMonomialLp K hk F htransport u
theorem momentNormalizedMonomialLp_orthonormal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Orthonormal ℂ
      (momentNormalizedMonomialLp K hk F htransport) := by
  classical
  rw [orthonormal_iff_ite]
  intro u v
  unfold momentNormalizedMonomialLp
  rw [inner_smul_left, inner_smul_right,
    inner_momentIndexedMonomialLp K hk F htransport]
  by_cases huv : u = v
  · subst v
    simp only [ite_true]
    have hI := momentMonomialNormSquared_pos
      K hk F htransport u
    have hsqrt : 0 < Real.sqrt
        (monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F)) :=
      Real.sqrt_pos.2 hI
    have hsqrt_complex :
        (Real.sqrt
          (monomialNormSquared k (u : Space n)
            (momentNormalizedPotential F)) : ℂ) ≠ 0 := by
      exact_mod_cast hsqrt.ne'
    have hsquare := Real.sq_sqrt hI.le
    simp only [map_inv₀, Complex.conj_ofReal]
    field_simp
    exact_mod_cast hsquare.symm
  · simp [huv]
def momentMonomialSpan
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Submodule ℂ
      (weightedHilbert k (momentNormalizedPotential F)) :=
  Submodule.span ℂ
    (Set.range (momentNormalizedMonomialLp K hk F htransport))
theorem finrank_momentMonomialSpan
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Module.finrank ℂ
      (momentMonomialSpan K hk F htransport) =
      bergmanDimension K k := by
  let := (monomialIndex_finite K hk).fintype
  unfold momentMonomialSpan
  calc
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range (momentNormalizedMonomialLp
          K hk F htransport))) =
        Fintype.card (monomialIndex K k) :=
          finrank_span_eq_card
            (momentNormalizedMonomialLp_orthonormal
              K hk F htransport).linearIndependent
    _ = bergmanDimension K k := by
      simp [bergmanDimension, Nat.card_eq_fintype_card]
def momentLatticeMonomialBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Basis (monomialIndex K k) ℂ
      (momentMonomialSpan K hk F htransport) :=
  Basis.span
    (momentNormalizedMonomialLp_orthonormal
      K hk F htransport).linearIndependent
theorem momentLatticeMonomialBasis_apply
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    ((momentLatticeMonomialBasis K hk F htransport u :
      momentMonomialSpan K hk F htransport) :
      weightedHilbert k (momentNormalizedPotential F)) =
        momentNormalizedMonomialLp K hk F htransport u := by
  exact Basis.coe_span_apply
    (momentNormalizedMonomialLp_orthonormal
      K hk F htransport).linearIndependent u
theorem momentLatticeMonomialBasis_orthonormal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Orthonormal ℂ (momentLatticeMonomialBasis
      K hk F htransport) := by
  rw [orthonormal_iff_ite]
  intro u v
  change
    @inner ℂ
      (weightedHilbert k (momentNormalizedPotential F)) _
      ((momentLatticeMonomialBasis K hk F htransport u :
        momentMonomialSpan K hk F htransport) :
        weightedHilbert k (momentNormalizedPotential F))
      ((momentLatticeMonomialBasis K hk F htransport v :
        momentMonomialSpan K hk F htransport) :
        weightedHilbert k (momentNormalizedPotential F)) =
      if u = v then 1 else 0
  rw [momentLatticeMonomialBasis_apply,
    momentLatticeMonomialBasis_apply]
  exact (orthonormal_iff_ite.mp
    (momentNormalizedMonomialLp_orthonormal
      K hk F htransport)) u v
def momentMonomialOrthonormalBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    OrthonormalBasis
      (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport) := by
  letI := (monomialIndex_finite K hk).fintype
  exact ((momentLatticeMonomialBasis K hk F htransport).toOrthonormalBasis
    (momentLatticeMonomialBasis_orthonormal
      K hk F htransport)).reindex
        (monomialIndexEquivFin K hk)
theorem momentMonomialOrthonormalBasis_apply
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    ((momentMonomialOrthonormalBasis K hk F htransport
        (monomialIndexEquivFin K hk u) :
          momentMonomialSpan K hk F htransport) :
      weightedHilbert k (momentNormalizedPotential F)) =
        momentNormalizedMonomialLp K hk F htransport u := by
  classical
  let := (monomialIndex_finite K hk).fintype
  simpa [momentMonomialOrthonormalBasis,
    OrthonormalBasis.reindex_apply] using
      momentLatticeMonomialBasis_apply K hk F htransport u
theorem finiteDimensional_momentMonomialSpan
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    FiniteDimensional ℂ
      (momentMonomialSpan K hk F htransport) := by
  let := (monomialIndex_finite K hk).fintype
  exact FiniteDimensional.span_of_finite ℂ
    (Set.finite_range
      (momentNormalizedMonomialLp K hk F htransport))
def momentHolomorphicRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    momentMonomialSpan K hk F htransport →ₗ[ℂ]
      (TorusCharacters.LogSpace n → ℂ) :=
  (Finsupp.linearCombination ℂ
    (normalizedHolomorphicMonomial K hk
      (momentNormalizedPotential F))).comp
        (momentLatticeMonomialBasis
          K hk F htransport).repr.toLinearMap
theorem momentHolomorphicRepresentative_latticeMonomialBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    momentHolomorphicRepresentative K hk F htransport
      (momentLatticeMonomialBasis K hk F htransport u) =
      normalizedHolomorphicMonomial K hk
        (momentNormalizedPotential F) u := by
  classical
  simp [momentHolomorphicRepresentative,
    Finsupp.linearCombination_single]
theorem differentiable_momentHolomorphicRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    Differentiable ℂ
      (momentHolomorphicRepresentative K hk F htransport s) := by
  classical
  unfold momentHolomorphicRepresentative
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  apply Differentiable.sum
  intro u _
  exact
    (differentiable_normalizedHolomorphicMonomial K hk
      (momentNormalizedPotential F) u).const_smul _
def momentHolomorphicJetMap
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ) :
    momentMonomialSpan K hk F htransport →ₗ[ℂ]
      (JetCounting.JetIndexLT n j → ℂ) :=
  (Finsupp.linearCombination ℂ
    (fun u (α : JetCounting.JetIndexLT n j) =>
      holomorphicMonomialJet K hk
        (momentNormalizedPotential F) p u α.val)).comp
    (momentLatticeMonomialBasis K hk F htransport).repr.toLinearMap
def momentJetFiltration
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ) :
    Submodule ℂ (momentMonomialSpan K hk F htransport) :=
  LinearMap.ker
    (momentHolomorphicJetMap K hk F htransport p j)
end BergmanJetBasis
namespace MomentWeakGlobalKernel
open Set Function Filter MeasureTheory Module
open LaplaceAsymptotics MonomialIntegrability BergmanMonomials LatticeAsymptotics MomentMinimizer
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetBasis GlobalBergmanKernelBound
open scoped BigOperators ENNReal InnerProductSpace NNReal Topology
theorem lipschitz_momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (momentNormalizedPotential F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [momentNormalizedPotential, dist_add_right] using
    F.lipschitz.dist_le_mul x y
theorem monomialNormSquared_momentNormalized_global_lower_bound
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) (x : Space n) :
    (2 / (k : ℝ)) ^ n *
        Real.exp
          ((k : ℝ) * phase (u : Space n)
            (momentNormalizedPotential F) x -
              bodyPhaseSlopeBound K) ≤
      monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkreal
  have hφ := lipschitz_momentNormalizedPotential F
  have hslope :
      phaseSlopeBound K (sourceBodyLipschitzConstant K) =
        bodyPhaseSlopeBound K := by
    exact phaseSlopeBound_body K
  have hweight :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport u.property.1 hkreal
  have hballfinite :
      (volume : Measure (Space n))
        (Metric.ball x (k : ℝ)⁻¹) ≠ ⊤ :=
    (measure_ball_lt_top
      (μ := (volume : Measure (Space n)))
      (x := x) (r := (k : ℝ)⁻¹)).ne
  have hconst : IntegrableOn
      (fun _ : Space n =>
        Real.exp
          ((k : ℝ) * phase (u : Space n)
            (momentNormalizedPotential F) x -
              bodyPhaseSlopeBound K))
      (Metric.ball x (k : ℝ)⁻¹)
      (volume : Measure (Space n)) :=
    integrableOn_const hballfinite
  calc
    (2 / (k : ℝ)) ^ n *
        Real.exp
          ((k : ℝ) * phase (u : Space n)
            (momentNormalizedPotential F) x -
              bodyPhaseSlopeBound K) =
        (volume : Measure (Space n)).real
          (Metric.ball x (k : ℝ)⁻¹) *
        Real.exp
          ((k : ℝ) * phase (u : Space n)
            (momentNormalizedPotential F) x -
              bodyPhaseSlopeBound K) := by
          rw [real_volume_ball_inv_nat hk x]
    _ = ∫ _v : Space n in Metric.ball x (k : ℝ)⁻¹,
          Real.exp
            ((k : ℝ) * phase (u : Space n)
              (momentNormalizedPotential F) x -
                bodyPhaseSlopeBound K)
          ∂(volume : Measure (Space n)) := by
          rw [setIntegral_const]
          simp [smul_eq_mul]
    _ ≤ ∫ v : Space n in Metric.ball x (k : ℝ)⁻¹,
          monomialWeight (k : ℝ) (u : Space n)
            (momentNormalizedPotential F) v
          ∂(volume : Measure (Space n)) := by
          apply setIntegral_mono_on hconst hweight.integrableOn
            Metric.isOpen_ball.measurableSet
          intro v hv
          unfold monomialWeight
          apply Real.exp_le_exp.mpr
          have hphase := phase_lower_on_inv_nat_ball
            K hk hφ u x v hv
          rw [hslope] at hphase
          have hscaled := mul_le_mul_of_nonneg_left hphase hkreal.le
          have hcancel :
              (k : ℝ) *
                (phase (u : Space n)
                  (momentNormalizedPotential F) x -
                    bodyPhaseSlopeBound K / (k : ℝ)) =
                (k : ℝ) * phase (u : Space n)
                  (momentNormalizedPotential F) x -
                    bodyPhaseSlopeBound K := by
            field_simp
          rw [hcancel] at hscaled
          exact hscaled
    _ ≤ monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) := by
          unfold monomialNormSquared monomialIntegral
          apply setIntegral_le_integral hweight
          exact Filter.Eventually.of_forall
            (fun _ => (Real.exp_pos _).le)
theorem normalizedMonomialDensity_momentNormalized_global_upper_bound
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) (x : Space n) :
    normalizedMonomialDensity K k
        (momentNormalizedPotential F) u x ≤
      Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkreal
  have hnormpos := momentMonomialNormSquared_pos
    K hk F htransport u
  have hlower :=
    monomialNormSquared_momentNormalized_global_lower_bound
      K hk F htransport u x
  change
    Real.exp ((k : ℝ) * phase (u : Space n)
      (momentNormalizedPotential F) x) /
        monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) ≤
      Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n
  apply (div_le_iff₀ hnormpos).mpr
  have hcancel :
      (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) *
          ((2 / (k : ℝ)) ^ n *
            Real.exp
              ((k : ℝ) * phase (u : Space n)
                (momentNormalizedPotential F) x -
                  bodyPhaseSlopeBound K)) =
        Real.exp ((k : ℝ) * phase (u : Space n)
          (momentNormalizedPotential F) x) := by
    calc
      (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) *
          ((2 / (k : ℝ)) ^ n *
            Real.exp
              ((k : ℝ) * phase (u : Space n)
                (momentNormalizedPotential F) x -
                  bodyPhaseSlopeBound K)) =
        (((k : ℝ) / 2) * (2 / (k : ℝ))) ^ n *
          (Real.exp (bodyPhaseSlopeBound K) *
            Real.exp
              ((k : ℝ) * phase (u : Space n)
                (momentNormalizedPotential F) x -
                  bodyPhaseSlopeBound K)) := by
        rw [mul_pow]
        ring
      _ = Real.exp ((k : ℝ) * phase (u : Space n)
          (momentNormalizedPotential F) x) := by
        have hratio : ((k : ℝ) / 2) * (2 / (k : ℝ)) = 1 := by
          field_simp
        rw [hratio, one_pow, one_mul, ← Real.exp_add]
        congr 1
        ring
  calc
    Real.exp ((k : ℝ) * phase (u : Space n)
        (momentNormalizedPotential F) x) =
      (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) *
          ((2 / (k : ℝ)) ^ n *
            Real.exp
              ((k : ℝ) * phase (u : Space n)
                (momentNormalizedPotential F) x -
                  bodyPhaseSlopeBound K)) := hcancel.symm
    _ ≤ (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) *
        monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) :=
      mul_le_mul_of_nonneg_left hlower (by positivity)
theorem weightedDiagonalKernel_momentNormalized_global_upper_bound
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    weightedDiagonalKernel K k
        (momentNormalizedPotential F) x ≤
      (bergmanDimension K k : ℝ) *
        (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel
  rw [tsum_fintype]
  calc
    (∑ u : monomialIndex K k,
      normalizedMonomialDensity K k
        (momentNormalizedPotential F) u x) ≤
        ∑ _u : monomialIndex K k,
          (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) :=
            Finset.sum_le_sum fun u _ =>
              normalizedMonomialDensity_momentNormalized_global_upper_bound
                K hk F htransport u x
    _ = (bergmanDimension K k : ℝ) *
        (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) := by
          simp [bergmanDimension, Nat.card_eq_fintype_card]
theorem weightedDiagonalKernel_momentNormalized_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    0 < weightedDiagonalKernel K k
      (momentNormalizedPotential F) x := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel
  rw [tsum_fintype]
  apply Finset.sum_pos
  · intro u _
    unfold normalizedMonomialDensity
    exact div_pos (Real.exp_pos _)
      (momentMonomialNormSquared_pos K hk F htransport u)
  · exact ⟨⟨0, zero_mem_monomialIndex K hk⟩,
      Finset.mem_univ _⟩
theorem diagonalKernel_momentNormalized_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    0 < diagonalKernel K k
      (momentNormalizedPotential F) x := by
  have hweighted := weightedDiagonalKernel_momentNormalized_pos
    K hk F htransport x
  rw [weightedDiagonalKernel_eq_exp_neg_mul_diagonalKernel
      K hk (momentNormalizedPotential F) x] at hweighted
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hweighted
theorem eventually_momentNormalized_weightedDiagonalKernel_le_polynomial
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
      weightedDiagonalKernel K k
        (momentNormalizedPotential F) x ≤
        globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
  filter_upwards [eventually_bergmanDimension_le_volume_mul_pow K,
    eventually_gt_atTop (0 : ℕ)] with k hdim hk x
  calc
    weightedDiagonalKernel K k
        (momentNormalizedPotential F) x ≤
      (bergmanDimension K k : ℝ) *
        (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) :=
      weightedDiagonalKernel_momentNormalized_global_upper_bound
        K hk F htransport x
    _ ≤ ((normalizedVolume K.carrier + 1) * (k : ℝ) ^ n) *
        (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) :=
      mul_le_mul_of_nonneg_right hdim (by positivity)
    _ = globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
      unfold globalKernelPolynomialConstant
      rw [show 2 * n = n + n by omega, pow_add, div_pow]
      ring
theorem eventually_momentNormalized_diagonalKernel_le_polynomial
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
      diagonalKernel K k (momentNormalizedPotential F) x ≤
        Real.exp ((k : ℝ) * momentNormalizedPotential F x) *
          globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
  filter_upwards
    [eventually_momentNormalized_weightedDiagonalKernel_le_polynomial
      K F htransport, eventually_gt_atTop (0 : ℕ)]
    with k hweighted hk x
  let φ := momentNormalizedPotential F
  have hw := hweighted x
  rw [weightedDiagonalKernel_eq_exp_neg_mul_diagonalKernel
      K hk φ x] at hw
  have hscaled := mul_le_mul_of_nonneg_left hw
    (Real.exp_pos ((k : ℝ) * φ x)).le
  have hcancel :
      Real.exp ((k : ℝ) * φ x) *
        Real.exp (-(k : ℝ) * φ x) = 1 := by
    rw [← Real.exp_add,
      show (k : ℝ) * φ x + -(k : ℝ) * φ x = 0 by ring,
      Real.exp_zero]
  rw [← mul_assoc, hcancel, one_mul] at hscaled
  simpa only [mul_assoc] using hscaled
theorem eventually_log_momentNormalized_diagonalKernel_div_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
      Real.log (diagonalKernel K k
          (momentNormalizedPotential F) x) / (k : ℝ) ≤
        momentNormalizedPotential F x +
          globalKernelLogError K k := by
  filter_upwards
    [eventually_momentNormalized_diagonalKernel_le_polynomial
      K F htransport, eventually_gt_atTop (0 : ℕ)]
    with k hpoly hk x
  let φ := momentNormalizedPotential F
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hconstant := globalKernelPolynomialConstant_pos K
  have hdiag := diagonalKernel_momentNormalized_pos
    K hk F htransport x
  have hmajor : 0 <
      Real.exp ((k : ℝ) * φ x) *
        globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
    positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    hdiag hmajor (hpoly x)
  have hexpand :
      Real.log (Real.exp ((k : ℝ) * φ x) *
          globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)) =
        (k : ℝ) * φ x + Real.log (globalKernelPolynomialConstant K) +
          2 * (n : ℝ) * Real.log (k : ℝ) := by
    rw [Real.log_mul
      (mul_ne_zero (Real.exp_ne_zero _)
        (ne_of_gt hconstant)) (pow_ne_zero _ (ne_of_gt hkreal)),
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hconstant),
      Real.log_exp, Real.log_pow]
    push_cast
    ring
  rw [hexpand] at hlog
  unfold globalKernelLogError
  apply (div_le_iff₀ hkreal).mpr
  calc
    Real.log (diagonalKernel K k φ x) ≤
        (k : ℝ) * φ x + Real.log (globalKernelPolynomialConstant K) +
          2 * (n : ℝ) * Real.log (k : ℝ) := hlog
    _ = (φ x +
        (Real.log (globalKernelPolynomialConstant K) +
          2 * (n : ℝ) * Real.log (k : ℝ)) / (k : ℝ)) * (k : ℝ) := by
      field_simp
      ring_nf
theorem eventually_log_momentNormalized_diagonalKernel_div_le_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
      Real.log (diagonalKernel K k
        (momentNormalizedPotential F) x) / (k : ℝ) ≤
        momentNormalizedPotential F x + ε := by
  have herr := (tendsto_globalKernelLogError K).eventually
    (gt_mem_nhds hε)
  filter_upwards
    [eventually_log_momentNormalized_diagonalKernel_div_le
      K F htransport, herr] with k hupper hsmall x
  exact (hupper x).trans (add_le_add_right hsmall.le _)
end MomentWeakGlobalKernel
namespace BergmanJetGeodesic
open Set Function Filter MeasureTheory Module
open BergmanMonomials LatticeAsymptotics AdaptedBergmanBasis MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetBasis JetAdaptedOrthonormalBasis
open GenuineJetAdaptedBasisCounting
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology
theorem momentJetFiltration_antitone
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {j l : ℕ} (hjl : j ≤ l) :
    momentJetFiltration K hk F htransport p l ≤
      momentJetFiltration K hk F htransport p j := by
  classical
  intro s hs
  change momentHolomorphicJetMap K hk F htransport p l s = 0 at hs
  change momentHolomorphicJetMap K hk F htransport p j s = 0
  funext α
  let β : JetCounting.JetIndexLT n l :=
    ⟨α.val, lt_of_lt_of_le α.property hjl⟩
  have hβ := congrFun hs β
  simp only [momentHolomorphicJetMap, LinearMap.comp_apply,
    Finsupp.linearCombination_apply, Finsupp.sum] at hβ ⊢
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hβ ⊢
  exact hβ
theorem exists_momentSimultaneousJetBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) :
    ∃ b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport),
      ∀ (j : ℕ) (i : Fin (bergmanDimension K k)),
        b i ∈ momentJetFiltration K hk F htransport p j ∨
        b i ∈ (momentJetFiltration K hk F htransport p j)ᗮ := by
  classical
  let := finiteDimensional_momentMonomialSpan K hk F htransport
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_simultaneously_adapted
    (momentJetFiltration K hk F htransport p)
    (fun _ _ h => momentJetFiltration_antitone
      K hk F htransport p h)
  let e := finCongr
    (finrank_momentMonomialSpan K hk F htransport)
  refine ⟨b.reindex e, ?_⟩
  intro j i
  simpa only [OrthonormalBasis.reindex_apply] using
    hb j (e.symm i)
def momentSimultaneousJetBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) :
    OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport) :=
  Classical.choose
    (exists_momentSimultaneousJetBasis K hk F htransport p)
def momentUpperJetBasisIndices
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ) :
    Finset (Fin (bergmanDimension K k)) :=
  adaptedIndices (momentSimultaneousJetBasis K hk F htransport p)
    (momentJetFiltration K hk F htransport p j)
def momentTruncatedJetOrder
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k)) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun j =>
    momentSimultaneousJetBasis K hk F htransport p i ∈
      momentJetFiltration K hk F htransport p (j + 1))).card
theorem momentTruncatedJetOrder_le
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k)) :
    momentTruncatedJetOrder K hk F htransport p N i ≤ N := by
  classical
  unfold momentTruncatedJetOrder
  simpa using Finset.card_filter_le (s := Finset.range N)
    (p := fun j =>
      momentSimultaneousJetBasis K hk F htransport p i ∈
        momentJetFiltration K hk F htransport p (j + 1))
def momentHolomorphicBasisWeight
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n)
    (i : Fin (bergmanDimension K k)) : ℝ :=
  Complex.normSq
    (momentHolomorphicRepresentative
      K hk F htransport (b i) z)
theorem momentHolomorphicBasisWeight_nonneg
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n)
    (i : Fin (bergmanDimension K k)) :
    0 ≤ momentHolomorphicBasisWeight
      K hk F htransport b z i :=
  Complex.normSq_nonneg _
theorem exists_positive_momentHolomorphicBasisWeight
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    ∃ i, 0 < momentHolomorphicBasisWeight
      K hk F htransport b z i := by
  classical
  by_contra! hzero
  have hvanish : ∀ i,
      momentHolomorphicRepresentative
        K hk F htransport (b i) z = 0 := by
    intro i
    apply Complex.normSq_eq_zero.mp
    exact le_antisymm (hzero i)
      (momentHolomorphicBasisWeight_nonneg
        K hk F htransport b z i)
  let u : monomialIndex K k :=
    ⟨0, zero_mem_monomialIndex K hk⟩
  let s := momentLatticeMonomialBasis
    K hk F htransport u
  have hrep : momentHolomorphicRepresentative
      K hk F htransport s z = 0 := by
    rw [← b.sum_repr s]
    simp [map_sum, map_smul, hvanish]
  rw [momentHolomorphicRepresentative_latticeMonomialBasis]
    at hrep
  unfold normalizedHolomorphicMonomial at hrep
  have hnorm := momentMonomialNormSquared_pos
    K hk F htransport u
  have hsqrt :
      (Real.sqrt (monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hnorm).ne'
  exact (mul_ne_zero (inv_ne_zero hsqrt)
    (TorusCharacters.torusCharacter_ne_zero _ z)) hrep
def momentJointJetSection
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k))
    (q : TorusCharacters.LogSpace n × ℂ) : ℂ :=
  momentHolomorphicRepresentative K hk F htransport
      (momentSimultaneousJetBasis
        K hk F htransport p i) q.1 *
    q.2 ^ (momentTruncatedJetOrder
      K hk F htransport p N i)
theorem differentiable_momentJointJetSection
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k)) :
    Differentiable ℂ
      (momentJointJetSection K hk F htransport p N i) := by
  unfold momentJointJetSection
  exact
    ((differentiable_momentHolomorphicRepresentative
      K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i)).comp differentiable_fst).mul
      (differentiable_snd.pow
        (momentTruncatedJetOrder K hk F htransport p N i))
def momentJointJetSectionVector
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (q : TorusCharacters.LogSpace n × ℂ) :
    EuclideanSpace ℂ (Fin (bergmanDimension K k)) :=
  WithLp.toLp 2
    (fun i => momentJointJetSection
      K hk F htransport p N i q)
theorem differentiable_momentJointJetSectionVector
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ) :
    Differentiable ℂ
      (momentJointJetSectionVector K hk F htransport p N) := by
  apply (differentiable_piLp 2).2
  intro i
  exact differentiable_momentJointJetSection
    K hk F htransport p N i
def momentJointJetDiagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (q : TorusCharacters.LogSpace n × ℂ) : ℝ :=
  ∑ i : Fin (bergmanDimension K k),
    Complex.normSq
      (momentJointJetSection K hk F htransport p N i q)
theorem momentJointJetSectionVector_norm_sq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (q : TorusCharacters.LogSpace n × ℂ) :
    ‖momentJointJetSectionVector
      K hk F htransport p N q‖ ^ 2 =
      momentJointJetDiagonal K hk F htransport p N q := by
  rw [EuclideanSpace.norm_sq_eq]
  change
    (∑ i, ‖momentJointJetSection
      K hk F htransport p N i q‖ ^ 2) =
      ∑ i, Complex.normSq
        (momentJointJetSection
          K hk F htransport p N i q)
  exact Finset.sum_congr rfl
    (fun i _ => (Complex.normSq_eq_norm_sq _).symm)
theorem momentJointJetDiagonal_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n)
    {τ : ℂ} (hτ : τ ≠ 0) :
    0 < momentJointJetDiagonal
      K hk F htransport p N (z, τ) := by
  classical
  obtain ⟨i, hi⟩ :=
    exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis
        K hk F htransport p) z
  have hvalue :
      momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z ≠ 0 :=
    Complex.normSq_pos.mp hi
  have hsection :
      momentJointJetSection
        K hk F htransport p N i (z, τ) ≠ 0 := by
    exact mul_ne_zero hvalue (pow_ne_zero _ hτ)
  unfold momentJointJetDiagonal
  apply lt_of_lt_of_le (Complex.normSq_pos.mpr hsection)
  have hnonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin (bergmanDimension K k))),
        0 ≤ Complex.normSq
          (momentJointJetSection
            K hk F htransport p N j (z, τ)) :=
    fun j _ => Complex.normSq_nonneg _
  exact Finset.single_le_sum hnonneg (Finset.mem_univ i)
end BergmanJetGeodesic
namespace BergmanJetProfileBridge
open Set Function Filter MeasureTheory Module InnerProductSpace
open SupportFunction BergmanMonomials LatticeAsymptotics WeightedTorusHilbert AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity BergmanJetBasis
open BergmanJetGeodesic BergmanDiagonalBasisIndependence
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology
theorem normSq_momentHolomorphicMonomial_realLogSlice_eq_diagonalTerm
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) (x : Space n) :
    Complex.normSq
      (normalizedHolomorphicMonomial K hk
        (momentNormalizedPotential F) u
        (TorusCharacters.realLogSlice x)) =
      diagonalTerm K k (momentNormalizedPotential F) u x := by
  have hnorm := momentMonomialNormSquared_pos
    K hk F htransport u
  have hsqrt :
      Real.sqrt (monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F)) *
        Real.sqrt (monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F)) =
      monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) := by
    simpa [pow_two] using Real.sq_sqrt hnorm.le
  have hpair :
      (∑ i, (integerExponent K hk u i : ℝ) * x i) =
        (k : ℝ) * pairing (u : Space n) x := by
    calc
      (∑ i, (integerExponent K hk u i : ℝ) * x i) =
        pairing (integerPoint n (integerExponent K hk u)) x :=
          rfl
      _ = pairing ((k : ℝ) • (u : Space n)) x := by
          rw [integerPoint_integerExponent K hk u]
      _ = (k : ℝ) * pairing (u : Space n) x := by
          simp [pairing, Finset.mul_sum, mul_assoc]
  unfold normalizedHolomorphicMonomial
  rw [Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_ofReal, hsqrt, Complex.normSq_eq_norm_sq,
    TorusCharacters.norm_sq_torusCharacter_realLogSlice,
    hpair]
  simp [diagonalTerm, div_eq_mul_inv, mul_comm]
theorem normSq_momentHolomorphicMonomial_eq_diagonalTerm
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    (z : TorusCharacters.LogSpace n) :
    Complex.normSq
      (normalizedHolomorphicMonomial K hk
        (momentNormalizedPotential F) u z) =
      diagonalTerm K k (momentNormalizedPotential F) u
        (realLogCoordinate z) := by
  calc
    Complex.normSq
        (normalizedHolomorphicMonomial K hk
          (momentNormalizedPotential F) u z) =
      Complex.normSq
        (normalizedHolomorphicMonomial K hk
          (momentNormalizedPotential F) u
            (TorusCharacters.realLogSlice
              (realLogCoordinate z))) := by
        unfold normalizedHolomorphicMonomial
        rw [Complex.normSq_mul, Complex.normSq_mul,
          normSq_torusCharacter_eq_realLogSlice]
    _ = diagonalTerm K k (momentNormalizedPotential F) u
          (realLogCoordinate z) :=
      normSq_momentHolomorphicMonomial_realLogSlice_eq_diagonalTerm
        K hk F htransport u (realLogCoordinate z)
theorem momentHolomorphicRepresentative_monomialOrthonormalBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    momentHolomorphicRepresentative K hk F htransport
      (momentMonomialOrthonormalBasis K hk F htransport
        (monomialIndexEquivFin K hk u)) =
      normalizedHolomorphicMonomial K hk
        (momentNormalizedPotential F) u := by
  have hmono :
      momentMonomialOrthonormalBasis K hk F htransport
          (monomialIndexEquivFin K hk u) =
        momentLatticeMonomialBasis K hk F htransport u := by
    apply Subtype.ext
    exact
      (momentMonomialOrthonormalBasis_apply
        K hk F htransport u).trans
      (momentLatticeMonomialBasis_apply
        K hk F htransport u).symm
  rw [hmono]
  exact momentHolomorphicRepresentative_latticeMonomialBasis
    K hk F htransport u
def momentHolomorphicEvaluationRepresenter
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    momentMonomialSpan K hk F htransport :=
  ∑ i, (starRingEnd ℂ)
    (momentHolomorphicRepresentative
      K hk F htransport (b i) z) • b i
theorem momentHolomorphicEvaluationRepresenter_inner
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport) :
    @inner ℂ _ _
      (momentHolomorphicEvaluationRepresenter
        K hk F htransport b z) s =
      momentHolomorphicRepresentative
        K hk F htransport s z := by
  classical
  have hrepr := congrArg
    (fun v : momentMonomialSpan K hk F htransport =>
      momentHolomorphicRepresentative
        K hk F htransport v z)
    (b.sum_repr' s)
  calc
    @inner ℂ _ _
        (momentHolomorphicEvaluationRepresenter
          K hk F htransport b z) s =
      ∑ i, (momentHolomorphicRepresentative
          K hk F htransport (b i) z) *
        (@inner ℂ _ _ (b i) s) := by
          rw [momentHolomorphicEvaluationRepresenter, sum_inner]
          apply Finset.sum_congr rfl
          intro i _
          simp [inner_smul_left]
    _ = ∑ i, (@inner ℂ _ _ (b i) s) *
        (momentHolomorphicRepresentative
          K hk F htransport (b i) z) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = momentHolomorphicRepresentative
        K hk F htransport s z := by
          simpa [map_sum, map_smul, Pi.smul_apply, smul_eq_mul]
            using hrepr
theorem sum_normSq_momentHolomorphicRepresentative_eq_representer_norm_sq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b b₀ : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    (∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport (b i) z)) =
      ‖momentHolomorphicEvaluationRepresenter
        K hk F htransport b₀ z‖ ^ 2 := by
  classical
  calc
    (∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport (b i) z)) =
      ∑ i, ‖@inner ℂ _ _
        (momentHolomorphicEvaluationRepresenter
          K hk F htransport b₀ z) (b i)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [momentHolomorphicEvaluationRepresenter_inner,
            Complex.normSq_eq_norm_sq]
    _ = ‖momentHolomorphicEvaluationRepresenter
        K hk F htransport b₀ z‖ ^ 2 :=
      b.sum_sq_norm_inner_left _
theorem sum_momentHolomorphicBasisWeight_eq_of_orthonormalBases
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b b' : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    (∑ i, momentHolomorphicBasisWeight
      K hk F htransport b z i) =
      ∑ i, momentHolomorphicBasisWeight
        K hk F htransport b' z i := by
  unfold momentHolomorphicBasisWeight
  calc
    (∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport (b i) z)) =
      ‖momentHolomorphicEvaluationRepresenter
        K hk F htransport b z‖ ^ 2 :=
      sum_normSq_momentHolomorphicRepresentative_eq_representer_norm_sq
        K hk F htransport b b z
    _ = ∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport (b' i) z) :=
      (sum_normSq_momentHolomorphicRepresentative_eq_representer_norm_sq
        K hk F htransport b' b z).symm
theorem sum_momentMonomialHolomorphicBasisWeight_eq_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (z : TorusCharacters.LogSpace n) :
    (∑ i, momentHolomorphicBasisWeight
      K hk F htransport
        (momentMonomialOrthonormalBasis K hk F htransport)
        z i) =
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := by
  classical
  let := (monomialIndex_finite K hk).fintype
  unfold momentHolomorphicBasisWeight
  calc
    (∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport
          (momentMonomialOrthonormalBasis
            K hk F htransport i) z)) =
      ∑ u : monomialIndex K k,
        Complex.normSq
          (momentHolomorphicRepresentative
            K hk F htransport
              (momentMonomialOrthonormalBasis
                K hk F htransport
                  (monomialIndexEquivFin K hk u)) z) := by
        symm
        exact (monomialIndexEquivFin K hk).sum_comp
          (fun i => Complex.normSq
            (momentHolomorphicRepresentative
              K hk F htransport
                (momentMonomialOrthonormalBasis
                  K hk F htransport i) z))
    _ = ∑ u : monomialIndex K k,
        diagonalTerm K k (momentNormalizedPotential F)
          u (realLogCoordinate z) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [momentHolomorphicRepresentative_monomialOrthonormalBasis
          K hk F htransport u]
        exact normSq_momentHolomorphicMonomial_eq_diagonalTerm
          K hk F htransport u z
    _ = diagonalKernel K k (momentNormalizedPotential F)
          (realLogCoordinate z) := by
        unfold diagonalKernel
        rw [tsum_fintype]
theorem sum_momentHolomorphicBasisWeight_eq_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    (∑ i, momentHolomorphicBasisWeight
      K hk F htransport b z i) =
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := by
  calc
    (∑ i, momentHolomorphicBasisWeight
      K hk F htransport b z i) =
      ∑ i, momentHolomorphicBasisWeight
        K hk F htransport
          (momentMonomialOrthonormalBasis K hk F htransport)
          z i :=
        sum_momentHolomorphicBasisWeight_eq_of_orthonormalBases
          K hk F htransport b
            (momentMonomialOrthonormalBasis
              K hk F htransport) z
    _ = diagonalKernel K k (momentNormalizedPotential F)
          (realLogCoordinate z) :=
      sum_momentMonomialHolomorphicBasisWeight_eq_diagonalKernel
        K hk F htransport z
theorem momentJointJetDiagonal_one_eq_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ) :
    momentJointJetDiagonal
      K hk F htransport p N (z, (1 : ℂ)) =
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := by
  unfold momentJointJetDiagonal momentJointJetSection
  simp only [one_pow, mul_one]
  exact sum_momentHolomorphicBasisWeight_eq_diagonalKernel
    K hk F htransport
    (momentSimultaneousJetBasis K hk F htransport p) z
def normalizedMomentTruncatedJetOrderProfile
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (t : ℝ) (k : ℕ) : ℝ :=
  if hk : 0 < k then
    ((∑ i : Fin (bergmanDimension K k),
      momentTruncatedJetOrder K hk F htransport p
        (Nat.floor (t * (k : ℝ))) i) : ℝ) /
      ((k : ℝ) * (bergmanDimension K k : ℝ))
  else 0
end BergmanJetProfileBridge
namespace BergmanJetRealGeodesic
open Set Function Filter MeasureTheory Module
open BergmanMonomials MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge BergmanGeodesicConvexity
open BergmanDiagonalBasisIndependence
open scoped BigOperators ENNReal InnerProductSpace Topology
def momentJetGeodesic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) : ℝ :=
  logarithmicPotential
    (momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z)
    (momentTruncatedJetOrder K hk F htransport p N)
    (k : ℝ) t
theorem momentJointJetDiagonal_realTime
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    momentJointJetDiagonal K hk F htransport p N
        (z, (Real.exp (t / 2) : ℂ)) =
      exponentialPartition
        (momentHolomorphicBasisWeight
          K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z)
        (momentTruncatedJetOrder K hk F htransport p N) t := by
  classical
  unfold momentJointJetDiagonal exponentialPartition
    exponentialMoment
  simp only [pow_zero, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  unfold momentJointJetSection momentHolomorphicBasisWeight
  rw [Complex.normSq_mul, map_pow, Complex.normSq_ofReal,
    ← Real.exp_add]
  have hhalf : t / 2 + t / 2 = t := by ring
  rw [hhalf, ← Real.exp_nat_mul]
  congr 2
  ring
theorem momentJetGeodesic_eq_log_jointJetDiagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    momentJetGeodesic K hk F htransport p N z t =
      Real.log (momentJointJetDiagonal K hk F htransport p N
        (z, (Real.exp (t / 2) : ℂ))) / (k : ℝ) := by
  unfold momentJetGeodesic logarithmicPotential
  rw [momentJointJetDiagonal_realTime]
theorem momentJetGeodesic_zero_eq_log_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ) :
    momentJetGeodesic K hk F htransport p N z 0 =
      Real.log (diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z)) / (k : ℝ) := by
  rw [momentJetGeodesic_eq_log_jointJetDiagonal]
  norm_num
  rw [momentJointJetDiagonal_one_eq_diagonalKernel]
theorem momentJetGeodesic_deriv_nonneg
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    0 ≤ deriv (momentJetGeodesic
      K hk F htransport p N z) t := by
  unfold momentJetGeodesic
  apply logarithmicPotential_deriv_nonneg
  · exact momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact_mod_cast hk
theorem momentJetGeodesic_deriv_le_cutoff
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    deriv (momentJetGeodesic
      K hk F htransport p N z) t ≤
      (N : ℝ) / (k : ℝ) := by
  unfold momentJetGeodesic
  apply logarithmicPotential_deriv_le
  · exact momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact_mod_cast hk
  · exact momentTruncatedJetOrder_le K hk F htransport p N
theorem momentJetGeodesic_deriv_le_floor_cutoff
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {a : ℝ} (ha : 0 ≤ a)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    deriv (momentJetGeodesic K hk F htransport p
      (Nat.floor (a * (k : ℝ))) z) t ≤ a := by
  have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  calc
    deriv (momentJetGeodesic K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z) t ≤
        ((Nat.floor (a * (k : ℝ)) : ℕ) : ℝ) / (k : ℝ) :=
      momentJetGeodesic_deriv_le_cutoff K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z t
    _ ≤ a :=
      (div_le_iff₀ hkreal).mpr
        (Nat.floor_le (mul_nonneg ha hkreal.le))
theorem momentJetGeodesic_le_zero_add_linear
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    momentJetGeodesic K hk F htransport p N z t ≤
      momentJetGeodesic K hk F htransport p N z 0 +
        (N : ℝ) / (k : ℝ) * t := by
  let w := momentHolomorphicBasisWeight
    K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  let order := momentTruncatedJetOrder
    K hk F htransport p N
  have hw : ∀ i, 0 ≤ w i :=
    momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  have hpositive : ∃ i, 0 < w i :=
    exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  have horder : ∀ i, order i ≤ N :=
    momentTruncatedJetOrder_le K hk F htransport p N
  have hsum : 0 < ∑ i, w i := by
    have h := exponentialPartition_pos
      w order hw hpositive 0
    simpa [exponentialPartition, exponentialMoment] using h
  have hpart :=
    BergmanDiagonalBasisIndependence.exponentialPartition_le_exp_mul_sum
      w order hw N horder ht
  have hpartpos := exponentialPartition_pos
    w order hw hpositive t
  have hlog :
      Real.log (exponentialPartition w order t) ≤
        t * (N : ℝ) + Real.log (∑ i, w i) := by
    calc
      Real.log (exponentialPartition w order t) ≤
        Real.log (Real.exp (t * (N : ℝ)) * ∑ i, w i) :=
          Real.log_le_log hpartpos hpart
      _ = t * (N : ℝ) + Real.log (∑ i, w i) := by
        rw [Real.log_mul (Real.exp_ne_zero _) hsum.ne',
          Real.log_exp]
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  change
    Real.log (exponentialPartition w order t) / (k : ℝ) ≤
      Real.log (exponentialPartition w order 0) / (k : ℝ) +
        (N : ℝ) / (k : ℝ) * t
  have hzero : exponentialPartition w order 0 = ∑ i, w i := by
    simp [exponentialPartition, exponentialMoment]
  rw [hzero]
  apply (div_le_iff₀ hkreal).mpr
  calc
    Real.log (exponentialPartition w order t) ≤
      t * (N : ℝ) + Real.log (∑ i, w i) := hlog
    _ = (Real.log (∑ i, w i) / (k : ℝ) +
      (N : ℝ) / (k : ℝ) * t) * (k : ℝ) := by
      field_simp
      ring
theorem eventually_momentJetGeodesic_zero_le_potential_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (hk : 0 < k)
        (p z : TorusCharacters.LogSpace n) (N : ℕ),
      momentJetGeodesic K hk F htransport p N z 0 ≤
        momentNormalizedPotential F
          (realLogCoordinate z) + ε := by
  filter_upwards
    [eventually_log_momentNormalized_diagonalKernel_div_le_add
      K F htransport hε] with k hupper hk p z N
  rw [momentJetGeodesic_zero_eq_log_diagonalKernel]
  exact hupper (realLogCoordinate z)
theorem eventually_momentJetGeodesic_le_potential_add_linear
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {a : ℝ} (ha : 0 ≤ a)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (hk : 0 < k)
        (p z : TorusCharacters.LogSpace n)
        (t : ℝ), 0 ≤ t →
      momentJetGeodesic K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z t ≤
        momentNormalizedPotential F
          (realLogCoordinate z) + ε + a * t := by
  filter_upwards
    [eventually_momentJetGeodesic_zero_le_potential_add
      K F htransport hε] with k hzero hk p z t ht
  have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hfloor :
      ((Nat.floor (a * (k : ℝ)) : ℕ) : ℝ) / (k : ℝ) ≤ a :=
    (div_le_iff₀ hkreal).mpr
      (Nat.floor_le (mul_nonneg ha hkreal.le))
  calc
    momentJetGeodesic K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z t ≤
      momentJetGeodesic K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z 0 +
          ((Nat.floor (a * (k : ℝ)) : ℕ) : ℝ) /
            (k : ℝ) * t :=
      momentJetGeodesic_le_zero_add_linear
        K hk F htransport p z (Nat.floor (a * (k : ℝ))) ht
    _ ≤ (momentNormalizedPotential F
          (realLogCoordinate z) + ε) + a * t :=
      add_le_add
        (hzero hk p z (Nat.floor (a * (k : ℝ))))
        (mul_le_mul_of_nonneg_right hfloor ht)
    _ = momentNormalizedPotential F
          (realLogCoordinate z) + ε + a * t := by ring
end BergmanJetRealGeodesic
namespace ActualJetPlurisubharmonicClosure
open Set Metric Filter Function MeasureTheory
open ActualJetUpperEnvelope
open scoped BigOperators Topology ENNReal
theorem exists_mem_ball_sub_lt_upperRegularization
    {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (x : X) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ y ∈ Metric.ball x ε,
      upperRegularization f x - δ < f y := by
  by_contra h
  push Not at h
  have hev :
      ∀ᶠ y : X in 𝓝 x,
        f y ≤ upperRegularization f x - δ :=
    Filter.mem_of_superset (Metric.ball_mem_nhds x hε) h
  have hle :=
    upperRegularization_le_of_eventually f x hev
  linarith
theorem exists_mem_ball_family_sub_lt_upperRegularization
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ y ∈ Metric.ball x ε, ∃ i : ι,
      upperRegularization
        (fun z : X => sSup (Set.range fun j => F j z)) x - δ <
        F i y := by
  obtain ⟨y, hy, hlt⟩ :=
    exists_mem_ball_sub_lt_upperRegularization
      (fun z : X => sSup (Set.range fun j => F j z))
      x hε hδ
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ :=
    exists_lt_of_lt_csSup
      (Set.range_nonempty fun j : ι => F j y) hlt
  exact ⟨y, hy, i, hi⟩
def regularizationApproximationRadius (m : ℕ) : ℝ :=
  1 / ((m + 1 : ℕ) : ℝ)
theorem regularizationApproximationRadius_pos (m : ℕ) :
    0 < regularizationApproximationRadius m := by
  unfold regularizationApproximationRadius
  positivity
theorem tendsto_regularizationApproximationRadius :
    Tendsto regularizationApproximationRadius atTop (𝓝 0) := by
  change Tendsto
    (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0)
  simpa [Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
theorem exists_upperRegularizationFamilyApproximant
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) (m : ℕ) :
    ∃ z : X × ι,
      z.1 ∈ Metric.ball x (regularizationApproximationRadius m) ∧
        upperRegularization
          (fun y : X => sSup (Set.range fun j => F j y)) x -
            regularizationApproximationRadius m < F z.2 z.1 := by
  obtain ⟨y, hy, i, hi⟩ :=
    exists_mem_ball_family_sub_lt_upperRegularization
      F x (regularizationApproximationRadius_pos m)
        (regularizationApproximationRadius_pos m)
  exact ⟨(y, i), hy, hi⟩
def upperRegularizationFamilyApproximant
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) (m : ℕ) : X × ι :=
  Classical.choose
    (exists_upperRegularizationFamilyApproximant F x m)
theorem upperRegularizationFamilyApproximant_mem_ball
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) (m : ℕ) :
    (upperRegularizationFamilyApproximant F x m).1 ∈
      Metric.ball x (regularizationApproximationRadius m) := by
  exact (Classical.choose_spec
    (exists_upperRegularizationFamilyApproximant F x m)).1
theorem upperRegularizationFamilyApproximant_sub_lt
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) (m : ℕ) :
    upperRegularization
        (fun y : X => sSup (Set.range fun j => F j y)) x -
          regularizationApproximationRadius m <
      F (upperRegularizationFamilyApproximant F x m).2
        (upperRegularizationFamilyApproximant F x m).1 := by
  exact (Classical.choose_spec
    (exists_upperRegularizationFamilyApproximant F x m)).2
theorem tendsto_upperRegularizationFamilyApproximant_center
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) :
    Tendsto
      (fun m : ℕ =>
        (upperRegularizationFamilyApproximant F x m).1)
      atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev :
      ∀ᶠ m : ℕ in atTop,
        regularizationApproximationRadius m < ε :=
    tendsto_regularizationApproximationRadius
      (Iio_mem_nhds hε)
  filter_upwards [hev] with m hm
  exact lt_trans
    (Metric.mem_ball.mp
      (upperRegularizationFamilyApproximant_mem_ball F x m)) hm
theorem tendsto_upperRegularizationFamilyApproximant_value
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X)
    (hbounded : ∀ y : X,
      BddAbove (Set.range fun i : ι => F i y))
    (hlocal : ∀ y : X,
      (localUpperBounds
        (fun z : X => sSup (Set.range fun i => F i z)) y).Nonempty) :
    Tendsto
      (fun m : ℕ =>
        F (upperRegularizationFamilyApproximant F x m).2
          (upperRegularizationFamilyApproximant F x m).1)
      atTop
      (𝓝 (upperRegularization
        (fun y : X => sSup (Set.range fun i => F i y)) x)) := by
  let f : X → ℝ :=
    fun y => sSup (Set.range fun i : ι => F i y)
  have hreg : UpperSemicontinuous (upperRegularization f) :=
    upperSemicontinuous_upperRegularization f hlocal
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hlow :
        Tendsto
          (fun m : ℕ =>
            upperRegularization f x -
              regularizationApproximationRadius m)
          atTop (𝓝 (upperRegularization f x)) := by
      simpa using
        tendsto_regularizationApproximationRadius.const_sub
          (upperRegularization f x)
    filter_upwards [(tendsto_order.mp hlow).1 a ha] with m hm
    exact hm.trans
      (upperRegularizationFamilyApproximant_sub_lt F x m)
  · intro a ha
    have hnear :
        ∀ᶠ y : X in 𝓝 x,
          upperRegularization f y < a :=
      hreg x a ha
    have hev :=
      (tendsto_upperRegularizationFamilyApproximant_center F x)
        hnear
    filter_upwards [hev] with m hm
    let y := (upperRegularizationFamilyApproximant F x m).1
    let i := (upperRegularizationFamilyApproximant F x m).2
    have hfamily : F i y ≤ f y := by
      exact le_csSup (hbounded y) ⟨i, rfl⟩
    have hupper : f y ≤ upperRegularization f y :=
      le_upperRegularization f y (hlocal y)
    exact (hfamily.trans hupper).trans_lt hm
theorem limsup_integral_le_of_nonnegative_bounded
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (g : α → ℝ) (C : ℝ)
    (hFmeas : ∀ m : ℕ, Measurable (F m))
    (hgint : Integrable g μ)
    (hFnonneg : ∀ m : ℕ, ∀ a : α, 0 ≤ F m a)
    (hFbound : ∀ m : ℕ, ∀ a : α, F m a ≤ C)
    (hgnonneg : ∀ᵐ a ∂μ, 0 ≤ g a)
    (hlimsup : ∀ᵐ a ∂μ,
      Filter.limsup (fun m : ℕ => F m a) atTop ≤ g a) :
    Filter.limsup (fun m : ℕ => ∫ a, F m a ∂μ) atTop ≤
      ∫ a, g a ∂μ := by
  have hFint (m : ℕ) : Integrable (F m) μ := by
    refine (integrable_const C).mono'
      ((hFmeas m).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg m a)]
      exact hFbound m a
  have hintnonneg (m : ℕ) : 0 ≤ ∫ a, F m a ∂μ :=
    integral_nonneg (hFnonneg m)
  have hintbound (m : ℕ) :
      (∫ a, F m a ∂μ) ≤ ∫ _ : α, C ∂μ :=
    integral_mono (hFint m) (integrable_const C)
      (hFbound m)
  have hseqcob :
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun m : ℕ => ∫ a, F m a ∂μ) :=
    Filter.isCoboundedUnder_le_of_le atTop hintnonneg
  have hseqbdd :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun m : ℕ => ∫ a, F m a ∂μ) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall hintbound)
  apply (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg_of_ae hgnonneg)).mp
  rw [ENNReal.ofReal_limsup hseqcob hseqbdd]
  have hrewrite (m : ℕ) :
      ENNReal.ofReal (∫ a, F m a ∂μ) =
        ∫⁻ a, ENNReal.ofReal (F m a) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (hFint m)
      (Filter.Eventually.of_forall (hFnonneg m))
  simp_rw [hrewrite]
  calc
    Filter.limsup
        (fun m : ℕ => ∫⁻ a, ENNReal.ofReal (F m a) ∂μ)
          atTop ≤
        ∫⁻ a,
          Filter.limsup
            (fun m : ℕ => ENNReal.ofReal (F m a)) atTop ∂μ := by
      apply MeasureTheory.limsup_lintegral_le
        (fun _ : α => ENNReal.ofReal C)
      · intro m
        exact ENNReal.continuous_ofReal.measurable.comp
          (hFmeas m)
      · intro m
        exact Filter.Eventually.of_forall fun a =>
          ENNReal.ofReal_le_ofReal (hFbound m a)
      · rw [lintegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (measure_ne_top μ Set.univ)
    _ ≤ ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hlimsup] with a ha
      have hpcob :
          Filter.IsCoboundedUnder (· ≤ ·) atTop
            (fun m : ℕ => F m a) :=
        Filter.isCoboundedUnder_le_of_le atTop
          (fun m => hFnonneg m a)
      have hpbdd :
          Filter.IsBoundedUnder (· ≤ ·) atTop
            (fun m : ℕ => F m a) :=
        Filter.isBoundedUnder_of_eventually_le
          (Filter.Eventually.of_forall
            (fun m => hFbound m a))
      change
        Filter.limsup
          (fun m : ℕ => ENNReal.ofReal (F m a)) atTop ≤
            ENNReal.ofReal (g a)
      rw [← ENNReal.ofReal_limsup hpcob hpbdd]
      exact ENNReal.ofReal_le_ofReal ha
    _ = ENNReal.ofReal (∫ a, g a ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hgint hgnonneg).symm
theorem limsup_le_of_upperSemicontinuous_of_tendsto
    {X : Type*} [TopologicalSpace X]
    (u : X → ℝ) (hu : UpperSemicontinuous u)
    (x : ℕ → X) (p : X)
    (hx : Tendsto x atTop (𝓝 p))
    (L C : ℝ)
    (hlower : ∀ m : ℕ, L ≤ u (x m))
    (hupper : ∀ m : ℕ, u (x m) ≤ C) :
    Filter.limsup (fun m : ℕ => u (x m)) atTop ≤ u p := by
  have hcob :
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun m : ℕ => u (x m)) :=
    Filter.isCoboundedUnder_le_of_le atTop hlower
  have hbdd :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun m : ℕ => u (x m)) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall hupper)
  apply (Filter.limsup_le_iff hcob hbdd).mpr
  intro b hb
  exact hx (hu p b hb)
theorem limsup_integral_sub_const_le_of_upperSemicontinuous
    {X : Type*} [TopologicalSpace X]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (u : X → ℝ) (hu : UpperSemicontinuous u)
    (γ : ℕ → α → X) (γ₀ : α → X)
    (hγ : ∀ m : ℕ, Continuous (γ m))
    (hγ₀ : Continuous γ₀)
    (htend : ∀ a : α,
      Tendsto (fun m : ℕ => γ m a) atTop (𝓝 (γ₀ a)))
    (L C : ℝ)
    (hbound : ∀ m : ℕ, ∀ a : α,
      L ≤ u (γ m a) ∧ u (γ m a) ≤ C)
    (hbound₀ : ∀ a : α,
      L ≤ u (γ₀ a) ∧ u (γ₀ a) ≤ C) :
    Filter.limsup
        (fun m : ℕ => ∫ a, u (γ m a) - L ∂μ) atTop ≤
      ∫ a, u (γ₀ a) - L ∂μ := by
  have hshift : UpperSemicontinuous (fun z : X => u z - L) := by
    have hconst : UpperSemicontinuous (fun _ : X => -L) :=
      (continuous_const : Continuous (fun _ : X => -L)).upperSemicontinuous
    simpa [sub_eq_add_neg] using
      hu.add hconst
  have hmeas (m : ℕ) :
      Measurable (fun a : α => u (γ m a) - L) := by
    exact (hshift.comp (hγ m)).measurable
  have hgmeas : Measurable (fun a : α => u (γ₀ a) - L) := by
    exact (hshift.comp hγ₀).measurable
  have hgint :
      Integrable (fun a : α => u (γ₀ a) - L) μ := by
    refine (integrable_const (C - L)).mono'
      hgmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hbound₀ a).1)]
      exact sub_le_sub_right (hbound₀ a).2 L
  apply limsup_integral_le_of_nonnegative_bounded μ
    (fun m a => u (γ m a) - L)
    (fun a => u (γ₀ a) - L) (C - L)
    hmeas hgint
  · exact fun m a => sub_nonneg.mpr (hbound m a).1
  · exact fun m a => sub_le_sub_right (hbound m a).2 L
  · exact Filter.Eventually.of_forall fun a =>
      sub_nonneg.mpr (hbound₀ a).1
  · filter_upwards [] with a
    exact limsup_le_of_upperSemicontinuous_of_tendsto
      (fun z : X => u z - L) hshift
      (fun m : ℕ => γ m a) (γ₀ a) (htend a)
      0 (C - L)
      (fun m => sub_nonneg.mpr (hbound m a).1)
      (fun m => sub_le_sub_right (hbound m a).2 L)
end ActualJetPlurisubharmonicClosure
namespace BergmanJetUpperEnvelope
open Set Function Filter MeasureTheory Module
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetGeodesic BergmanJetRealGeodesic ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology
theorem continuous_momentJointJetDiagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ) :
    Continuous (momentJointJetDiagonal
      K hk F htransport p N) := by
  have heq : momentJointJetDiagonal K hk F htransport p N =
      fun q => ‖momentJointJetSectionVector
        K hk F htransport p N q‖ ^ 2 := by
    funext q
    exact (momentJointJetSectionVector_norm_sq
      K hk F htransport p N q).symm
  rw [heq]
  exact (differentiable_momentJointJetSectionVector
    K hk F htransport p N).continuous.norm.pow 2
theorem momentJointJetDiagonal_eq_radial
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ)
    {τ : ℂ} (hτ : τ ≠ 0) :
    momentJointJetDiagonal K hk F htransport p N (z, τ) =
      momentJointJetDiagonal K hk F htransport p N
        (z, (Real.exp (Real.log (Complex.normSq τ) / 2) : ℂ)) := by
  have hsq : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hτ
  have hrad :
      Real.exp (Real.log (Complex.normSq τ) / 2) ^ 2 =
        Complex.normSq τ := by
    rw [pow_two, ← Real.exp_add,
      show Real.log (Complex.normSq τ) / 2 +
          Real.log (Complex.normSq τ) / 2 =
        Real.log (Complex.normSq τ) by ring,
      Real.exp_log hsq]
  unfold momentJointJetDiagonal
  apply Finset.sum_congr rfl
  intro i _
  simp only [momentJointJetSection,
    Complex.normSq_mul, map_pow, Complex.normSq_ofReal]
  rw [← pow_two, hrad]
def momentPositiveJointGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (k : ℕ)
    (q : PositiveJointLogSpace n) : ℝ :=
  Real.log
    (momentJointJetDiagonal K (Nat.zero_lt_succ k)
      F htransport p
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ))) q.val) /
      ((k + 1 : ℕ) : ℝ)
theorem momentPositiveJointGeodesic_eq_momentJetGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (k : ℕ)
    (q : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k q =
      momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) q.val.1
          (jointLogTime q) := by
  have hτ : q.val.2 ≠ 0 :=
    Complex.normSq_pos.mp
      (lt_trans (by norm_num : (0 : ℝ) < 1) q.property)
  unfold momentPositiveJointGeodesic jointLogTime
  rw [momentJointJetDiagonal_eq_radial
    K (Nat.zero_lt_succ k) F htransport p q.val.1
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ))) hτ]
  exact
    (momentJetGeodesic_eq_log_jointJetDiagonal
      K (Nat.zero_lt_succ k) F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) q.val.1
          (Real.log (Complex.normSq q.val.2))).symm
def momentJointMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : PositiveJointLogSpace n) : ℝ :=
  momentNormalizedPotential F (jointRealCoordinate q) +
    BodyScale.canonicalScale K * jointLogTime q
theorem continuous_momentJointMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentJointMajorant K F) := by
  unfold momentJointMajorant
  exact (continuous_momentNormalizedPotential F).comp
      (continuous_jointRealCoordinate n) |>.add
        (continuous_const.mul (continuous_jointLogTime n))
theorem eventually_momentPositiveJointGeodesic_le_majorant_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∀ q : PositiveJointLogSpace n,
        momentPositiveJointGeodesic K F htransport p k q ≤
          momentJointMajorant K F q + ε := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_momentJetGeodesic_le_potential_add_linear
      K F htransport
      (BodyScale.canonicalScale_pos K).le hε)
  filter_upwards [eventually_ge_atTop N] with k hk q
  have h := hN (k + 1) (by omega)
    (Nat.zero_lt_succ k) p q.val.1
    (jointLogTime q) (jointLogTime_pos q).le
  rw [momentPositiveJointGeodesic_eq_momentJetGeodesic]
  simpa [momentJointMajorant, jointRealCoordinate,
    add_assoc, add_left_comm, add_comm] using h
def momentJointTailStart
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) : ℕ :=
  Classical.choose (Filter.eventually_atTop.mp
    (eventually_momentPositiveJointGeodesic_le_majorant_add
      K F htransport p (by norm_num : (0 : ℝ) < 1)))
theorem momentPositiveJointGeodesic_le_majorant_add_one_of_tail
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (k : ℕ) (hk : momentJointTailStart K F htransport p ≤ k)
    (q : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k q ≤
      momentJointMajorant K F q + 1 := by
  exact (Classical.choose_spec (Filter.eventually_atTop.mp
    (eventually_momentPositiveJointGeodesic_le_majorant_add
      K F htransport p (by norm_num : (0 : ℝ) < 1)))) k hk q
def momentJointTailSup
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) : ℝ :=
  sSup (Set.range fun j : ℕ =>
    momentPositiveJointGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r + j) q)
theorem momentJointTailSup_range_bddAbove
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    BddAbove (Set.range fun j : ℕ =>
      momentPositiveJointGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r + j) q) := by
  refine ⟨momentJointMajorant K F q + 1, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact momentPositiveJointGeodesic_le_majorant_add_one_of_tail
    K F htransport p _ (by omega) q
theorem momentJointTailSup_le_majorant_add_one
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    momentJointTailSup K F htransport p r q ≤
      momentJointMajorant K F q + 1 := by
  unfold momentJointTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact momentPositiveJointGeodesic_le_majorant_add_one_of_tail
    K F htransport p _ (by omega) q
def momentJointTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) : PositiveJointLogSpace n → ℝ :=
  upperRegularization (momentJointTailSup K F htransport p r)
theorem momentJointTailSup_localUpperBounds_nonempty
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    (localUpperBounds
      (momentJointTailSup K F htransport p r) q).Nonempty := by
  exact localUpperBounds_nonempty_of_continuous_majorant
    (momentJointTailSup K F htransport p r)
    (fun z => momentJointMajorant K F z + 1)
    ((continuous_momentJointMajorant K F).add continuous_const)
    (momentJointTailSup_le_majorant_add_one
      K F htransport p r) q
theorem upperSemicontinuous_momentJointTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (r : ℕ) :
    UpperSemicontinuous
      (momentJointTailUpperEnvelope
        K F htransport p r) :=
  upperSemicontinuous_upperRegularization
    (momentJointTailSup K F htransport p r)
    (momentJointTailSup_localUpperBounds_nonempty
      K F htransport p r)
end BergmanJetUpperEnvelope
namespace BergmanJetEnvelopePlurisubharmonic
open Set Function Filter MeasureTheory Module
open SupportFunction MonomialIntegrability BergmanMonomials LatticeAsymptotics MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetBasis
open BergmanJetGeodesic BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanGeodesicConvexity
open BergmanDiagonalBasisIndependence ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology
theorem momentZeroMonomialNorm_le_partition
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    monomialNormSquared k (0 : Space n)
        (momentNormalizedPotential F) ≤
      Real.exp
        (-(k : ℝ) * Real.log
          (finiteEnergySourcePartition F /
            normalizedVolume K.carrier)) *
        finiteEnergySourcePartition F := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hrawint :=
    integrable_monomialWeight_finiteEnergySource_of_mem_interior
      F htransport (LatticeAsymptotics.zero_mem_interior K)
      hkreal
  have hraw :
      monomialIntegral (k : ℝ) (0 : Space n) F.potential ≤
        finiteEnergySourcePartition F := by
    unfold monomialIntegral finiteEnergySourcePartition
    apply MeasureTheory.integral_mono hrawint F.densityIntegrable
    intro x
    unfold monomialWeight pairing
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_sub]
    apply Real.exp_le_exp.mpr
    nlinarith [F.nonnegative x]
  have hshift :
      monomialNormSquared k (0 : Space n)
          (momentNormalizedPotential F) =
        Real.exp
          (-(k : ℝ) * Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) *
          monomialIntegral (k : ℝ) (0 : Space n)
            F.potential := by
    unfold monomialNormSquared monomialIntegral
    rw [show
      (fun x : Space n =>
        monomialWeight (k : ℝ) (0 : Space n)
          (momentNormalizedPotential F) x) =
      (fun x : Space n =>
        Real.exp
          (-(k : ℝ) * Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) *
        monomialWeight (k : ℝ) (0 : Space n)
          F.potential x) by
        funext x
        exact monomialWeight_momentNormalizedPotential_eq
          F (k : ℝ) (0 : Space n) x]
    exact MeasureTheory.integral_const_mul _ _
  rw [hshift]
  exact mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le
def momentJointGlobalLowerBound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) : ℝ :=
  Real.log
    (finiteEnergySourcePartition F /
      normalizedVolume K.carrier) -
    |Real.log (finiteEnergySourcePartition F)|
theorem momentJointGlobalLowerBound_le_zeroMonomial
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    momentJointGlobalLowerBound K F ≤
      -(Real.log
        (monomialNormSquared k (0 : Space n)
          (momentNormalizedPotential F))) / (k : ℝ) := by
  let u₀ : monomialIndex K k :=
    ⟨0, zero_mem_monomialIndex K hk⟩
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hZ := finiteEnergySourcePartition_pos F
  have hnorm : 0 < monomialNormSquared k (0 : Space n)
      (momentNormalizedPotential F) := by
    simpa [u₀] using
      (momentMonomialNormSquared_pos K hk F htransport u₀)
  have hbound := momentZeroMonomialNorm_le_partition
    K hk F htransport
  have hlog := Real.log_le_log hnorm hbound
  rw [Real.log_mul (Real.exp_ne_zero _) hZ.ne',
    Real.log_exp] at hlog
  have habs :
      Real.log (finiteEnergySourcePartition F) ≤
        (k : ℝ) * |Real.log (finiteEnergySourcePartition F)| := by
    calc
      Real.log (finiteEnergySourcePartition F) ≤
        |Real.log (finiteEnergySourcePartition F)| := le_abs_self _
      _ ≤ (k : ℝ) * |Real.log (finiteEnergySourcePartition F)| := by
        nlinarith [abs_nonneg
          (Real.log (finiteEnergySourcePartition F))]
  unfold momentJointGlobalLowerBound
  apply (le_div_iff₀ hkreal).mpr
  nlinarith
theorem inv_momentZeroMonomialNorm_le_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    (monomialNormSquared k (0 : Space n)
      (momentNormalizedPotential F))⁻¹ ≤
      diagonalKernel K k (momentNormalizedPotential F) x := by
  classical
  let := (monomialIndex_finite K hk).fintype
  let u₀ : monomialIndex K k :=
    ⟨0, zero_mem_monomialIndex K hk⟩
  have hterm :
      (monomialNormSquared k (0 : Space n)
        (momentNormalizedPotential F))⁻¹ =
        diagonalTerm K k (momentNormalizedPotential F) u₀ x := by
    simp [diagonalTerm, pairing, u₀]
  rw [hterm]
  unfold diagonalKernel
  rw [tsum_fintype]
  have hnonneg :
      ∀ u ∈ (Finset.univ : Finset (monomialIndex K k)),
        0 ≤ diagonalTerm K k
          (momentNormalizedPotential F) u x := by
    intro u _
    unfold diagonalTerm
    exact div_nonneg (Real.exp_pos _).le
      (momentMonomialNormSquared_pos
        K hk F htransport u).le
  exact Finset.single_le_sum hnonneg (Finset.mem_univ u₀)
theorem momentJointGlobalLowerBound_le_log_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    momentJointGlobalLowerBound K F ≤
      Real.log (diagonalKernel K k
        (momentNormalizedPotential F) x) / (k : ℝ) := by
  let u₀ : monomialIndex K k :=
    ⟨0, zero_mem_monomialIndex K hk⟩
  have hnorm : 0 < monomialNormSquared k (0 : Space n)
      (momentNormalizedPotential F) := by
    simpa [u₀] using
      (momentMonomialNormSquared_pos K hk F htransport u₀)
  have hbound := inv_momentZeroMonomialNorm_le_diagonalKernel
    K hk F htransport x
  have hlog := Real.log_le_log (inv_pos.mpr hnorm) hbound
  rw [Real.log_inv] at hlog
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  calc
    momentJointGlobalLowerBound K F ≤
      -(Real.log
        (monomialNormSquared k (0 : Space n)
          (momentNormalizedPotential F))) / (k : ℝ) :=
      momentJointGlobalLowerBound_le_zeroMonomial
        K hk F htransport
    _ ≤ Real.log (diagonalKernel K k
        (momentNormalizedPotential F) x) / (k : ℝ) :=
      (div_le_div_iff_of_pos_right hkreal).mpr hlog
theorem monotone_momentJetGeodesic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ) :
    Monotone (momentJetGeodesic
      K hk F htransport p N z) := by
  apply monotone_of_deriv_nonneg
  · intro t
    unfold momentJetGeodesic
    exact (hasDerivAt_logarithmicPotential
      (momentHolomorphicBasisWeight
        K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (momentTruncatedJetOrder K hk F htransport p N)
      (momentHolomorphicBasisWeight_nonneg
        K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (exists_positive_momentHolomorphicBasisWeight
        K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (k : ℝ) t).differentiableAt
  · exact momentJetGeodesic_deriv_nonneg
      K hk F htransport p N z
theorem momentJointGlobalLowerBound_le_positiveJointGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (k : ℕ) (q : PositiveJointLogSpace n) :
    momentJointGlobalLowerBound K F ≤
      momentPositiveJointGeodesic
        K F htransport p k q := by
  let hk : 0 < k + 1 := Nat.zero_lt_succ k
  let N := Nat.floor (BodyScale.canonicalScale K *
    ((k + 1 : ℕ) : ℝ))
  calc
    momentJointGlobalLowerBound K F ≤
      Real.log
        (diagonalKernel K (k + 1)
          (momentNormalizedPotential F)
          (realLogCoordinate q.val.1)) /
            ((k + 1 : ℕ) : ℝ) :=
      momentJointGlobalLowerBound_le_log_diagonalKernel
        K hk F htransport (realLogCoordinate q.val.1)
    _ = momentJetGeodesic
      K hk F htransport p N q.val.1 0 :=
      (momentJetGeodesic_zero_eq_log_diagonalKernel
        K hk F htransport p q.val.1 N).symm
    _ ≤ momentJetGeodesic
      K hk F htransport p N q.val.1 (jointLogTime q) :=
      monotone_momentJetGeodesic
        K hk F htransport p q.val.1 N (jointLogTime_pos q).le
    _ = momentPositiveJointGeodesic
      K F htransport p k q :=
      (momentPositiveJointGeodesic_eq_momentJetGeodesic
        K F htransport p k q).symm
theorem momentJointGlobalLowerBound_le_tailSup
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    momentJointGlobalLowerBound K F ≤
      momentJointTailSup K F htransport p r q := by
  calc
    momentJointGlobalLowerBound K F ≤
      momentPositiveJointGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r) q :=
      momentJointGlobalLowerBound_le_positiveJointGeodesic
        K F htransport p
        (momentJointTailStart K F htransport p + r) q
    _ ≤ momentJointTailSup K F htransport p r q := by
      unfold momentJointTailSup
      apply le_csSup
        (momentJointTailSup_range_bddAbove
          K F htransport p r q)
      exact ⟨0, by simp⟩
theorem momentJointGlobalLowerBound_le_tailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    momentJointGlobalLowerBound K F ≤
      momentJointTailUpperEnvelope
        K F htransport p r q := by
  calc
    momentJointGlobalLowerBound K F ≤
      momentJointTailSup K F htransport p r q :=
      momentJointGlobalLowerBound_le_tailSup
        K F htransport p r q
    _ ≤ momentJointTailUpperEnvelope
      K F htransport p r q :=
      le_upperRegularization
        (momentJointTailSup K F htransport p r) q
        (momentJointTailSup_localUpperBounds_nonempty
          K F htransport p r q)
end BergmanJetEnvelopePlurisubharmonic
namespace BergmanJetEnvelopeLimit
open Set Function Filter MeasureTheory Module
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopePlurisubharmonic ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology
theorem momentJointTailUpperEnvelope_bddBelow
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) :
    BddBelow (Set.range fun r : ℕ =>
      momentJointTailUpperEnvelope
        K F htransport p r q) := by
  refine ⟨momentJointGlobalLowerBound K F, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact momentJointGlobalLowerBound_le_tailUpperEnvelope
    K F htransport p r q
def momentJointUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) : ℝ :=
  ⨅ r : ℕ, momentJointTailUpperEnvelope
    K F htransport p r q
theorem upperSemicontinuous_momentJointUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) :
    UpperSemicontinuous
      (momentJointUpperEnvelope K F htransport p) :=
  upperSemicontinuous_ciInf
    (momentJointTailUpperEnvelope_bddBelow
      K F htransport p)
    (upperSemicontinuous_momentJointTailUpperEnvelope
      K F htransport p)
end BergmanJetEnvelopeLimit
namespace LogPartitionConvexity
open Set Filter MeasureTheory Metric
open JetEnvelopeSlopeConvergence
open scoped ENNReal Topology
theorem sourceTorusBaseMeasure_neZero (n : ℕ) :
    NeZero (sourceTorusBaseMeasure n) := by
  refine ⟨?_⟩
  intro hzero
  have hmap := congrArg
    (Measure.map (Prod.fst :
      WeightedTorusHilbert.LogTorus n → Space n)) hzero
  have hvol : (volume : Measure (Space n)) = 0 := by
    simpa [sourceTorusBaseMeasure] using hmap
  exact (NeZero.ne (volume : Measure (Space n))) hvol
def sourceTimeDensity {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  Real.exp (-a t q)
def sourcePartition {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    sourceTimeDensity a t q ∂(sourceTorusBaseMeasure n)
def sourceLogPartition {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  -Real.log (sourcePartition a t)
def sourceFirstMoment {n : ℕ}
    (a f : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    f t q * sourceTimeDensity a t q ∂(sourceTorusBaseMeasure n)
def sourceSecondMoment {n : ℕ}
    (a f : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    f t q ^ 2 * sourceTimeDensity a t q ∂(sourceTorusBaseMeasure n)
def sourceAccelerationMoment {n : ℕ}
    (a j : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    j t q * sourceTimeDensity a t q ∂(sourceTorusBaseMeasure n)
def sourceLogSlope {n : ℕ}
    (a f : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  sourceFirstMoment a f t / sourcePartition a t
def sourceMomentVariance {n : ℕ}
    (a f : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  sourceSecondMoment a f t / sourcePartition a t -
    (sourceLogSlope a f t) ^ 2
def sourceNormalizedDensity {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  sourceTimeDensity a t q / sourcePartition a t
def sourceProbability {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : Measure (WeightedTorusHilbert.LogTorus n) :=
  (sourceTorusBaseMeasure n).withDensity
    (fun q => ENNReal.ofReal (sourceNormalizedDensity a t q))
def sourceProbabilityMean {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) (F : WeightedTorusHilbert.LogTorus n → ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    F q ∂(sourceProbability a t)
def sourceProbabilityVariance {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) (F : WeightedTorusHilbert.LogTorus n → ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    (F q - sourceProbabilityMean a t F) ^ 2
      ∂(sourceProbability a t)
end LogPartitionConvexity
namespace WeightedBrascampLieb
open Set MeasureTheory Matrix Filter
open WeightedPoincare
open scoped BigOperators ENNReal InnerProductSpace
abbrev scalarL2 {n : ℕ} (a : Space n → ℝ) :=
  MeasureTheory.Lp ℝ 2 (normalizedMeasure a)
def euclideanGradient {n : ℕ}
    (f : Space n → ℝ) (x : Space n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (coordinateGradient f x)
theorem continuous_euclideanGradient {n : ℕ}
    {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (euclideanGradient f) := by
  unfold euclideanGradient
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  exact continuous_pi (fun i =>
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const)
end WeightedBrascampLieb
namespace WeightedResolventConstantCore
open Set Function MeasureTheory Filter Matrix
open WeightedPoincare WeightedBrascampLieb
open scoped BigOperators ENNReal InnerProductSpace Topology
def growingBump {n : ℕ} (k : ℕ) : ContDiffBump (0 : Space n) where
  rIn := (k : ℝ) + 1
  rOut := 2 * ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
def unitBump {n : ℕ} : ContDiffBump (0 : Space n) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num
theorem growingBump_apply_eq_unit {n : ℕ} (k : ℕ) (x : Space n) :
    growingBump (n := n) k x = unitBump (n := n) (((k : ℝ) + 1)⁻¹ • x) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp [ContDiffBump.apply, growingBump, unitBump, hk]
theorem growingBump_fderiv {n : ℕ} (k : ℕ) (x : Space n) :
    fderiv ℝ (fun y : Space n => growingBump k y) x =
      ((k : ℝ) + 1)⁻¹ •
        fderiv ℝ (fun y : Space n => unitBump y)
          (((k : ℝ) + 1)⁻¹ • x) := by
  have hfun :
      (fun y : Space n => growingBump k y) =
        (fun y : Space n =>
          unitBump (((k : ℝ) + 1)⁻¹ • y)) :=
    funext (growingBump_apply_eq_unit k)
  rw [hfun, fderiv_comp_smul]
theorem unitBump_euclideanGradient_hasCompactSupport {n : ℕ} :
    HasCompactSupport
      (euclideanGradient (fun x : Space n => unitBump x)) := by
  refine ((unitBump (n := n)).hasCompactSupport.fderiv ℝ).mono ?_
  intro x
  exact mt (fun hx => by
    ext i
    simp [euclideanGradient, coordinateGradient, hx])
theorem unitBump_euclideanGradient_bound {n : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Space n,
        ‖euclideanGradient (fun y : Space n => unitBump y) x‖ ≤ C := by
  have hsmooth :
      ContDiff ℝ 1 (fun x : Space n => unitBump x) :=
    (unitBump (n := n)).contDiff
  obtain ⟨C, hC⟩ :=
    (continuous_euclideanGradient hsmooth).bounded_above_of_compact_support
      (unitBump_euclideanGradient_hasCompactSupport (n := n))
  exact ⟨max C 0, le_max_right C 0,
    fun x => (hC x).trans (le_max_left C 0)⟩
theorem growingBump_euclideanGradient {n : ℕ}
    (k : ℕ) (x : Space n) :
    euclideanGradient (fun y : Space n => growingBump k y) x =
      ((k : ℝ) + 1)⁻¹ •
        euclideanGradient (fun y : Space n => unitBump y)
          (((k : ℝ) + 1)⁻¹ • x) := by
  ext i
  change
    (fderiv ℝ (fun y : Space n => growingBump k y) x)
        (Pi.single i (1 : ℝ)) =
      ((k : ℝ) + 1)⁻¹ *
        (fderiv ℝ (fun y : Space n => unitBump y)
          (((k : ℝ) + 1)⁻¹ • x)) (Pi.single i (1 : ℝ))
  rw [growingBump_fderiv]
  rfl
theorem growingBump_euclideanGradient_norm_le {n : ℕ}
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y : Space n => unitBump y) x‖ ≤ C)
    (k : ℕ) (x : Space n) :
    ‖euclideanGradient (fun y : Space n => growingBump k y) x‖ ≤
      ((k : ℝ) + 1)⁻¹ * C := by
  rw [growingBump_euclideanGradient, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((k : ℝ) + 1)⁻¹)]
  exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
end WeightedResolventConstantCore
namespace WeightedBrascampSaturation
open Set Function MeasureTheory Filter Matrix
open scoped BigOperators ENNReal InnerProductSpace Topology
abbrev weightedTorusFormL2 {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :=
  MeasureTheory.Lp (EuclideanSpace ℂ (Fin n)) 2
    (WeightedTorusHilbert.weightedTorusMeasure k φ)
end WeightedBrascampSaturation
namespace HolomorphicLaurentFourierCompletenessBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
local instance _p2m_local_instance_3610026555_13449 : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance _p2m_local_instance_3610026555_13452 : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def logarithmicPeriod : ℂ := 2 * (Real.pi : ℂ) * Complex.I
def angularFourierCoefficient {n k : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) (x : Space n) : ℂ :=
  UnitAddTorus.mFourierCoeff
    (fun θ : TorusCharacters.AngularTorus n =>
      f (x, θ)) m
def coordinateHolomorphicSlice {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (ζ : TorusCharacters.LogSpace n)
    (i : Fin n) : ℂ → ℂ :=
  fun w => F (fun j => if j = i then w else ζ j)
end HolomorphicLaurentFourierCompletenessBridge
namespace JointHolomorphicLaurentFourierCompatibility
open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace
local instance _p2m_local_instance_3610026555_13915 : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance _p2m_local_instance_3610026555_13918 : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def angularBox (n : ℕ) : Set (Space n) :=
  Set.univ.pi fun _ : Fin n => Set.Ioc (0 : ℝ) 1
def angularBoxMeasure (n : ℕ) : Measure (Space n) :=
  Measure.pi fun _ : Fin n =>
    (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
def logarithmicPoint {n : ℕ}
    (x t : Space n) : TorusCharacters.LogSpace n :=
  fun i => (x i : ℂ) / 2 +
    (2 * (Real.pi : ℂ) * Complex.I) * (t i : ℂ)
def coverRepresentative {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (x : Space n)
    (θ : TorusCharacters.AngularTorus n) : ℂ :=
  F (fun i => (x i : ℂ) / 2 +
    (2 * (Real.pi : ℂ) * Complex.I) *
      ((AddCircle.equivIoc 1 0 (θ i)).1 : ℂ))
def globalLaurentTwist {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) :
    TorusCharacters.LogSpace n → ℂ :=
  fun ζ => Complex.exp
      (-(TorusCharacters.characterExponent m ζ)) * F ζ
def twistedAngularIntegrand {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) (x : Space n) :
    Space n → ℂ :=
  fun t => globalLaurentTwist F m (logarithmicPoint x t)
def twistedAngularAverage {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) (x : Space n) : ℂ :=
  ∫ t : Space n,
    twistedAngularIntegrand F m x t ∂(angularBoxMeasure n)
theorem mFourier_neg_coe_eq_exp {n : ℕ}
    (m : Fin n → ℤ) (t : Space n) :
    UnitAddTorus.mFourier (-m)
        (fun i => (t i : UnitAddCircle)) =
      Complex.exp
        (-(TorusCharacters.characterExponent m
          (logarithmicPoint 0 t))) := by
  unfold UnitAddTorus.mFourier
    TorusCharacters.characterExponent
    logarithmicPoint
  simp only [ContinuousMap.coe_mk, Pi.neg_apply,
    Pi.zero_apply, Complex.ofReal_zero, zero_div, zero_add]
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring
theorem logarithmicPoint_eq_add {n : ℕ}
    (x t : Space n) :
    logarithmicPoint x t =
      TorusCharacters.realLogSlice x +
        logarithmicPoint 0 t := by
  funext i
  simp [logarithmicPoint,
    TorusCharacters.realLogSlice]
theorem characterExponent_logarithmicPoint {n : ℕ}
    (m : Fin n → ℤ) (x t : Space n) :
    TorusCharacters.characterExponent m
        (logarithmicPoint x t) =
      TorusCharacters.characterExponent m
        (TorusCharacters.realLogSlice x) +
      TorusCharacters.characterExponent m
        (logarithmicPoint 0 t) := by
  rw [logarithmicPoint_eq_add,
    TorusCharacters.characterExponent_add]
def scaledExponent {n : ℕ}
    (k : ℕ) (m : Fin n → ℤ) : Space n :=
  (k : ℝ)⁻¹ • integerPoint n m
def laurentCoefficient {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (coverRepresentative F 0) m
end JointHolomorphicLaurentFourierCompatibility
namespace EqualitySaturatingKillingPaths
open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology
def barPartialCoordinate {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (z : TorusCharacters.LogSpace n) (j : Fin n) : ℂ :=
  ((fderiv ℝ F z) (Pi.single j (1 : ℂ)) +
    Complex.I * (fderiv ℝ F z) (Pi.single j Complex.I)) / 2
def torusFormRepresentative {n : ℕ}
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (z : WeightedTorusHilbert.LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i =>
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
      (fun ζ => W ζ i) z.1 z.2
end EqualitySaturatingKillingPaths
namespace DolbeaultRegularity
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
def complexContinuousOfCoordinateCR {n : ℕ}
    (D : TorusCharacters.LogSpace n →L[ℝ] ℂ)
    (hI : ∀ j : Fin n,
      D (Pi.single j Complex.I) =
        Complex.I • D (Pi.single j (1 : ℂ))) :
    TorusCharacters.LogSpace n →L[ℂ] ℂ where
  __ := D
  map_smul' := by
    intro a x
    have hcoord (i : Fin n) (b d : ℂ) :
        D (Pi.single i (b • d)) =
          b • D (Pi.single i d) := by
      let L : ℂ →L[ℝ] ℂ := D.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i)
      have hL : L Complex.I = Complex.I • L 1 := by
        simpa [L, ContinuousLinearMap.comp_apply] using hI i
      have h := real_linearMap_map_smul_complex
        (ℓ := L.toLinearMap) hL b d
      simpa [L, ContinuousLinearMap.comp_apply] using h
    calc
      D (a • x) = ∑ i : Fin n,
          D (Pi.single i ((a • x) i)) := by
            simpa only [map_sum] using
              (congrArg D (Finset.univ_sum_single (a • x))).symm
      _ = ∑ i : Fin n, D (Pi.single i (a • x i)) := by rfl
      _ = ∑ i : Fin n, a • D (Pi.single i (x i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hcoord i a (x i)
      _ = a • ∑ i : Fin n, D (Pi.single i (x i)) :=
            Finset.smul_sum.symm
      _ = a • D x := by
            rw [← map_sum, Finset.univ_sum_single]
def complexRealMultiplication : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip
def complexShrinkingBump {n : ℕ} (k : ℕ) :
    ContDiffBump (0 : TorusCharacters.LogSpace n) where
  rIn := (1 / ((k : ℝ) + 1)) / 2
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact half_lt_self h
theorem complex_convolution_flip {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ)
    (κ : TorusCharacters.LogSpace n → ℝ) :
    (g ⋆[complexRealMultiplication,
      (volume : Measure (TorusCharacters.LogSpace n))] κ) =
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g) := by
  exact MeasureTheory.convolution_flip
    (μ := (volume : Measure (TorusCharacters.LogSpace n)))
    (f := κ) (g := g) (ContinuousLinearMap.lsmul ℝ ℝ)
end DolbeaultRegularity
namespace ComplexKillingSaturationBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths WeightedBrascampSaturation
open scoped BigOperators ENNReal InnerProductSpace Topology
def torusScalarRepresentative {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (z : WeightedTorusHilbert.LogTorus n) : ℂ :=
  JointHolomorphicLaurentFourierCompatibility.coverRepresentative
    F z.1 z.2
def torusFunctionBarPartialRepresentative {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (z : WeightedTorusHilbert.LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j =>
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
      (fun ζ => barPartialCoordinate F ζ j) z.1 z.2
abbrev weightedTorusScalarL2 {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :=
  WeightedTorusHilbert.weightedHilbert k φ
abbrev functionDolbeaultGraphAmbient {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :=
  WithLp 2
    (weightedTorusScalarL2 k φ × weightedTorusFormL2 k φ)
def torusScalarL2OfRepresentative {n k : ℕ}
    (φ : Space n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hF : MemLp (torusScalarRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ)) :
    weightedTorusScalarL2 k φ :=
  hF.toLp (torusScalarRepresentative F)
def torusFunctionBarPartialL2 {n k : ℕ}
    (φ : Space n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hF : MemLp (torusFunctionBarPartialRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ)) :
    weightedTorusFormL2 k φ :=
  hF.toLp (torusFunctionBarPartialRepresentative F)
def smoothFunctionDolbeaultGraphSet {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :
    Set (functionDolbeaultGraphAmbient k φ) :=
  {v | ∃ F : TorusCharacters.LogSpace n → ℂ,
    ContDiff ℝ 3 F ∧
    (∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q)) ∧
    HasCompactSupport (torusScalarRepresentative F) ∧
    ∃ hF : MemLp (torusScalarRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ),
    ∃ hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ),
      v = WithLp.toLp 2
        (torusScalarL2OfRepresentative φ F hF,
         torusFunctionBarPartialL2 φ F hD)}
def functionDolbeaultGraph {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :
    Submodule ℂ (functionDolbeaultGraphAmbient k φ) :=
  (Submodule.span ℂ
    (smoothFunctionDolbeaultGraphSet k φ)).topologicalClosure
end ComplexKillingSaturationBridge
namespace DolbeaultGraphDistributionBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths DolbeaultRegularity
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
theorem compactSupport_complexOfReal {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : HasCompactSupport ψ) :
    HasCompactSupport
      (fun z : TorusCharacters.LogSpace n => (ψ z : ℂ)) := by
  refine hψ.mono ?_
  intro z hz
  exact Complex.ofReal_ne_zero.mp hz
theorem fderiv_complexOfReal {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun w : TorusCharacters.LogSpace n => (ψ w : ℂ)) z) v =
      ((fderiv ℝ ψ z) v : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp z
    (hψ z).hasFDerivAt).fderiv
  exact congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℂ => D v) h
def coverBarPartialTest {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (z : TorusCharacters.LogSpace n) : ℂ :=
  ((fderiv ℝ ψ z) (Pi.single j (1 : ℂ)) : ℂ) +
    Complex.I *
      ((fderiv ℝ ψ z) (Pi.single j Complex.I) : ℂ)
theorem complexReal_convolution_periodic {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (κ : TorusCharacters.LogSpace n → ℝ)
    {d : TorusCharacters.LogSpace n}
    (hperiod : Function.Periodic g d) :
    Function.Periodic
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) d := by
  intro x
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  let H : TorusCharacters.LogSpace n → ℂ :=
    fun t => complexRealMultiplication (g t) (κ (x - t))
  calc
    (∫ t : TorusCharacters.LogSpace n,
      complexRealMultiplication (g t) (κ (x + d - t))
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
      ∫ t : TorusCharacters.LogSpace n,
        H (t - d)
        ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
          congr 1
          funext t
          dsimp [H]
          rw [show g (t - d) = g t by
            have hp := hperiod (t - d)
            simpa using hp.symm]
          congr 2
          abel
    _ = ∫ t : TorusCharacters.LogSpace n,
      H t ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
      simpa [sub_eq_add_neg] using
        (integral_add_right_eq_self H (-d))
    _ = _ := rfl
theorem normalizedShrinkingConvolution_periodic {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic g (TorusCharacters.imaginaryShift q))
    (k : ℕ) (q : Fin n → ℤ) :
    Function.Periodic
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (TorusCharacters.LogSpace n))
       ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
         (volume : Measure (TorusCharacters.LogSpace n))] g)
      (TorusCharacters.imaginaryShift q) := by
  rw [← complex_convolution_flip]
  exact complexReal_convolution_periodic
    ((complexShrinkingBump (n := n) k).normed
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hperiod q)
abbrev coverScalarL2 (n : ℕ) :=
  MeasureTheory.Lp ℂ 2
    (volume : Measure (TorusCharacters.LogSpace n))
def coverAdjointScalarTest {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (z : TorusCharacters.LogSpace n) : ℂ :=
  star (coverBarPartialTest ψ j z)
def coverAdjointVectorTest {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (z : TorusCharacters.LogSpace n) :
    EuclideanSpace ℂ (Fin n) :=
  EuclideanSpace.single j ((2 : ℂ) * (ψ z : ℂ))
theorem continuous_coverBarPartialTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (j : Fin n) :
    Continuous (coverBarPartialTest ψ j) := by
  unfold coverBarPartialTest
  exact
    (Complex.continuous_ofReal.comp
      ((hψ.continuous_fderiv (by simp)).clm_apply
        continuous_const)).add
      (continuous_const.mul
        (Complex.continuous_ofReal.comp
          ((hψ.continuous_fderiv (by simp)).clm_apply
            continuous_const)))
theorem compactSupport_coverBarPartialTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (coverBarPartialTest ψ j) := by
  unfold coverBarPartialTest
  exact
    (compactSupport_complexOfReal
      (hψ.fderiv_apply ℝ (Pi.single j (1 : ℂ)))).add
      (compactSupport_complexOfReal
        (hψ.fderiv_apply ℝ (Pi.single j Complex.I))).mul_left
theorem continuous_coverAdjointScalarTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (j : Fin n) :
    Continuous (coverAdjointScalarTest ψ j) := by
  change Continuous
    (fun z => (starRingEnd ℂ) (coverBarPartialTest ψ j z))
  exact Complex.continuous_conj.comp
    (continuous_coverBarPartialTest hψ j)
theorem compactSupport_coverAdjointScalarTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (coverAdjointScalarTest ψ j) := by
  refine (compactSupport_coverBarPartialTest hψ j).mono ?_
  intro z hz
  exact mt (fun h => by simp [coverAdjointScalarTest, h]) hz
theorem continuous_coverAdjointVectorTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : Continuous ψ) (j : Fin n) :
    Continuous (coverAdjointVectorTest ψ j) := by
  classical
  have hs : Continuous
      (fun z : TorusCharacters.LogSpace n =>
        (2 : ℂ) * (ψ z : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp hψ)
  have hpi : Continuous
      (fun z : TorusCharacters.LogSpace n =>
        (Pi.single j ((2 : ℂ) * (ψ z : ℂ)) : Fin n → ℂ)) := by
    apply continuous_pi
    intro i
    by_cases hi : i = j
    · subst i
      simpa using hs
    · simpa [Pi.single_apply, hi] using
        (continuous_const :
          Continuous
            (fun _ : TorusCharacters.LogSpace n => (0 : ℂ)))
  change Continuous
    (fun z : TorusCharacters.LogSpace n =>
      WithLp.toLp 2
        (Pi.single j ((2 : ℂ) * (ψ z : ℂ)) : Fin n → ℂ))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp hpi
end DolbeaultGraphDistributionBridge
namespace WeightedDolbeaultBochnerIdentity
open Set MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal ComplexConjugate
def coverWeight {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (z : TorusCharacters.LogSpace n) : ℝ :=
  Real.exp (-a z)
def coverWeightedMeasure {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ) :
    Measure (TorusCharacters.LogSpace n) :=
  (volume : Measure (TorusCharacters.LogSpace n)).withDensity
    (fun z => ENNReal.ofReal (coverWeight a z))
def complexCoverWeight {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  (coverWeight a z : ℂ)
def holomorphicCoordinate {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) : ℂ :=
  ((fderiv ℝ F z) (Pi.single j (1 : ℂ)) -
    Complex.I * (fderiv ℝ F z) (Pi.single j Complex.I)) / 2
def weightedRealDerivative {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (v : TorusCharacters.LogSpace n)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  (fderiv ℝ F z) v - F z * ((fderiv ℝ a z) v : ℂ)
def weightedHolomorphicDerivative {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  holomorphicCoordinate F z j -
    F z * holomorphicCoordinate (fun w => (a w : ℂ)) z j
def weightedAntiholomorphicDerivative {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  barPartialCoordinate F z j -
    F z * barPartialCoordinate (fun w => (a w : ℂ)) z j
def complexHessian {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) : ℂ :=
  barPartialCoordinate
    (fun w => holomorphicCoordinate (fun ξ => (a ξ : ℂ)) w i) z j
theorem contDiff_directional {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (v : TorusCharacters.LogSpace n) :
    ContDiff ℝ 1
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v) := by
  have hd : ContDiff ℝ 1
      (fun p : TorusCharacters.LogSpace n ×
          TorusCharacters.LogSpace n =>
        (fderiv ℝ F p.1) p.2) :=
    hF.contDiff_fderiv_apply (by norm_num)
  have hp : ContDiff ℝ 1
      (fun z : TorusCharacters.LogSpace n => (z, v)) :=
    contDiff_id.prodMk contDiff_const
  exact hd.comp hp
theorem contDiff_holomorphicCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (j : Fin n) :
    ContDiff ℝ 1 (fun z => holomorphicCoordinate F z j) := by
  unfold holomorphicCoordinate
  exact ((contDiff_directional hF (Pi.single j (1 : ℂ))).sub
    (contDiff_const.mul
      (contDiff_directional hF (Pi.single j Complex.I)))).div_const 2
theorem barPartial_sub {n : ℕ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate (fun w => F w - G w) z j =
      barPartialCoordinate F z j -
        barPartialCoordinate G z j := by
  have hp := fderiv_sub
    (hF.differentiable (by simp) z)
    (hG.differentiable (by simp) z)
  unfold barPartialCoordinate
  change
    ((fderiv ℝ (F - G) z) (Pi.single j (1 : ℂ)) +
      Complex.I *
        (fderiv ℝ (F - G) z) (Pi.single j Complex.I)) / 2 = _
  rw [hp]
  simp only [_root_.sub_apply]
  ring
theorem continuous_barPartialCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 1 F)
    (j : Fin n) :
    Continuous (fun z => barPartialCoordinate F z j) := by
  unfold barPartialCoordinate
  exact (((hF.continuous_fderiv (by simp)).clm_apply
    continuous_const).add
    (continuous_const.mul
      ((hF.continuous_fderiv (by simp)).clm_apply
        continuous_const))).div_const 2
theorem continuous_holomorphicCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 1 F)
    (j : Fin n) :
    Continuous (fun z => holomorphicCoordinate F z j) := by
  unfold holomorphicCoordinate
  exact (((hF.continuous_fderiv (by simp)).clm_apply
    continuous_const).sub
    (continuous_const.mul
      ((hF.continuous_fderiv (by simp)).clm_apply
        continuous_const))).div_const 2
theorem continuous_weightedHolomorphicDerivative {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (j : Fin n) :
    Continuous (weightedHolomorphicDerivative a F j) := by
  have hac : ContDiff ℝ 1 (fun z => (a z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  unfold weightedHolomorphicDerivative
  exact (continuous_holomorphicCoordinate hF j).sub
    (hF.continuous.mul (continuous_holomorphicCoordinate hac j))
theorem continuous_complexHessian {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (i j : Fin n) :
    Continuous (fun z => complexHessian a z i j) := by
  have hac : ContDiff ℝ 2 (fun z => (a z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  exact continuous_barPartialCoordinate
    (contDiff_holomorphicCoordinate hac i) j
def coverFormAdjoint {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  ∑ i : Fin n,
    weightedHolomorphicDerivative a (fun w => W w i) i z
end WeightedDolbeaultBochnerIdentity
namespace SchurConvexity
open Set Matrix
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder
def complexSchurColumn {n : ℕ} (b : Fin n → ℂ) :
    Matrix (Fin n) (Fin 1) ℂ :=
  fun i _ => b i
def complexSchurScalar (c : ℝ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => (c : ℂ)
theorem complexSchurColumn_mul_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) :
    ((complexSchurColumn b)ᴴ * A * complexSchurColumn b)
      (0 : Fin 1) (0 : Fin 1) =
      star b ⬝ᵥ (A *ᵥ b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    complexSchurColumn, Matrix.mulVec, dotProduct,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
def complexSchurEnergyDensity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) : ℝ :=
  (star b ⬝ᵥ (A⁻¹ *ᵥ b)).re
theorem complex_schur_energy_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ) (c : ℝ)
    (hblock :
      (Matrix.fromBlocks A (complexSchurColumn b)
        (complexSchurColumn b)ᴴ
        (complexSchurScalar c)).PosSemidef) :
    complexSchurEnergyDensity A b ≤ c := by
  let : Invertible A := hA.isUnit.invertible
  have hschur :=
    (Matrix.PosDef.fromBlocks₁₁
      (complexSchurColumn b) (complexSchurScalar c) hA).mp hblock
  have hdiag := hschur.diag_nonneg (i := (0 : Fin 1))
  have hreal := (Complex.nonneg_iff.mp hdiag).1
  change
    0 ≤ (c : ℂ).re -
      (((complexSchurColumn b)ᴴ * A⁻¹ * complexSchurColumn b)
        (0 : Fin 1) (0 : Fin 1)).re at hreal
  rw [complexSchurColumn_mul_apply] at hreal
  change 0 ≤ c - complexSchurEnergyDensity A b at hreal
  linarith
def sourceCoverComplexHessian {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (z : TorusCharacters.LogSpace n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => complexHessian a z i j
def sourceCoverAntiholomorphicGradient {n : ℕ}
    (f : TorusCharacters.LogSpace n → ℂ)
    (z : TorusCharacters.LogSpace n) : Fin n → ℂ :=
  fun i => EqualitySaturatingKillingPaths.barPartialCoordinate
    f z i
end SchurConvexity
namespace JetEnvelopeRightDerivative
open Set Filter MeasureTheory Module
open scoped BigOperators Topology ENNReal InnerProductSpace
def sourceTorusCoverPoint {n : ℕ}
    (q : WeightedTorusHilbert.LogTorus n) :
    TorusCharacters.LogSpace n :=
  JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
    q.1 (fun i => (AddCircle.equivIoc 1 0 (q.2 i)).1)
theorem realLogCoordinate_sourceTorusCoverPoint {n : ℕ}
    (q : WeightedTorusHilbert.LogTorus n) :
    BergmanDiagonalBasisIndependence.realLogCoordinate
        (sourceTorusCoverPoint q) = q.1 := by
  funext i
  simp [sourceTorusCoverPoint,
    BergmanDiagonalBasisIndependence.realLogCoordinate,
    JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
    Complex.add_re, Complex.mul_re]
  ring
theorem sourceTorusFundamentalAngularRepresentative {n : ℕ}
    (q : WeightedTorusHilbert.LogTorus n) :
    (fun i : Fin n =>
      (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) : UnitAddCircle)) =
      q.2 := by
  funext i
  exact (AddCircle.equivIoc 1 0).symm_apply_apply (q.2 i)
theorem torusCharacter_sourceTorusCoverPoint {n : ℕ}
    (m : Fin n → ℤ)
    (q : WeightedTorusHilbert.LogTorus n) :
    TorusCharacters.torusCharacter m
        (sourceTorusCoverPoint q) =
      WeightedTorusHilbert.torusMonomial m q := by
  let t : Space n :=
    fun i => (AddCircle.equivIoc 1 0 (q.2 i)).1
  have ht : (fun i : Fin n => (t i : UnitAddCircle)) = q.2 :=
    sourceTorusFundamentalAngularRepresentative q
  have hneg :
      TorusCharacters.characterExponent (-m)
          (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
            0 t) =
        -TorusCharacters.characterExponent m
          (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
            0 t) := by
    simp [TorusCharacters.characterExponent,
      Finset.sum_neg_distrib]
  have hfourier :
      UnitAddTorus.mFourier m q.2 =
        Complex.exp
          (TorusCharacters.characterExponent m
            (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
              0 t)) := by
    rw [← ht]
    have h :=
      JointHolomorphicLaurentFourierCompatibility.mFourier_neg_coe_eq_exp
        (-m) t
    simpa [hneg] using h
  unfold WeightedTorusHilbert.torusMonomial
    WeightedTorusHilbert.radialCharacter
    TorusCharacters.torusCharacter
  change
    Complex.exp
        (TorusCharacters.characterExponent m
          (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
            q.1 t)) =
      Complex.exp
          (TorusCharacters.characterExponent m
            (TorusCharacters.realLogSlice q.1)) *
        UnitAddTorus.mFourier m q.2
  rw [JointHolomorphicLaurentFourierCompatibility.characterExponent_logarithmicPoint,
    Complex.exp_add, hfourier]
def sourcePositiveJointTimePoint {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) (ht : 0 < t) :
    ActualJetUpperEnvelope.PositiveJointLogSpace n := by
  refine ⟨(z, (Real.exp (t / 2) : ℂ)), ?_⟩
  rw [Complex.normSq_ofReal]
  have h : (1 : ℝ) < Real.exp (t / 2) := by
    simpa using (Real.exp_lt_exp.mpr (half_pos ht))
  nlinarith
theorem jointLogTime_sourcePositiveJointTimePoint {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) (ht : 0 < t) :
    ActualJetUpperEnvelope.jointLogTime
      (sourcePositiveJointTimePoint z t ht) = t := by
  unfold ActualJetUpperEnvelope.jointLogTime
    sourcePositiveJointTimePoint
  rw [Complex.normSq_ofReal, ← Real.exp_add]
  have hadd : t / 2 + t / 2 = t := by ring
  rw [hadd, Real.log_exp]
theorem jointRealCoordinate_sourcePositiveJointTimePoint
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) (ht : 0 < t) :
    ActualJetUpperEnvelope.jointRealCoordinate
      (sourcePositiveJointTimePoint z t ht) =
      BergmanDiagonalBasisIndependence.realLogCoordinate z := by
  rfl
theorem measurable_sourceTorusCoverPoint {n : ℕ} :
    Measurable
      (sourceTorusCoverPoint (n := n)) := by
  apply measurable_pi_lambda
  intro i
  have hangle :
      Measurable
        (fun q : WeightedTorusHilbert.LogTorus n =>
          ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ)) :=
    measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIoc 1 0).measurable.comp
        ((measurable_pi_apply i).comp measurable_snd))
  change Measurable
    (fun q : WeightedTorusHilbert.LogTorus n =>
      (q.1 i : ℂ) / 2 +
        (2 * (Real.pi : ℂ) * Complex.I) *
          (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ)) )
  fun_prop
end JetEnvelopeRightDerivative
namespace JetEnvelopeLocalGrowth
open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
universe u v
def sourceLocalPolynomialConstant {n : ℕ}
    (K : CenteredBody n) : ℝ :=
  GlobalBergmanKernelBound.globalKernelPolynomialConstant K *
    (normalizedVolume K.carrier + 1)
def sourceLocalKernelLogError {n : ℕ}
    (K : CenteredBody n) (k : ℕ) : ℝ :=
  (Real.log (sourceLocalPolynomialConstant K) +
    3 * (n : ℝ) * Real.log (k : ℝ)) / (k : ℝ)
def sourceLocalJointRegion {n : ℕ}
    (p : TorusCharacters.LogSpace n) (R : ℝ) :
    Set (PositiveJointLogSpace n) :=
  {w | dist w.val.1 p <
    R * Real.exp (-jointLogTime w / 2)}
def sourcePositiveAngularArc (δ : ℝ) : Set UnitAddCircle :=
  {θ | ((AddCircle.equivIoc 1 0 θ).1 : ℝ) < δ}
def sourceLocalRadialBox (n : ℕ) (δ : ℝ) :
    Set (Space n) :=
  Set.univ.pi fun _ : Fin n => Set.Ioo (-δ) δ
def sourceLocalAngularBox (n : ℕ) (δ : ℝ) :
    Set (TorusCharacters.AngularTorus n) :=
  Set.univ.pi fun _ : Fin n => sourcePositiveAngularArc δ
def sourceLocalTorusBox (n : ℕ) (δ : ℝ) :
    Set (WeightedTorusHilbert.LogTorus n) :=
  sourceLocalRadialBox n δ ×ˢ sourceLocalAngularBox n δ
def sourceLocalBoxScale (R : ℝ) : ℝ :=
  min 1 (R / (1 + 4 * Real.pi))
def sourceLocalBoxRadius (R t : ℝ) : ℝ :=
  sourceLocalBoxScale R * Real.exp (-t / 2)
def sourceLocalBallVolumeConstant (n : ℕ) (R : ℝ) : ℝ :=
  (2 : ℝ) ^ n * sourceLocalBoxScale R ^ (2 * n)
end JetEnvelopeLocalGrowth
namespace JetEnvelopeGlobalPlurisubharmonic
open Set Filter MeasureTheory Metric
open ActualJetUpperEnvelope JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace
abbrev SourceJointComplexCover (n : ℕ) :=
  TorusCharacters.LogSpace n × ℂ
def sourceJointCoverTime {n : ℕ}
    (q : SourceJointComplexCover n) : ℝ :=
  2 * q.2.re
theorem continuous_sourceJointCoverTime (n : ℕ) :
    Continuous (sourceJointCoverTime (n := n)) := by
  unfold sourceJointCoverTime
  fun_prop
theorem normSq_mul_of_norm_one
    (u : ℂ) (hu : ‖u‖ = 1) (z : ℂ) :
    Complex.normSq (u * z) = Complex.normSq z := by
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, hu]
  simp
def sourceJointPhaseHomeomorph {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1) :
    PositiveJointLogSpace n ≃ₜ PositiveJointLogSpace n := by
  have hu0 : u ≠ 0 := by
    intro hzero
    simp [hzero] at hu
  let h :
      (TorusCharacters.LogSpace n × ℂ) ≃ₜ
        (TorusCharacters.LogSpace n × ℂ) :=
    (Homeomorph.refl (TorusCharacters.LogSpace n)).prodCongr
      (Homeomorph.mulLeft₀ u hu0)
  exact h.subtype fun q => by
    change
      (1 : ℝ) < Complex.normSq q.2 ↔
        (1 : ℝ) < Complex.normSq (u * q.2)
    rw [normSq_mul_of_norm_one u hu]
theorem upperRegularization_comp_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) (h : X ≃ₜ Y) (x : X) :
    upperRegularization (fun y : X => f (h y)) x =
      upperRegularization f (h x) := by
  unfold upperRegularization
  congr 1
  ext c
  change
    (∀ᶠ y : X in 𝓝 x, f (h y) ≤ c) ↔
      ∀ᶠ z : Y in 𝓝 (h x), f z ≤ c
  rw [← h.map_nhds_eq x, Filter.eventually_map]
def sourceJointCoverExp {n : ℕ}
    (q : SourceJointComplexCover n) :
    TorusCharacters.LogSpace n × ℂ :=
  (q.1, Complex.exp q.2)
theorem differentiable_sourceJointCoverExp (n : ℕ) :
    Differentiable ℂ (sourceJointCoverExp (n := n)) := by
  unfold sourceJointCoverExp
  fun_prop
theorem continuous_sourceJointCoverExp (n : ℕ) :
    Continuous (sourceJointCoverExp (n := n)) :=
  (differentiable_sourceJointCoverExp n).continuous
theorem normSq_sourceJointCoverExp
    {n : ℕ} (q : SourceJointComplexCover n) :
    Complex.normSq (sourceJointCoverExp q).2 =
      Real.exp (sourceJointCoverTime q) := by
  unfold sourceJointCoverExp sourceJointCoverTime
  calc
    Complex.normSq (Complex.exp q.2) =
        Real.exp q.2.re ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    _ = Real.exp (2 * q.2.re) := by
      simpa using (Real.exp_nat_mul q.2.re 2).symm
def sourceJointExpPositiveLift {n : ℕ}
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    PositiveJointLogSpace n := by
  refine ⟨sourceJointCoverExp q, ?_⟩
  rw [normSq_sourceJointCoverExp]
  simpa using (Real.exp_lt_exp.mpr hq)
theorem sourceJointAuxiliaryPhase_norm
    (η : ℂ) :
    ‖Complex.exp ((η.im : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]
def sourceRealLogCoordinateCLM (n : ℕ) :
    TorusCharacters.LogSpace n →L[ℝ] Space n :=
  ContinuousLinearMap.pi fun i =>
    (2 : ℝ) • (Complex.reCLM.comp
      (ContinuousLinearMap.proj i))
theorem sourceJointCircleAverage_eq_setAverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R : ℝ) :
    (⨍ θ in Set.Ioc 0 (2 * Real.pi), f (circleMap 0 R θ)) =
      Real.circleAverage f 0 R := by
  rw [MeasureTheory.setAverage_eq, Real.circleAverage_def,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp [MeasureTheory.measureReal_def, Real.volume_Ioc,
    Real.pi_pos.le]
theorem sourceJointSpatialLine_circleAverage
    {n : ℕ} (q v : SourceJointComplexCover n) (R : ℝ) :
    Real.circleAverage
      (fun w : ℂ => (q + w • v).1) 0 R = q.1 := by
  let f : ℂ → TorusCharacters.LogSpace n :=
    fun w => (q + w • v).1
  have hf : Differentiable ℂ f := by
    dsimp [f]
    fun_prop
  have hdc : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) |R|) :=
    hf.diffContOnCl
  simpa [f] using hdc.circleAverage
end JetEnvelopeGlobalPlurisubharmonic
namespace EnvelopeSmoothing
open Set Function Filter MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology Convolution ContDiff
local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (TorusCharacters.LogSpace n))
    (volume : Measure ℂ)
def sourceJointShrinkingBump (n k : ℕ) :
    ContDiffBump (0 : SourceJointComplexCover n) where
  rIn := (1 / ((k : ℝ) + 1)) / 2
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact half_lt_self h
def sourceJointTimeEmbedding {n : ℕ}
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    SourceJointComplexCover n :=
  (z, (t / 2 : ℂ))
theorem sourceJointCoverTime_timeEmbedding {n : ℕ}
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    sourceJointCoverTime (sourceJointTimeEmbedding z t) = t := by
  simp [sourceJointCoverTime, sourceJointTimeEmbedding]
  ring
end EnvelopeSmoothing
namespace EnvelopeSpatialPeriodicity
open Set Function Filter MeasureTheory
open ActualJetUpperEnvelope JetEnvelopeRightDerivative
open scoped BigOperators Topology
def sourceJointSpatialDeckHomeomorph {n : ℕ}
    (m : Fin n → ℤ) :
    PositiveJointLogSpace n ≃ₜ PositiveJointLogSpace n := by
  let h :
      (TorusCharacters.LogSpace n × ℂ) ≃ₜ
        (TorusCharacters.LogSpace n × ℂ) :=
    (Homeomorph.addRight (TorusCharacters.imaginaryShift m)).prodCongr
      (Homeomorph.refl ℂ)
  exact h.subtype fun _ => Iff.rfl
end EnvelopeSpatialPeriodicity
namespace BergmanJetSpatialPeriodicity
open Set Function Filter MeasureTheory
open TorusCharacters AdaptedBergmanBasis BergmanMonomials MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic BergmanJetBasis BergmanJetGeodesic BergmanJetRealGeodesic
open BergmanJetUpperEnvelope ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic
open EnvelopeSpatialPeriodicity
open scoped BigOperators Topology
theorem momentHolomorphicRepresentative_spatial_periodic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport)
    (m : Fin n → ℤ) :
    Function.Periodic
      (momentHolomorphicRepresentative K hk F htransport s)
      (imaginaryShift m) := by
  classical
  intro z
  simp [momentHolomorphicRepresentative,
    Finsupp.linearCombination_apply, Finsupp.sum,
    normalizedHolomorphicMonomial,
    TorusCharacters.torusCharacter_imaginaryShift]
theorem momentJointJetSection_spatial_periodic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k))
    (τ : ℂ) (m : Fin n → ℤ) :
    Function.Periodic
      (fun z : LogSpace n =>
        momentJointJetSection K hk F htransport p N i (z, τ))
      (imaginaryShift m) := by
  intro z
  change
    momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p i)
        (z + imaginaryShift m) *
      τ ^ momentTruncatedJetOrder K hk F htransport p N i =
    momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p i) z *
      τ ^ momentTruncatedJetOrder K hk F htransport p N i
  rw [momentHolomorphicRepresentative_spatial_periodic
    K hk F htransport
    (momentSimultaneousJetBasis K hk F htransport p i) m z]
theorem momentJointJetDiagonal_spatial_periodic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ)
    (τ : ℂ) (m : Fin n → ℤ) :
    Function.Periodic
      (fun z : LogSpace n =>
        momentJointJetDiagonal K hk F htransport p N (z, τ))
      (imaginaryShift m) := by
  intro z
  unfold momentJointJetDiagonal
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact momentJointJetSection_spatial_periodic
    K hk F htransport p N i τ m z
theorem momentJetGeodesic_spatial_periodic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ)
    (t : ℝ) (m : Fin n → ℤ) :
    Function.Periodic
      (fun z : LogSpace n =>
        momentJetGeodesic K hk F htransport p N z t)
      (imaginaryShift m) := by
  intro z
  change
    momentJetGeodesic K hk F htransport p N
        (z + imaginaryShift m) t =
      momentJetGeodesic K hk F htransport p N z t
  rw [momentJetGeodesic_eq_log_jointJetDiagonal,
    momentJetGeodesic_eq_log_jointJetDiagonal]
  have hdiag := momentJointJetDiagonal_spatial_periodic
    K hk F htransport p N (Real.exp (t / 2) : ℂ) m z
  change
    momentJointJetDiagonal K hk F htransport p N
        (z + imaginaryShift m, (Real.exp (t / 2) : ℂ)) =
      momentJointJetDiagonal K hk F htransport p N
        (z, (Real.exp (t / 2) : ℂ)) at hdiag
  rw [hdiag]
end BergmanJetSpatialPeriodicity
namespace BergmanJetTorusEnvelope
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit JetEnvelopeRightDerivative
open scoped BigOperators ENNReal Topology
def momentEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (t : ℝ) : ℝ :=
  if ht : 0 < t then
    momentJointUpperEnvelope K F htransport p
      (sourcePositiveJointTimePoint z t ht)
  else
    momentNormalizedPotential F (realLogCoordinate z)
@[simp] theorem momentEnvelopeTimeSlice_zero
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) :
    momentEnvelopeTimeSlice K F htransport p z 0 =
      momentNormalizedPotential F (realLogCoordinate z) := by
  simp [momentEnvelopeTimeSlice]
theorem momentEnvelopeTimeSlice_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) {t : ℝ} (ht : t ≤ 0) :
    momentEnvelopeTimeSlice K F htransport p z t =
      momentNormalizedPotential F (realLogCoordinate z) := by
  simp [momentEnvelopeTimeSlice, not_lt.mpr ht]
theorem momentEnvelopeTimeSlice_of_positive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) {t : ℝ} (ht : 0 < t) :
    momentEnvelopeTimeSlice K F htransport p z t =
      momentJointUpperEnvelope K F htransport p
        (sourcePositiveJointTimePoint z t ht) := by
  simp [momentEnvelopeTimeSlice, ht]
def momentTorusEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n) (t : ℝ) : ℝ :=
  momentEnvelopeTimeSlice K F htransport p
    (sourceTorusCoverPoint q) t
@[simp] theorem momentTorusEnvelopeTimeSlice_zero
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n) :
    momentTorusEnvelopeTimeSlice K F htransport p q 0 =
      momentNormalizedPotential F q.1 := by
  unfold momentTorusEnvelopeTimeSlice
  rw [momentEnvelopeTimeSlice_zero,
    realLogCoordinate_sourceTorusCoverPoint]
theorem measurable_momentTorusEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (t : ℝ) :
    Measurable
      (fun q : LogTorus n =>
        momentTorusEnvelopeTimeSlice K F htransport p q t) := by
  by_cases ht : 0 < t
  · have hpoint :
        Measurable
          (fun q : LogTorus n =>
            sourcePositiveJointTimePoint
              (sourceTorusCoverPoint q) t ht) := by
      apply Measurable.subtype_mk
      have hcover := measurable_sourceTorusCoverPoint (n := n)
      fun_prop
    change Measurable
      (fun q : LogTorus n =>
        if h : 0 < t then
          momentJointUpperEnvelope K F htransport p
            (sourcePositiveJointTimePoint
              (sourceTorusCoverPoint q) t h)
        else
          momentNormalizedPotential F
            (realLogCoordinate (sourceTorusCoverPoint q)))
    simp only [dif_pos ht]
    exact (upperSemicontinuous_momentJointUpperEnvelope
      K F htransport p).measurable.comp hpoint
  · have hnonpos : t ≤ 0 := le_of_not_gt ht
    have heq :
        (fun q : LogTorus n =>
          momentTorusEnvelopeTimeSlice K F htransport p q t) =
        (fun q : LogTorus n =>
          momentNormalizedPotential F q.1) := by
      funext q
      unfold momentTorusEnvelopeTimeSlice
      rw [momentEnvelopeTimeSlice_of_nonpositive
        K F htransport p (sourceTorusCoverPoint q) hnonpos,
        realLogCoordinate_sourceTorusCoverPoint]
    rw [heq]
    exact (continuous_momentNormalizedPotential F).measurable.comp
      measurable_fst
end BergmanJetTorusEnvelope
namespace BergmanJetPhaseLaplace
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ENNReal Topology
theorem exists_momentNormalized_phase_linear_coercivity
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∃ δ C : ℝ, 0 < δ ∧
      ∀ x : Space n,
        phase u (momentNormalizedPotential F) x ≤
          C - δ * ‖x‖ := by
  obtain ⟨δ, C, hδ, hcoerc⟩ :=
    exists_finiteEnergySource_interior_phase_linear_coercivity
      F htransport hu
  let c : ℝ :=
    Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier)
  refine ⟨δ, C - c, hδ, ?_⟩
  intro x
  have hx := hcoerc x
  change
    pairing u x -
        (F.potential x +
          Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) ≤
      C - c - δ * ‖x‖
  dsimp [c]
  linarith
theorem momentNormalized_monomialIntegral_le_exp_mul_base
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {M : ℝ}
    (hM : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤ M)
    {k : ℝ} (hk : 1 ≤ k) :
    monomialIntegral k u (momentNormalizedPotential F) ≤
      Real.exp ((k - 1) * M) *
        monomialIntegral 1 u (momentNormalizedPotential F) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hkint :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu hkpos
  have hbase :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu (k := (1 : ℝ)) zero_lt_one
  have hmajor := hbase.const_mul (Real.exp ((k - 1) * M))
  unfold monomialIntegral
  calc
    (∫ x : Space n,
      monomialWeight k u (momentNormalizedPotential F) x
        ∂(volume : Measure (Space n))) ≤
      ∫ x : Space n,
        Real.exp ((k - 1) * M) *
          monomialWeight 1 u
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n)) := by
            apply integral_mono hkint hmajor
            intro x
            unfold monomialWeight
            change
              Real.exp (k *
                (pairing u x - momentNormalizedPotential F x)) ≤
                Real.exp ((k - 1) * M) *
                  Real.exp (1 *
                    (pairing u x - momentNormalizedPotential F x))
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hx := hM x
            unfold phase at hx
            nlinarith
    _ = Real.exp ((k - 1) * M) *
        (∫ x : Space n,
          monomialWeight 1 u
            (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n))) :=
      integral_const_mul _ _
theorem momentNormalized_log_monomialIntegral_div_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {M : ℝ}
    (hM : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤ M)
    {k : ℝ} (hk : 1 ≤ k) :
    Real.log
      (monomialIntegral k u (momentNormalizedPotential F)) / k ≤
        |M| +
          |Real.log
            (monomialIntegral 1 u
              (momentNormalizedPotential F))| := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hI :=
    monomialIntegral_momentNormalized_pos
      F htransport hu hkpos
  have hbase :=
    monomialIntegral_momentNormalized_pos
      F htransport hu (k := (1 : ℝ)) zero_lt_one
  have hupper :=
    momentNormalized_monomialIntegral_le_exp_mul_base
      F htransport hu hM hk
  have hlog := Real.log_le_log hI hupper
  rw [Real.log_mul (Real.exp_ne_zero _) hbase.ne',
    Real.log_exp] at hlog
  apply (div_le_iff₀ hkpos).mpr
  calc
    Real.log
      (monomialIntegral k u (momentNormalizedPotential F)) ≤
        (k - 1) * M +
          Real.log
            (monomialIntegral 1 u
              (momentNormalizedPotential F)) := hlog
    _ ≤ k * |M| +
          k * |Real.log
            (monomialIntegral 1 u
              (momentNormalizedPotential F))| := by
      apply add_le_add
      · calc
          (k - 1) * M ≤
              (k - 1) * |M| :=
            mul_le_mul_of_nonneg_left
              (le_abs_self M) (sub_nonneg.mpr hk)
          _ ≤ k * |M| :=
            mul_le_mul_of_nonneg_right
              (by linarith) (abs_nonneg M)
      · calc
          Real.log
            (monomialIntegral 1 u
              (momentNormalizedPotential F)) ≤
              |Real.log
                (monomialIntegral 1 u
                  (momentNormalizedPotential F))| :=
            le_abs_self _
          _ ≤ k * |Real.log
              (monomialIntegral 1 u
                (momentNormalizedPotential F))| := by
            have hnonneg :
                0 ≤ |Real.log
                  (monomialIntegral 1 u
                    (momentNormalizedPotential F))| :=
              abs_nonneg _
            nlinarith
    _ = (|M| +
            |Real.log
              (monomialIntegral 1 u
                (momentNormalizedPotential F))|) * k := by ring
theorem exists_momentNormalized_log_monomialIntegral_uniform_bound
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∃ C : ℝ, ∀ k : ℕ, 0 < k →
      Real.log
        (monomialIntegral (k : ℝ) u
          (momentNormalizedPotential F)) /
            (k : ℝ) ≤ C := by
  obtain ⟨δ, M, hδ, hphase⟩ :=
    exists_momentNormalized_phase_linear_coercivity
      F htransport hu
  have hM : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤ M := by
    intro x
    exact (hphase x).trans
      (sub_le_self _ (mul_nonneg hδ.le (norm_nonneg x)))
  refine ⟨|M| +
    |Real.log
      (monomialIntegral 1 u
        (momentNormalizedPotential F))|, ?_⟩
  intro k hk
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  exact momentNormalized_log_monomialIntegral_div_le
    F htransport hu hM hkreal
end BergmanJetPhaseLaplace
namespace BergmanJetMonomialEnvelopeLower
open Set Function Filter MeasureTheory Metric
open SupportFunction MonomialIntegrability BergmanMonomials BergmanDiagonalBasisIndependence
open LatticeAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakBergman BergmanJetRealGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopePlurisubharmonic BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPhaseLaplace JetEnvelopeRightDerivative ActualJetUpperEnvelope
open scoped BigOperators ENNReal Topology
def repeatedMomentMonomialIndex
    {n k : ℕ} (K : CenteredBody n)
    (hk : 0 < k)
    (u : monomialIndex K k)
    (s : ℕ) (hs : 0 < s) :
    monomialIndex K (s * k) := by
  have hsk : 0 < s * k := Nat.mul_pos hs hk
  refine ⟨(u : Space n), ?_⟩
  apply (mem_monomialIndex_iff K hsk
    (u : Space n)).mpr
  obtain ⟨hu, hz⟩ :=
    (mem_monomialIndex_iff K hk
      (u : Space n)).mp u.property
  refine ⟨hu, ?_⟩
  intro i
  obtain ⟨m, hm⟩ := hz i
  refine ⟨(s : ℤ) * m, ?_⟩
  change
    (((s : ℤ) * m : ℤ) : ℝ) =
      ((s * k : ℕ) : ℝ) * (u : Space n) i
  push_cast
  change ((s : ℕ) : ℝ) * (m : ℝ) =
    ((s : ℕ) : ℝ) * (k : ℝ) * (u : Space n) i
  have hm' : (m : ℝ) = (k : ℝ) * (u : Space n) i := by
    exact_mod_cast hm
  rw [hm']
  ring
theorem moment_diagonalTerm_le_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    (x : Space n) :
    diagonalTerm K k (momentNormalizedPotential F) u x ≤
      diagonalKernel K k
        (momentNormalizedPotential F) x := by
  classical
  let := (monomialIndex_finite K hk).fintype
  unfold diagonalKernel
  rw [tsum_fintype]
  have hnonneg :
      ∀ v : monomialIndex K k,
        0 ≤ diagonalTerm K k
          (momentNormalizedPotential F) v x := by
    intro v
    unfold diagonalTerm
    exact div_nonneg (Real.exp_pos _).le
      (monomialIntegral_momentNormalized_pos
        F htransport v.property.1
        (by exact_mod_cast hk)).le
  simpa using
    (Finset.single_le_sum
      (s := (Finset.univ : Finset (monomialIndex K k)))
      (f := fun v : monomialIndex K k =>
        diagonalTerm K k (momentNormalizedPotential F) v x)
      (fun v _ => hnonneg v)
      (Finset.mem_univ u))
theorem moment_pairing_sub_log_monomialNorm_le_log_diagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    (x : Space n) :
    pairing (u : Space n) x -
      Real.log
        (monomialIntegral (k : ℝ) (u : Space n)
          (momentNormalizedPotential F)) / (k : ℝ) ≤
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hnorm :
      0 < monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) :=
    monomialIntegral_momentNormalized_pos
      F htransport u.property.1 hkreal
  have hterm :
      0 < diagonalTerm K k
        (momentNormalizedPotential F) u x := by
    unfold diagonalTerm
    exact div_pos (Real.exp_pos _) hnorm
  have hle := moment_diagonalTerm_le_diagonalKernel
    K hk F htransport u x
  have hlog := Real.log_le_log hterm hle
  unfold diagonalTerm at hlog
  rw [Real.log_div (Real.exp_ne_zero _) hnorm.ne',
    Real.log_exp] at hlog
  calc
    pairing (u : Space n) x -
        Real.log
          (monomialIntegral (k : ℝ) (u : Space n)
            (momentNormalizedPotential F)) / (k : ℝ) =
      ((k : ℝ) * pairing (u : Space n) x -
        Real.log
          (monomialNormSquared k (u : Space n)
            (momentNormalizedPotential F))) / (k : ℝ) := by
          unfold monomialNormSquared
          field_simp
    _ ≤ Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) x) / (k : ℝ) :=
      (div_le_div_iff_of_pos_right hkreal).mpr hlog
theorem moment_fixedMonomial_pairing_sub_le_log_diagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (s : ℕ) (hs : 0 < s)
    (x : Space n) :
    pairing (u : Space n) x - C ≤
      Real.log
        (diagonalKernel K (s * k)
          (momentNormalizedPotential F) x) /
            ((s * k : ℕ) : ℝ) := by
  have hsk := Nat.mul_pos hs hk
  let v := repeatedMomentMonomialIndex K hk u s hs
  have hnorm := hC (s * k) hsk
  have hdiag :=
    moment_pairing_sub_log_monomialNorm_le_log_diagonal
      K hsk F htransport v x
  change
    pairing (u : Space n) x -
      Real.log
        (monomialIntegral ((s * k : ℕ) : ℝ)
          (u : Space n)
          (momentNormalizedPotential F)) /
            ((s * k : ℕ) : ℝ) ≤
      Real.log
        (diagonalKernel K (s * k)
          (momentNormalizedPotential F) x) /
            ((s * k : ℕ) : ℝ) at hdiag
  linarith
theorem moment_fixedMonomial_pairing_sub_le_positiveJointGeodesic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (s : ℕ) (hs : 0 < s)
    (q : PositiveJointLogSpace n) :
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentPositiveJointGeodesic K F htransport p
        (s * k - 1) q := by
  let l := s * k - 1
  have hsk : 0 < s * k := Nat.mul_pos hs hk
  have hl : l + 1 = s * k := by
    dsimp [l]
    omega
  let N :=
    Nat.floor
      (BodyScale.canonicalScale K *
        ((l + 1 : ℕ) : ℝ))
  calc
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      Real.log
        (diagonalKernel K (s * k)
          (momentNormalizedPotential F)
          (realLogCoordinate q.val.1)) /
            ((s * k : ℕ) : ℝ) :=
      moment_fixedMonomial_pairing_sub_le_log_diagonal
        K hk F htransport u hC s hs
        (realLogCoordinate q.val.1)
    _ = Real.log
        (diagonalKernel K (l + 1)
          (momentNormalizedPotential F)
          (realLogCoordinate q.val.1)) /
            ((l + 1 : ℕ) : ℝ) := by rw [hl]
    _ = momentJetGeodesic K
        (Nat.zero_lt_succ l) F htransport p N q.val.1 0 :=
      (momentJetGeodesic_zero_eq_log_diagonalKernel
        K (Nat.zero_lt_succ l) F htransport p q.val.1 N).symm
    _ ≤ momentJetGeodesic K
        (Nat.zero_lt_succ l) F htransport p N
        q.val.1 (jointLogTime q) :=
      monotone_momentJetGeodesic
        K (Nat.zero_lt_succ l) F htransport p q.val.1 N
        (jointLogTime_pos q).le
    _ = momentPositiveJointGeodesic
        K F htransport p l q := by
      symm
      exact momentPositiveJointGeodesic_eq_momentJetGeodesic
        K F htransport p l q
theorem moment_fixedMonomial_pairing_sub_le_tailSup
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentJointTailSup K F htransport p r q := by
  let a := momentJointTailStart K F htransport p + r
  let s := a + 1
  have hs : 0 < s := by
    dsimp [s]
    omega
  have hbig : a + 1 ≤ s * k := by
    dsimp [s]
    exact Nat.le_mul_of_pos_right (a + 1) hk
  let j := s * k - 1 - a
  have hindex : a + j = s * k - 1 := by
    dsimp [j]
    omega
  calc
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentPositiveJointGeodesic K F htransport p
        (s * k - 1) q :=
      moment_fixedMonomial_pairing_sub_le_positiveJointGeodesic
        K hk F htransport u hC p s hs q
    _ = momentPositiveJointGeodesic K F htransport p
        (a + j) q := by rw [hindex]
    _ ≤ momentJointTailSup K F htransport p r q := by
      unfold momentJointTailSup
      apply le_csSup
        (momentJointTailSup_range_bddAbove
          K F htransport p r q)
      refine ⟨j, ?_⟩
      change
        momentPositiveJointGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r + j) q =
        momentPositiveJointGeodesic K F htransport p
          (a + j) q
      rfl
theorem moment_fixedMonomial_pairing_sub_le_tailUpperEnvelope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentJointTailUpperEnvelope K F htransport p r q := by
  calc
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentJointTailSup K F htransport p r q :=
      moment_fixedMonomial_pairing_sub_le_tailSup
        K hk F htransport u hC p r q
    _ ≤ momentJointTailUpperEnvelope
        K F htransport p r q :=
      le_upperRegularization
        (momentJointTailSup K F htransport p r) q
        (momentJointTailSup_localUpperBounds_nonempty
          K F htransport p r q)
theorem moment_fixedMonomial_pairing_sub_le_upperEnvelope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) :
    pairing (u : Space n)
        (realLogCoordinate q.val.1) - C ≤
      momentJointUpperEnvelope K F htransport p q := by
  apply (le_ciInf_iff
    (momentJointTailUpperEnvelope_bddBelow
      K F htransport p q)).mpr
  intro r
  exact moment_fixedMonomial_pairing_sub_le_tailUpperEnvelope
    K hk F htransport u hC p r q
theorem moment_fixedMonomial_pairing_sub_le_torusEnvelope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    {C : ℝ}
    (hC : ∀ l : ℕ, 0 < l →
      Real.log
        (monomialIntegral (l : ℝ) (u : Space n)
          (momentNormalizedPotential F)) /
            (l : ℝ) ≤ C)
    (p : TorusCharacters.LogSpace n)
    (q : WeightedTorusHilbert.LogTorus n)
    {t : ℝ} (ht : 0 < t) :
    pairing (u : Space n) q.1 - C ≤
      momentTorusEnvelopeTimeSlice
        K F htransport p q t := by
  unfold momentTorusEnvelopeTimeSlice
  rw [momentEnvelopeTimeSlice_of_positive
    K F htransport p (sourceTorusCoverPoint q) ht]
  have h := moment_fixedMonomial_pairing_sub_le_upperEnvelope
    K hk F htransport u hC p
      (sourcePositiveJointTimePoint
        (sourceTorusCoverPoint q) t ht)
  simpa [sourcePositiveJointTimePoint,
    realLogCoordinate_sourceTorusCoverPoint] using h
theorem exists_moment_fixedMonomial_torusEnvelope_lower
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    ∃ C : ℝ, ∀ (p : TorusCharacters.LogSpace n)
      (q : WeightedTorusHilbert.LogTorus n)
      (t : ℝ), 0 < t →
        pairing (u : Space n) q.1 - C ≤
          momentTorusEnvelopeTimeSlice
            K F htransport p q t := by
  obtain ⟨C, hC⟩ :=
    exists_momentNormalized_log_monomialIntegral_uniform_bound
      F htransport u.property.1
  exact ⟨C, fun p q t ht =>
    moment_fixedMonomial_pairing_sub_le_torusEnvelope
      K hk F htransport u hC p q ht⟩
end BergmanJetMonomialEnvelopeLower
namespace BergmanJetPointwiseLogKernel
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability BergmanMonomials MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open MomentWeakGlobalKernel BergmanJetPhaseLaplace BergmanJetMonomialEnvelopeLower
open MomentMoserTrudinger SpatialBergmanPointwiseAsymptotics
open scoped BigOperators ENNReal Topology
end BergmanJetPointwiseLogKernel
namespace WeightedTorusDistributionBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
local instance _p2m_local_instance_3610026555_18903 : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance _p2m_local_instance_3610026555_18906 : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def unweightedTorusMeasure (n : ℕ) :
    Measure (WeightedTorusHilbert.LogTorus n) :=
  (volume : Measure (Space n)).prod
    (WeightedTorusHilbert.angularMeasure n)
theorem unweightedTorusMeasure_isLocallyFinite (n : ℕ) :
    IsLocallyFiniteMeasure (unweightedTorusMeasure n) := by
  unfold unweightedTorusMeasure
  infer_instance
abbrev angularFundamentalCell (n : ℕ) :=
  {t : Space n // ∀ i : Fin n,
    t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)}
def angularFundamentalMeasure (n : ℕ) :
    Measure (angularFundamentalCell n) :=
  (volume : Measure (Space n)).comap Subtype.val
def angularFundamentalEquiv (n : ℕ) :
    TorusCharacters.AngularTorus n ≃ᵐ
      angularFundamentalCell n :=
  UnitAddTorus.measurableEquivPiIoc (fun _ : Fin n => 0)
def torusFundamentalMeasurableEquiv (n : ℕ) :
    WeightedTorusHilbert.LogTorus n ≃ᵐ
      Space n × angularFundamentalCell n :=
  MeasurableEquiv.prodCongr
    (MeasurableEquiv.refl (Space n))
    (angularFundamentalEquiv n)
def unweightedFundamentalMeasure (n : ℕ) :
    Measure (Space n × angularFundamentalCell n) :=
  (volume : Measure (Space n)).prod
    (angularFundamentalMeasure n)
def logarithmicCoordinatesEquiv (n : ℕ) :
    (Space n × Space n) ≃L[ℝ]
      TorusCharacters.LogSpace n where
  toFun p :=
    JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
      p.1 p.2
  invFun z :=
    (fun i => 2 * (z i).re,
     fun i => (z i).im / (2 * Real.pi))
  left_inv := by
    intro p
    apply Prod.ext
    · funext i
      simp [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
        Complex.mul_re]
      ring
    · funext i
      simp [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
        Complex.mul_im]
  right_inv := by
    intro z
    funext i
    apply Complex.ext
    · simp [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
        Complex.mul_re, -Complex.ofReal_mul, -Complex.ofReal_div]
    · simp [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
        Complex.mul_im, -Complex.ofReal_mul, -Complex.ofReal_div]
      field_simp [Real.pi_ne_zero]
  map_add' := by
    intro p q
    funext i
    simp [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint]
    ring
  map_smul' := by
    intro c p
    funext i
    simp [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
      Complex.real_smul]
    ring
  continuous_toFun := by
    apply continuous_pi
    intro i
    change Continuous
      (fun p : Space n × Space n =>
        (p.1 i : ℂ) / 2 +
          (2 * (Real.pi : ℂ) * Complex.I) * (p.2 i : ℂ))
    fun_prop
  continuous_invFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      fun_prop
    · apply continuous_pi
      intro i
      fun_prop
@[simp] theorem logarithmicCoordinatesEquiv_apply {n : ℕ}
    (x t : Space n) :
    logarithmicCoordinatesEquiv n (x, t) =
      JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t := rfl
def logarithmicCoverPushforward (n : ℕ) :
    Measure (TorusCharacters.LogSpace n) :=
  (volume : Measure (Space n × Space n)).map
    (logarithmicCoordinatesEquiv n)
theorem logarithmicCoverPushforward_isAddHaar (n : ℕ) :
    (logarithmicCoverPushforward n).IsAddHaarMeasure := by
  let :
      (volume : Measure (Space n × Space n)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod.instIsAddHaarMeasure _ _
  unfold logarithmicCoverPushforward
  exact (logarithmicCoordinatesEquiv n).isAddHaarMeasure_map
    (volume : Measure (Space n × Space n))
def logarithmicCoverJacobianFactor (n : ℕ) : NNReal := by
  letI : (logarithmicCoverPushforward n).IsAddHaarMeasure :=
    logarithmicCoverPushforward_isAddHaar n
  exact (logarithmicCoverPushforward n).addHaarScalarFactor
    (volume : Measure (TorusCharacters.LogSpace n))
theorem logarithmicCoverJacobianFactor_pos (n : ℕ) :
    0 < logarithmicCoverJacobianFactor n := by
  let : (logarithmicCoverPushforward n).IsAddHaarMeasure :=
    logarithmicCoverPushforward_isAddHaar n
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (logarithmicCoverPushforward n)
    (volume : Measure (TorusCharacters.LogSpace n))
theorem logarithmicCoverPushforward_eq_smul_volume (n : ℕ) :
    logarithmicCoverPushforward n =
      logarithmicCoverJacobianFactor n •
        (volume : Measure (TorusCharacters.LogSpace n)) := by
  let : (logarithmicCoverPushforward n).IsAddHaarMeasure :=
    logarithmicCoverPushforward_isAddHaar n
  exact Measure.isAddLeftInvariant_eq_smul
    (logarithmicCoverPushforward n)
    (volume : Measure (TorusCharacters.LogSpace n))
def angularFundamentalBox {n : ℕ} (b : Space n) :
    Set (Space n) :=
  {t | ∀ i : Fin n, t i ∈ Set.Ioc (b i) (b i + 1)}
def angularCoverProjection (n : ℕ) :
    Space n → TorusCharacters.AngularTorus n :=
  fun t i => (t i : UnitAddCircle)
theorem angularCoverProjection_integer_add {n : ℕ}
    (t : Space n) (q : Fin n → ℤ) :
    angularCoverProjection n (fun i => t i + (q i : ℝ)) =
      angularCoverProjection n t := by
  funext i
  change ((t i + (q i : ℝ) : ℝ) : UnitAddCircle) =
    (t i : UnitAddCircle)
  rw [AddCircle.coe_add]
  have hq : (((q i : ℝ) : UnitAddCircle) = 0) := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨q i, by simp⟩
  rw [hq, add_zero]
theorem angularCoverProjection_measurePreserving {n : ℕ}
    (b : Space n) :
    MeasurePreserving (angularCoverProjection n)
      ((volume : Measure (Space n)).restrict
        (angularFundamentalBox b))
      (WeightedTorusHilbert.angularMeasure n) := by
  have hb : MeasurableSet (angularFundamentalBox b) := by
    unfold angularFundamentalBox
    exact MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have hp : Measurable (angularCoverProjection n) := by
    apply measurable_pi_lambda
    intro i
    exact AddCircle.measurable_mk'.comp (measurable_pi_apply i)
  refine ⟨hp, ?_⟩
  rw [← map_comap_subtype_coe hb (volume : Measure (Space n)),
    Measure.map_map hp measurable_subtype_coe]
  change
    Measure.map
      (UnitAddTorus.measurableEquivPiIoc b).symm
      ((volume : Measure (Space n)).comap
        (Subtype.val : angularFundamentalBox b → Space n)) =
      WeightedTorusHilbert.angularMeasure n
  change
    Measure.map
      (UnitAddTorus.measurableEquivPiIoc b).symm
      ((volume : Measure (Space n)).comap
        (Subtype.val : angularFundamentalBox b → Space n)) =
      (volume : Measure (TorusCharacters.AngularTorus n))
  exact ((UnitAddTorus.measurePreserving_equivPiIoc b).symm
    (UnitAddTorus.measurableEquivPiIoc b)).map_eq
def realTorusCoverProjection (n : ℕ) :
    Space n × Space n →
      WeightedTorusHilbert.LogTorus n :=
  fun p => (p.1, angularCoverProjection n p.2)
theorem realTorusCoverProjection_measurePreserving {n : ℕ}
    (μ : Measure (Space n)) [SFinite μ]
    (b : Space n) :
    MeasurePreserving (realTorusCoverProjection n)
      (μ.prod
        ((volume : Measure (Space n)).restrict
          (angularFundamentalBox b)))
      (μ.prod (WeightedTorusHilbert.angularMeasure n)) := by
  change MeasurePreserving
    (Prod.map id (angularCoverProjection n))
    (μ.prod
      ((volume : Measure (Space n)).restrict
        (angularFundamentalBox b)))
    (μ.prod (WeightedTorusHilbert.angularMeasure n))
  exact (MeasurePreserving.id μ).prod
    (angularCoverProjection_measurePreserving b)
theorem weightedRealTorusCoverProjection_measurePreserving {n k : ℕ}
    (φ : Space n → ℝ) (b : Space n) :
    MeasurePreserving (realTorusCoverProjection n)
      ((WeightedTorusHilbert.radialMeasure k φ).prod
        ((volume : Measure (Space n)).restrict
          (angularFundamentalBox b)))
      (WeightedTorusHilbert.weightedTorusMeasure k φ) := by
  simpa [WeightedTorusHilbert.weightedTorusMeasure] using
    realTorusCoverProjection_measurePreserving
      (WeightedTorusHilbert.radialMeasure k φ) b
def realTorusCoverLift {n : ℕ}
    (g : WeightedTorusHilbert.LogTorus n → ℂ) :
    Space n × Space n → ℂ :=
  fun p => g (realTorusCoverProjection n p)
theorem realTorusCoverLift_integrableOn_fundamental {n : ℕ}
    {g : WeightedTorusHilbert.LogTorus n → ℂ}
    (hg : LocallyIntegrable g (unweightedTorusMeasure n))
    {s : Set (Space n)} (hs : IsCompact s)
    (b : Space n) :
    IntegrableOn (realTorusCoverLift g)
      (s ×ˢ angularFundamentalBox b)
      (volume : Measure (Space n × Space n)) := by
  have htorus : IntegrableOn g
      (s ×ˢ (Set.univ : Set (TorusCharacters.AngularTorus n)))
      (unweightedTorusMeasure n) :=
    hg.integrableOn_isCompact (hs.prod isCompact_univ)
  have hradial : Integrable g
      (((volume : Measure (Space n)).restrict s).prod
        (WeightedTorusHilbert.angularMeasure n)) := by
    simpa [IntegrableOn, unweightedTorusMeasure,
      Measure.restrict_prod_eq_prod_univ] using htorus
  have hlift :=
    (realTorusCoverProjection_measurePreserving
      ((volume : Measure (Space n)).restrict s) b).integrable_comp_of_integrable
        hradial
  change Integrable (realTorusCoverLift g)
    (((volume : Measure (Space n)).prod
      (volume : Measure (Space n))).restrict
        (s ×ˢ angularFundamentalBox b))
  rw [← Measure.prod_restrict]
  change Integrable (g ∘ realTorusCoverProjection n)
    (((volume : Measure (Space n)).restrict s).prod
      ((volume : Measure (Space n)).restrict
        (angularFundamentalBox b)))
  exact hlift
theorem angularFundamentalBox_mem_nhds {n : ℕ}
    (t : Space n) :
    angularFundamentalBox
        (fun i : Fin n => t i - (1 / 2 : ℝ)) ∈ 𝓝 t := by
  have h :
      Set.univ.pi
        (fun i : Fin n =>
          Set.Ioc (t i - (1 / 2 : ℝ))
            (t i - (1 / 2 : ℝ) + 1)) ∈ 𝓝 t := by
    apply set_pi_mem_nhds Set.finite_univ
    intro i _
    apply Ioc_mem_nhds <;> linarith
  simpa [angularFundamentalBox, Set.pi] using h
theorem realTorusCoverLift_locallyIntegrable {n : ℕ}
    {g : WeightedTorusHilbert.LogTorus n → ℂ}
    (hg : LocallyIntegrable g (unweightedTorusMeasure n)) :
    LocallyIntegrable (realTorusCoverLift g)
      (volume : Measure (Space n × Space n)) := by
  intro p
  refine ⟨Metric.closedBall p.1 1 ×ˢ
    angularFundamentalBox
      (fun i : Fin n => p.2 i - (1 / 2 : ℝ)), ?_, ?_⟩
  · exact prod_mem_nhds
      (Metric.closedBall_mem_nhds p.1 (by norm_num))
      (angularFundamentalBox_mem_nhds p.2)
  · exact realTorusCoverLift_integrableOn_fundamental hg
      (isCompact_closedBall p.1 1)
      (fun i : Fin n => p.2 i - (1 / 2 : ℝ))
def complexTorusCoverProjection (n : ℕ) :
    TorusCharacters.LogSpace n →
      WeightedTorusHilbert.LogTorus n :=
  fun z => realTorusCoverProjection n
    ((logarithmicCoordinatesEquiv n).symm z)
@[simp] theorem complexTorusCoverProjection_logarithmicPoint {n : ℕ}
    (x t : Space n) :
    complexTorusCoverProjection n
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) =
      realTorusCoverProjection n (x, t) := by
  change
    realTorusCoverProjection n
      ((logarithmicCoordinatesEquiv n).symm
        (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          x t)) =
      realTorusCoverProjection n (x, t)
  rw [← logarithmicCoordinatesEquiv_apply,
    ContinuousLinearEquiv.symm_apply_apply]
theorem logarithmicPoint_integer_add {n : ℕ}
    (x t : Space n) (q : Fin n → ℤ) :
    JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
      x (fun i => t i + (q i : ℝ)) =
      JointHolomorphicLaurentFourierCompatibility.logarithmicPoint x t +
        TorusCharacters.imaginaryShift q := by
  funext i
  simp only [JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
    TorusCharacters.imaginaryShift, Pi.add_apply,
    Complex.ofReal_add, Complex.ofReal_intCast]
  ring
theorem complexTorusCoverProjection_imaginaryShift {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (q : Fin n → ℤ) :
    complexTorusCoverProjection n
      (z + TorusCharacters.imaginaryShift q) =
      complexTorusCoverProjection n z := by
  let p : Space n × Space n :=
    (logarithmicCoordinatesEquiv n).symm z
  have hz :
      JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2 = z := by
    change (logarithmicCoordinatesEquiv n) p = z
    exact (logarithmicCoordinatesEquiv n).apply_symm_apply z
  rw [← hz, ← logarithmicPoint_integer_add,
    complexTorusCoverProjection_logarithmicPoint,
    complexTorusCoverProjection_logarithmicPoint]
  change
    (p.1, angularCoverProjection n (fun i => p.2 i + (q i : ℝ))) =
      (p.1, angularCoverProjection n p.2)
  rw [angularCoverProjection_integer_add]
def complexTorusCoverLift {n : ℕ}
    (g : WeightedTorusHilbert.LogTorus n → ℂ) :
    TorusCharacters.LogSpace n → ℂ :=
  fun z => g (complexTorusCoverProjection n z)
theorem complexTorusCoverLift_periodic {n : ℕ}
    (g : WeightedTorusHilbert.LogTorus n → ℂ)
    (q : Fin n → ℤ) :
    Function.Periodic (complexTorusCoverLift g)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  unfold complexTorusCoverLift
  rw [complexTorusCoverProjection_imaginaryShift]
@[simp] theorem complexTorusCoverLift_logarithmicPoint {n : ℕ}
    (g : WeightedTorusHilbert.LogTorus n → ℂ)
    (x t : Space n) :
    complexTorusCoverLift g
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) =
      realTorusCoverLift g (x, t) := by
  change
    g (realTorusCoverProjection n
      ((logarithmicCoordinatesEquiv n).symm
        (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          x t))) =
      g (realTorusCoverProjection n (x, t))
  rw [← logarithmicCoordinatesEquiv_apply,
    ContinuousLinearEquiv.symm_apply_apply]
theorem locallyIntegrable_logarithmicCoverPushforward_iff {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ) :
    LocallyIntegrable g (logarithmicCoverPushforward n) ↔
      LocallyIntegrable g
        (volume : Measure (TorusCharacters.LogSpace n)) := by
  rw [logarithmicCoverPushforward_eq_smul_volume]
  constructor
  · intro hg z
    obtain ⟨s, hs, hg⟩ := hg z
    refine ⟨s, hs, ?_⟩
    have hc :
        (logarithmicCoverJacobianFactor n : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr
        (logarithmicCoverJacobianFactor_pos n).ne'
    exact (integrable_smul_measure hc ENNReal.coe_ne_top).mp
      (by simpa [IntegrableOn, Measure.restrict_smul] using hg)
  · intro hg z
    obtain ⟨s, hs, hg⟩ := hg z
    refine ⟨s, hs, ?_⟩
    have hc :
        (logarithmicCoverJacobianFactor n : ℝ≥0∞) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr
        (logarithmicCoverJacobianFactor_pos n).ne'
    simpa [IntegrableOn, Measure.restrict_smul] using
      (integrable_smul_measure hc ENNReal.coe_ne_top).mpr hg
theorem complexTorusCoverLift_locallyIntegrable {n : ℕ}
    {g : WeightedTorusHilbert.LogTorus n → ℂ}
    (hg : LocallyIntegrable g (unweightedTorusMeasure n)) :
    LocallyIntegrable (complexTorusCoverLift g)
      (volume : Measure (TorusCharacters.LogSpace n)) := by
  apply (locallyIntegrable_logarithmicCoverPushforward_iff _).mp
  apply (locallyIntegrable_map_homeomorph
    (logarithmicCoordinatesEquiv n).toHomeomorph).mpr
  refine (realTorusCoverLift_locallyIntegrable hg).congr
    (Filter.Eventually.of_forall fun p => ?_)
  simp [complexTorusCoverLift,
    complexTorusCoverProjection, realTorusCoverLift]
end WeightedTorusDistributionBridge
namespace WeightedTorusGraphWeakBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge
open WeightedTorusDistributionBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
theorem exists_integer_translate_of_angularCoverProjection_eq
    {n : ℕ} {s t : Space n}
    (h : angularCoverProjection n s = angularCoverProjection n t) :
    ∃ q : Fin n → ℤ, s = fun i => t i + (q i : ℝ) := by
  have hi : ∀ i : Fin n,
      ∃ q : ℤ, s i = t i + (q : ℝ) := by
    intro i
    have he : ((s i : ℝ) : UnitAddCircle) =
        ((t i : ℝ) : UnitAddCircle) := congrFun h i
    have hz : (((s i - t i : ℝ) : UnitAddCircle) = 0) := by
      rw [AddCircle.coe_sub]
      exact sub_eq_zero.mpr he
    obtain ⟨q, hq⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    refine ⟨q, ?_⟩
    have hq' : (q : ℝ) = s i - t i := by
      simpa using hq
    linarith
  choose q hq using hi
  exact ⟨q, funext hq⟩
theorem angularCoverProjection_fundamentalRepresentative
    {n : ℕ} (t : Space n) :
    angularCoverProjection n
      (fun i : Fin n =>
        (AddCircle.equivIoc 1 0 ((t i : ℝ) : UnitAddCircle)).1) =
      angularCoverProjection n t := by
  funext i
  change
    (((AddCircle.equivIoc 1 0
      ((t i : ℝ) : UnitAddCircle)).1 : ℝ) : UnitAddCircle) =
      (t i : UnitAddCircle)
  exact (AddCircle.equivIoc 1 0).symm_apply_apply
    ((t i : ℝ) : UnitAddCircle)
theorem periodic_torusScalarRepresentative_logarithmicPoint {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (x t : Space n) :
    torusScalarRepresentative F
      (x, angularCoverProjection n t) =
      F (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) := by
  let u : Space n := fun i =>
    (AddCircle.equivIoc 1 0 ((t i : ℝ) : UnitAddCircle)).1
  obtain ⟨q, hq⟩ := exists_integer_translate_of_angularCoverProjection_eq
    (angularCoverProjection_fundamentalRepresentative t)
  change
    F (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
      x u) =
      F (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t)
  change u = (fun i => t i + (q i : ℝ)) at hq
  rw [hq, logarithmicPoint_integer_add]
  exact hperiod q _
theorem complexTorusCoverLift_torusScalarRepresentative_eq {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q)) :
    complexTorusCoverLift (torusScalarRepresentative F) = F := by
  funext z
  let p : Space n × Space n :=
    (logarithmicCoordinatesEquiv n).symm z
  have hp :
      JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        p.1 p.2 = z := by
    change (logarithmicCoordinatesEquiv n) p = z
    exact (logarithmicCoordinatesEquiv n).apply_symm_apply z
  rw [← hp, complexTorusCoverLift_logarithmicPoint]
  exact periodic_torusScalarRepresentative_logarithmicPoint
    F hperiod p.1 p.2
theorem barPartialCoordinate_periodic {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (j : Fin n) (q : Fin n → ℤ) :
    Function.Periodic (fun z => barPartialCoordinate F z j)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  have he :
      (fun w : TorusCharacters.LogSpace n =>
        F (w + TorusCharacters.imaginaryShift q)) = F :=
    funext (hperiod q)
  have hd := congrArg
    (fun G : TorusCharacters.LogSpace n → ℂ =>
      fderiv ℝ G z) he
  change
    fderiv ℝ
      (fun w : TorusCharacters.LogSpace n =>
        F (w + TorusCharacters.imaginaryShift q)) z =
      fderiv ℝ F z at hd
  rw [fderiv_comp_add_right] at hd
  unfold barPartialCoordinate
  change
    ((fderiv ℝ F (z + TorusCharacters.imaginaryShift q))
        (Pi.single j (1 : ℂ)) +
      Complex.I *
        (fderiv ℝ F (z + TorusCharacters.imaginaryShift q))
          (Pi.single j Complex.I)) / 2 =
      ((fderiv ℝ F z) (Pi.single j (1 : ℂ)) +
        Complex.I * (fderiv ℝ F z) (Pi.single j Complex.I)) / 2
  rw [hd]
end WeightedTorusGraphWeakBridge
namespace WeightedTorusClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff
def realFundamentalCellMeasure {n : ℕ} (b : Space n) :
    Measure (Space n × Space n) :=
  (volume : Measure (Space n)).prod
    ((volume : Measure (Space n)).restrict
      (angularFundamentalBox b))
def realWeightedFundamentalCellMeasure {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :
    Measure (Space n × Space n) :=
  (radialMeasure k φ).prod
    ((volume : Measure (Space n)).restrict
      (angularFundamentalBox b))
abbrev weightedCellScalarL2 {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :=
  MeasureTheory.Lp ℂ 2 (realWeightedFundamentalCellMeasure k φ b)
abbrev weightedCellFormL2 {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :=
  MeasureTheory.Lp (EuclideanSpace ℂ (Fin n)) 2
    (realWeightedFundamentalCellMeasure k φ b)
theorem realWeightedFundamentalCell_measurePreserving {n k : ℕ}
    (φ : Space n → ℝ) (b : Space n) :
    MeasurePreserving (realTorusCoverProjection n)
      (realWeightedFundamentalCellMeasure k φ b)
      (weightedTorusMeasure k φ) :=
  weightedRealTorusCoverProjection_measurePreserving φ b
def weightedScalarFundamentalLiftLI {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :
    weightedTorusScalarL2 k φ →ₗᵢ[ℂ] weightedCellScalarL2 k φ b :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (realTorusCoverProjection n)
    (realWeightedFundamentalCell_measurePreserving φ b)
def weightedFormFundamentalLiftLI {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n) :
    weightedTorusFormL2 k φ →ₗᵢ[ℂ] weightedCellFormL2 k φ b :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (realTorusCoverProjection n)
    (realWeightedFundamentalCell_measurePreserving φ b)
def weightedCellScalarAdjointFunctional {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n)
    (u : weightedCellScalarL2 k φ b) :
    functionDolbeaultGraphAmbient k φ →L[ℂ] ℂ :=
  ((innerSL ℂ u).comp
    (weightedScalarFundamentalLiftLI k φ b).toContinuousLinearMap).comp
      (WithLp.fstL 2 ℂ (weightedTorusScalarL2 k φ)
        (weightedTorusFormL2 k φ))
def weightedCellFormAdjointFunctional {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) (b : Space n)
    (u : weightedCellFormL2 k φ b) :
    functionDolbeaultGraphAmbient k φ →L[ℂ] ℂ :=
  ((innerSL ℂ u).comp
    (weightedFormFundamentalLiftLI k φ b).toContinuousLinearMap).comp
      (WithLp.sndL 2 ℂ (weightedTorusScalarL2 k φ)
        (weightedTorusFormL2 k φ))
theorem realWeightedFundamentalCellMeasure_eq_withDensity {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n) :
    realWeightedFundamentalCellMeasure k φ b =
      (realFundamentalCellMeasure b).withDensity
        (fun p : Space n × Space n =>
          radialWeight k φ p.1) := by
  unfold realWeightedFundamentalCellMeasure realFundamentalCellMeasure
    radialMeasure
  exact MeasureTheory.prod_withDensity_left
    (radialWeight_measurable k hφ)
theorem realFundamentalCellMeasure_isLocallyFinite {n : ℕ}
    (b : Space n) :
    IsLocallyFiniteMeasure (realFundamentalCellMeasure b) := by
  unfold realFundamentalCellMeasure
  infer_instance
theorem realWeightedFundamentalCellMeasure_isLocallyFinite {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n) :
    IsLocallyFiniteMeasure (realWeightedFundamentalCellMeasure k φ b) := by
  let : IsLocallyFiniteMeasure (realFundamentalCellMeasure b) :=
    realFundamentalCellMeasure_isLocallyFinite b
  rw [realWeightedFundamentalCellMeasure_eq_withDensity hφ b]
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (Real.continuous_exp.comp
      (continuous_const.mul (hφ.comp continuous_fst)))
def inverseRealCoverWeight {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ)
    (p : Space n × Space n) : ℂ :=
  (Real.exp ((k : ℝ) * φ p.1) : ℂ)
theorem continuous_inverseRealCoverWeight {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ) :
    Continuous (inverseRealCoverWeight k φ) := by
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (continuous_const.mul (hφ.comp continuous_fst)))
def weightedCellAdjointScalarTest {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ)
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (p : Space n × Space n) : ℂ :=
  inverseRealCoverWeight k φ p *
    coverAdjointScalarTest ψ j (logarithmicCoordinatesEquiv n p)
def weightedCellAdjointVectorTest {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ)
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (p : Space n × Space n) :
    EuclideanSpace ℂ (Fin n) :=
  inverseRealCoverWeight k φ p •
    coverAdjointVectorTest ψ j (logarithmicCoordinatesEquiv n p)
theorem continuous_weightedCellAdjointScalarTest {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (j : Fin n) :
    Continuous (weightedCellAdjointScalarTest k φ ψ j) := by
  exact (continuous_inverseRealCoverWeight hφ).mul
    ((continuous_coverAdjointScalarTest hψ j).comp
      (logarithmicCoordinatesEquiv n).continuous)
theorem continuous_weightedCellAdjointVectorTest {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (j : Fin n) :
    Continuous (weightedCellAdjointVectorTest k φ ψ j) := by
  exact (continuous_inverseRealCoverWeight hφ).smul
    ((continuous_coverAdjointVectorTest hψ.continuous j).comp
      (logarithmicCoordinatesEquiv n).continuous)
theorem compactSupport_weightedCellAdjointScalarTest {n k : ℕ}
    (φ : Space n → ℝ)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (weightedCellAdjointScalarTest k φ ψ j) := by
  have hcomp : HasCompactSupport
      (fun p : Space n × Space n =>
        coverAdjointScalarTest ψ j
          (logarithmicCoordinatesEquiv n p)) := by
    simpa [Function.comp_def] using
      (compactSupport_coverAdjointScalarTest hψcompact j).comp_homeomorph
        (logarithmicCoordinatesEquiv n).toHomeomorph
  exact hcomp.mul_left
theorem compactSupport_weightedCellAdjointVectorTest {n k : ℕ}
    (φ : Space n → ℝ)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (weightedCellAdjointVectorTest k φ ψ j) := by
  have hcomp : HasCompactSupport
      (fun p : Space n × Space n =>
        ψ (logarithmicCoordinatesEquiv n p)) := by
    simpa [Function.comp_def] using
      hψcompact.comp_homeomorph
        (logarithmicCoordinatesEquiv n).toHomeomorph
  refine hcomp.mono ?_
  intro p hp
  exact mt (fun h => by
    simp [weightedCellAdjointVectorTest, coverAdjointVectorTest, h]) hp
def weightedCellAdjointScalarL2 {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    weightedCellScalarL2 k φ b := by
  letI : IsLocallyFiniteMeasure
      (realWeightedFundamentalCellMeasure k φ b) :=
    realWeightedFundamentalCellMeasure_isLocallyFinite hφ b
  exact ((continuous_weightedCellAdjointScalarTest hφ hψ j).memLp_of_hasCompactSupport
      (μ := realWeightedFundamentalCellMeasure k φ b)
      (compactSupport_weightedCellAdjointScalarTest φ hψcompact j)).toLp
        (weightedCellAdjointScalarTest k φ ψ j)
def weightedCellAdjointVectorL2 {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    weightedCellFormL2 k φ b := by
  letI : IsLocallyFiniteMeasure
      (realWeightedFundamentalCellMeasure k φ b) :=
    realWeightedFundamentalCellMeasure_isLocallyFinite hφ b
  exact ((continuous_weightedCellAdjointVectorTest hφ hψ j).memLp_of_hasCompactSupport
      (μ := realWeightedFundamentalCellMeasure k φ b)
      (compactSupport_weightedCellAdjointVectorTest φ hψcompact j)).toLp
        (weightedCellAdjointVectorTest k φ ψ j)
def weightedCellWeakAdjointFunctional {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    functionDolbeaultGraphAmbient k φ →L[ℂ] ℂ :=
  weightedCellScalarAdjointFunctional k φ b
    (weightedCellAdjointScalarL2 hφ b hψ hψcompact j) +
  weightedCellFormAdjointFunctional k φ b
    (weightedCellAdjointVectorL2 hφ b hψ hψcompact j)
def coverFundamentalCell {n : ℕ} (b : Space n) :
    Set (TorusCharacters.LogSpace n) :=
  {z | ((logarithmicCoordinatesEquiv n).symm z).2 ∈ angularFundamentalBox b}
def angularFundamentalInterior {n : ℕ} (b : Space n) :
    Set (Space n) :=
  {t | ∀ i : Fin n, t i ∈ Set.Ioo (b i) (b i + 1)}
def coverFundamentalInterior {n : ℕ}
    (b : Space n) :
    Set (TorusCharacters.LogSpace n) :=
  {z | ((logarithmicCoordinatesEquiv n).symm z).2 ∈
    angularFundamentalInterior b}
def coverCenteredFundamentalBase {n : ℕ}
    (z : TorusCharacters.LogSpace n) : Space n :=
  fun i => ((logarithmicCoordinatesEquiv n).symm z).2 i - (1 / 2 : ℝ)
end WeightedTorusClosedGraphWeakBridge
namespace WeightedTorusVectorClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
def formCoordinateCLM {n : ℕ} (i : Fin n) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
  PiLp.proj 2 (fun _ : Fin n => ℂ) i
end WeightedTorusVectorClosedGraphWeakBridge
namespace WeightedTorusWeylRepresentativeBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open DolbeaultRegularity DolbeaultGraphDistributionBridge
def radialCoordinateKernel (w : ℂ) : ℝ :=
  Real.smoothTransition (1 - Complex.normSq w)
def productRadialKernel {n : ℕ}
    (w : TorusCharacters.LogSpace n) : ℝ :=
  ∏ i : Fin n, radialCoordinateKernel (w i)
def productRadialKernelMass (n : ℕ) : ℝ :=
  ∫ w : TorusCharacters.LogSpace n,
    productRadialKernel w
def normalizedProductRadialKernel {n : ℕ}
    (w : TorusCharacters.LogSpace n) : ℝ :=
  productRadialKernel w / productRadialKernelMass n
def productRadialHolomorphicMollification {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ) :
    TorusCharacters.LogSpace n → ℂ :=
  normalizedProductRadialKernel
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g
end WeightedTorusWeylRepresentativeBridge
namespace WeightedTorusWeylRadialIntegrationBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open WeightedTorusWeylRepresentativeBridge
def radialPolarIntegrand
    (f : ℂ → ℂ) (c : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) *
    ((radialCoordinateKernel (Complex.polarCoord.symm p) : ℂ) *
      f (c - Complex.polarCoord.symm p))
def compactPolarDomain : Set (ℝ × ℝ) :=
  Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi
def productRadialWeightedIntegrand {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (w : TorusCharacters.LogSpace n) : ℂ :=
  (productRadialKernel w : ℂ) * F w
def holomorphicCoordinateReset {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (i : Fin n) :
    TorusCharacters.LogSpace n → ℂ :=
  fun w => F (Function.update w i 0)
def holomorphicFinsetReset {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (s : Finset (Fin n)) :
    TorusCharacters.LogSpace n → ℂ :=
  fun w => F (fun i => if i ∈ s then 0 else w i)
end WeightedTorusWeylRadialIntegrationBridge
namespace WeightedTorusWeylWeakRepresentativeBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedBrascampSaturation DolbeaultRegularity ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusWeylRepresentativeBridge
open WeightedTorusWeylRadialIntegrationBridge
end WeightedTorusWeylWeakRepresentativeBridge
namespace ComplexMatrixWeightedHilbert
open Set Function MeasureTheory Filter Matrix
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace
  MatrixOrder Matrix.Norms.L2Operator Topology
def sourceMatrixHessian {n : ℕ}
    (φ : Space n → ℝ) :
    Space n → Matrix (Fin n) (Fin n) ℝ :=
  BergmanAsymptotics.actualHessianMatrix φ
end ComplexMatrixWeightedHilbert
namespace MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
def angularSmoothPartitionBump (t : ℝ) : ℝ :=
  Real.smoothTransition (t + 1) - Real.smoothTransition t
def angularSmoothPartition {n : ℕ} (t : Space n) : ℝ :=
  ∏ i : Fin n, angularSmoothPartitionBump (t i)
theorem continuous_angularCoverProjection
    (n : ℕ) :
    Continuous (angularCoverProjection n) := by
  unfold angularCoverProjection
  fun_prop
def binaryAngularFundamentalBase {n : ℕ}
    (q : Fin n → Bool) : Space n :=
  fun i => if q i then (-1 : ℝ) else 0
def matrixSourceCoverPotential {n : ℕ}
    (φ : Space n → ℝ)
    (z : TorusCharacters.LogSpace n) : ℝ :=
  φ ((logarithmicCoordinatesEquiv n).symm z).1
theorem contDiff_matrixSourceCoverPotential
    {n : ℕ} {m : ℕ∞} {φ : Space n → ℝ}
    (hφ : ContDiff ℝ m φ) :
    ContDiff ℝ m (matrixSourceCoverPotential φ) := by
  unfold matrixSourceCoverPotential
  exact hφ.comp (by fun_prop)
theorem continuous_matrixSourceCoverPotential
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ) :
    Continuous (matrixSourceCoverPotential φ) := by
  unfold matrixSourceCoverPotential
  exact hφ.comp
    (continuous_fst.comp (logarithmicCoordinatesEquiv n).symm.continuous)
@[simp] theorem matrixSourceCoverPotential_logarithmicPoint
    {n : ℕ} (φ : Space n → ℝ)
    (x t : Space n) :
    matrixSourceCoverPotential φ
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) = φ x := by
  unfold matrixSourceCoverPotential
  rw [← logarithmicCoordinatesEquiv_apply,
    ContinuousLinearEquiv.symm_apply_apply]
def coverAngularSmoothPartition {n : ℕ}
    (z : TorusCharacters.LogSpace n) : ℝ :=
  angularSmoothPartition
    ((logarithmicCoordinatesEquiv n).symm z).2
@[simp] theorem coverAngularSmoothPartition_logarithmicPoint
    {n : ℕ} (x t : Space n) :
    coverAngularSmoothPartition
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) = angularSmoothPartition t := by
  unfold coverAngularSmoothPartition
  rw [← logarithmicCoordinatesEquiv_apply,
    ContinuousLinearEquiv.symm_apply_apply]
def partitionedRealCoverIntegrand {n : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (p : Space n × Space n) : ℂ :=
  (Real.exp (-φ p.1) : ℂ) *
    ((angularSmoothPartition p.2 : ℂ) *
      f (p.1, angularCoverProjection n p.2))
def unweightedSourceTorusIntegrand {n : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) : ℂ :=
  (Real.exp (-φ p.1) : ℂ) * f p
end MatrixTorusBochnerBridge
namespace MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
def binaryAngularPartitionSum (n : ℕ)
    (t : Space n) : ℝ :=
  ∑ q : Fin n → Bool,
    angularSmoothPartition (binaryAngularFundamentalBase q + t)
def derivativePartitionedRealCoverIntegrand {n : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (v : Space n)
    (p : Space n × Space n) : ℂ :=
  (Real.exp (-φ p.1) : ℂ) *
    (((fderiv ℝ (angularSmoothPartition (n := n)) p.2) v : ℂ) *
      f (p.1, angularCoverProjection n p.2))
def sourceCoverAngularLinear (n : ℕ) :
    TorusCharacters.LogSpace n →L[ℝ] Space n :=
  (ContinuousLinearMap.snd ℝ (Space n)
    (Space n)).comp
      (logarithmicCoordinatesEquiv n).symm.toContinuousLinearMap
theorem angularCoverProjection_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (angularCoverProjection n) := by
  change IsOpenQuotientMap
    (Pi.map (fun _ : Fin n =>
      (fun t : ℝ => (t : UnitAddCircle))))
  exact IsOpenQuotientMap.piMap
    (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)
theorem realTorusCoverProjection_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (realTorusCoverProjection n) := by
  change IsOpenQuotientMap
    (Prod.map (id : Space n → Space n)
      (angularCoverProjection n))
  exact IsOpenQuotientMap.id.prodMap
    (angularCoverProjection_isOpenQuotientMap n)
theorem complexTorusCoverProjection_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (complexTorusCoverProjection n) := by
  have h :=
    (realTorusCoverProjection_isOpenQuotientMap n).comp
      (logarithmicCoordinatesEquiv n).symm.toHomeomorph.isOpenQuotientMap
  change IsOpenQuotientMap
    (realTorusCoverProjection n ∘ (logarithmicCoordinatesEquiv n).symm)
  exact h
theorem continuous_torusScalarRepresentative_of_periodic
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Continuous F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q)) :
    Continuous (torusScalarRepresentative F) := by
  apply (complexTorusCoverProjection_isOpenQuotientMap n).continuous_comp_iff.mp
  have hrecover :=
    complexTorusCoverLift_torusScalarRepresentative_eq F hperiod
  have hcomp :
      (torusScalarRepresentative F ∘
        complexTorusCoverProjection n) = F := by
    funext z
    exact congrFun hrecover z
  rw [hcomp]
  exact hF
theorem continuous_complexTorusCoverProjection (n : ℕ) :
    Continuous (complexTorusCoverProjection n) :=
  (complexTorusCoverProjection_isOpenQuotientMap n).continuous
def sourceAngularCutoffLift {n : ℕ}
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  (coverAngularSmoothPartition z : ℂ) *
    f (complexTorusCoverProjection n z)
def sourceAngularDerivativeLift {n : ℕ}
    (f : WeightedTorusHilbert.LogTorus n → ℂ)
    (v : TorusCharacters.LogSpace n)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  ((fderiv ℝ (coverAngularSmoothPartition (n := n)) z) v : ℂ) *
    f (complexTorusCoverProjection n z)
theorem fderiv_periodic
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (q : Fin n → ℤ) :
    Function.Periodic (fderiv ℝ F)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  have he :
      (fun w : TorusCharacters.LogSpace n =>
        F (w + TorusCharacters.imaginaryShift q)) = F :=
    funext (hperiod q)
  have hd := congrArg
    (fun G : TorusCharacters.LogSpace n → ℂ =>
      fderiv ℝ G z) he
  change
    fderiv ℝ
      (fun w : TorusCharacters.LogSpace n =>
        F (w + TorusCharacters.imaginaryShift q)) z =
      fderiv ℝ F z at hd
  rw [fderiv_comp_add_right] at hd
  exact hd
theorem holomorphicCoordinate_periodic
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (j : Fin n) (q : Fin n → ℤ) :
    Function.Periodic (fun z => holomorphicCoordinate F z j)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  change
    holomorphicCoordinate F
      (z + TorusCharacters.imaginaryShift q) j =
    holomorphicCoordinate F z j
  unfold holomorphicCoordinate
  rw [fderiv_periodic F hperiod q z]
theorem matrixSourceCoverPotential_periodic
    {n : ℕ} (φ : Space n → ℝ)
    (q : Fin n → ℤ) :
    Function.Periodic (matrixSourceCoverPotential φ)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  change
    φ (complexTorusCoverProjection n
      (z + TorusCharacters.imaginaryShift q)).1 =
    φ (complexTorusCoverProjection n z).1
  rw [complexTorusCoverProjection_imaginaryShift]
theorem conj_holomorphicCoordinate_real
    {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    conj (holomorphicCoordinate (fun w => (ψ w : ℂ)) z j) =
      barPartialCoordinate (fun w => (ψ w : ℂ)) z j := by
  unfold holomorphicCoordinate barPartialCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hψ z (Pi.single j (1 : ℂ)),
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hψ z (Pi.single j Complex.I)]
  simp only [map_div₀, map_sub, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring
theorem conj_barPartialCoordinate_real
    {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    conj (barPartialCoordinate (fun w => (ψ w : ℂ)) z j) =
      holomorphicCoordinate (fun w => (ψ w : ℂ)) z j := by
  have h := congrArg conj (conj_holomorphicCoordinate_real hψ z j)
  simpa using h.symm
theorem directionalDerivative_periodic
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (v : TorusCharacters.LogSpace n)
    (q : Fin n → ℤ) :
    Function.Periodic
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  exact congrArg
    (fun A : TorusCharacters.LogSpace n →L[ℝ] ℂ => A v)
    (fderiv_periodic F hperiod q z)
def torusDirectionalDerivativeRepresentative
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (v : TorusCharacters.LogSpace n) :
    WeightedTorusHilbert.LogTorus n → ℂ :=
  torusScalarRepresentative
    (fun z : TorusCharacters.LogSpace n =>
      (fderiv ℝ F z) v)
theorem tsupport_torusDirectionalDerivativeRepresentative_subset
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (v : TorusCharacters.LogSpace n) :
    tsupport (torusDirectionalDerivativeRepresentative F v) ⊆
      tsupport (torusScalarRepresentative F) := by
  apply closure_minimal
    (t := tsupport (torusScalarRepresentative F))
    ?_ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  obtain ⟨z, hz⟩ :=
    (complexTorusCoverProjection_isOpenQuotientMap n).surjective p
  let g : WeightedTorusHilbert.LogTorus n → ℂ :=
    torusScalarRepresentative F
  have hsubset :
      tsupport (complexTorusCoverLift g) ⊆
        (complexTorusCoverProjection n) ⁻¹' tsupport g := by
    have hlift : complexTorusCoverLift g =
        g ∘ complexTorusCoverProjection n := by
      funext z
      rfl
    rw [hlift]
    exact tsupport_comp_subset_preimage g
      (continuous_complexTorusCoverProjection n)
  have hnot : z ∉ tsupport (complexTorusCoverLift g) := by
    intro h
    apply hn
    have hp' := hsubset h
    simpa [g, hz] using hp'
  have hrec : complexTorusCoverLift g = F :=
    complexTorusCoverLift_torusScalarRepresentative_eq F hperiod
  have hderzero : fderiv ℝ F z = 0 := by
    rw [← hrec]
    exact fderiv_of_notMem_tsupport ℝ hnot
  have hrep := congrFun
    (complexTorusCoverLift_torusScalarRepresentative_eq
      (fun w : TorusCharacters.LogSpace n =>
        (fderiv ℝ F w) v)
      (fun q => directionalDerivative_periodic F hperiod v q)) z
  change torusDirectionalDerivativeRepresentative F v p ≠ 0 at hp
  change
    torusDirectionalDerivativeRepresentative F v
      (complexTorusCoverProjection n z) =
        (fderiv ℝ F z) v at hrep
  rw [hz] at hrep
  apply hp
  rw [hrep, hderzero]
  simp
theorem hasCompactSupport_torusDirectionalDerivativeRepresentative
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (v : TorusCharacters.LogSpace n) :
    HasCompactSupport (torusDirectionalDerivativeRepresentative F v) := by
  exact hcompact.of_isClosed_subset
    (isClosed_tsupport (torusDirectionalDerivativeRepresentative F v))
    (tsupport_torusDirectionalDerivativeRepresentative_subset
      F hperiod v)
def sourceTorusBarPartial
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n) : WeightedTorusHilbert.LogTorus n → ℂ :=
  torusScalarRepresentative
    (fun z => barPartialCoordinate F z j)
def sourceTorusHolomorphicDerivative
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n) : WeightedTorusHilbert.LogTorus n → ℂ :=
  torusScalarRepresentative
    (fun z => holomorphicCoordinate F z j)
theorem continuous_sourceTorusBarPartial
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (j : Fin n) :
    Continuous (sourceTorusBarPartial F j) := by
  unfold sourceTorusBarPartial
  exact continuous_torusScalarRepresentative_of_periodic
    (continuous_barPartialCoordinate
      (hF.of_le (by norm_num)) j)
    (fun q => barPartialCoordinate_periodic F hperiod j q)
theorem hasCompactSupport_sourceTorusBarPartial
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (j : Fin n) :
    HasCompactSupport (sourceTorusBarPartial F j) := by
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  have hs : HasCompactSupport
      (fun p : WeightedTorusHilbert.LogTorus n =>
        torusDirectionalDerivativeRepresentative F v₀ p +
          Complex.I *
            torusDirectionalDerivativeRepresentative F v₁ p) := by
    exact (hasCompactSupport_torusDirectionalDerivativeRepresentative
      F hperiod hcompact v₀).add
      ((hasCompactSupport_torusDirectionalDerivativeRepresentative
        F hperiod hcompact v₁).mul_left)
  have hp := hs.mul_right
    (f' := fun _ : WeightedTorusHilbert.LogTorus n =>
      ((2 : ℂ)⁻¹))
  change HasCompactSupport
    (fun p : WeightedTorusHilbert.LogTorus n =>
      (torusDirectionalDerivativeRepresentative F v₀ p +
        Complex.I * torusDirectionalDerivativeRepresentative F v₁ p) *
        ((2 : ℂ)⁻¹)) at hp
  have hfunction :
      (fun p : WeightedTorusHilbert.LogTorus n =>
        (torusDirectionalDerivativeRepresentative F v₀ p +
          Complex.I * torusDirectionalDerivativeRepresentative F v₁ p) *
          ((2 : ℂ)⁻¹)) = sourceTorusBarPartial F j := by
    funext p
    change
      ((fderiv ℝ F _) (Pi.single j (1 : ℂ)) +
        Complex.I * (fderiv ℝ F _) (Pi.single j Complex.I)) *
          ((2 : ℂ)⁻¹) =
        ((fderiv ℝ F _) (Pi.single j (1 : ℂ)) +
          Complex.I * (fderiv ℝ F _) (Pi.single j Complex.I)) / 2
    exact (div_eq_mul_inv _ _).symm
  rw [hfunction] at hp
  exact hp
theorem hasCompactSupport_sourceTorusHolomorphicDerivative
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (j : Fin n) :
    HasCompactSupport (sourceTorusHolomorphicDerivative F j) := by
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  have hs : HasCompactSupport
      (fun p : WeightedTorusHilbert.LogTorus n =>
        torusDirectionalDerivativeRepresentative F v₀ p -
          Complex.I *
            torusDirectionalDerivativeRepresentative F v₁ p) := by
    exact (hasCompactSupport_torusDirectionalDerivativeRepresentative
      F hperiod hcompact v₀).sub
      ((hasCompactSupport_torusDirectionalDerivativeRepresentative
        F hperiod hcompact v₁).mul_left)
  have hp := hs.mul_right
    (f' := fun _ : WeightedTorusHilbert.LogTorus n =>
      ((2 : ℂ)⁻¹))
  change HasCompactSupport
    (fun p : WeightedTorusHilbert.LogTorus n =>
      (torusDirectionalDerivativeRepresentative F v₀ p -
        Complex.I * torusDirectionalDerivativeRepresentative F v₁ p) *
        ((2 : ℂ)⁻¹)) at hp
  have hfunction :
      (fun p : WeightedTorusHilbert.LogTorus n =>
        (torusDirectionalDerivativeRepresentative F v₀ p -
          Complex.I * torusDirectionalDerivativeRepresentative F v₁ p) *
          ((2 : ℂ)⁻¹)) = sourceTorusHolomorphicDerivative F j := by
    funext p
    change
      ((fderiv ℝ F _) (Pi.single j (1 : ℂ)) -
        Complex.I * (fderiv ℝ F _) (Pi.single j Complex.I)) *
          ((2 : ℂ)⁻¹) =
        ((fderiv ℝ F _) (Pi.single j (1 : ℂ)) -
          Complex.I * (fderiv ℝ F _) (Pi.single j Complex.I)) / 2
    exact (div_eq_mul_inv _ _).symm
  rw [hfunction] at hp
  exact hp
theorem hasCompactSupport_sourceTorusConj
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun p => conj (f p)) := by
  apply hf.mono
  intro p hp
  change conj (f p) ≠ 0 at hp
  change f p ≠ 0
  intro hzero
  apply hp
  rw [hzero, map_zero]
def sourceTorusFormMixedDerivativeDensity
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    sourceTorusBarPartial (fun z => W z i) j p *
      conj (sourceTorusBarPartial (fun z => W z j) i p)
def sourceTorusFormFullDerivativeDensity
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    sourceTorusBarPartial (fun z => W z i) j p *
      conj (sourceTorusBarPartial (fun z => W z i) j p)
def sourceTorusFormExteriorDerivativeDensity
    {n : ℕ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) : ℂ :=
  (∑ i : Fin n, ∑ j : Fin n,
    (sourceTorusBarPartial (fun z => W z i) j p -
      sourceTorusBarPartial (fun z => W z j) i p) *
      conj
        (sourceTorusBarPartial (fun z => W z i) j p -
          sourceTorusBarPartial (fun z => W z j) i p)) / 2
end MatrixTorusBochnerIdentity
namespace MatrixTorusBochnerCore
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open ComplexMatrixWeightedHilbert MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
def sourceCoverRadialLinear (n : ℕ) :
    TorusCharacters.LogSpace n →L[ℝ] Space n :=
  (ContinuousLinearMap.fst ℝ
    (Space n) (Space n)).comp
    (logarithmicCoordinatesEquiv n).symm.toContinuousLinearMap
@[simp] theorem sourceCoverRadialLinear_apply
    {n : ℕ} (z : TorusCharacters.LogSpace n)
    (i : Fin n) :
    sourceCoverRadialLinear n z i = 2 * (z i).re := by
  rfl
theorem sourceCoverRadialLinear_single_one
    {n : ℕ} (j : Fin n) :
    sourceCoverRadialLinear n (Pi.single j (1 : ℂ)) =
      (2 : ℝ) • (Pi.single j (1 : ℝ) : Space n) := by
  funext i
  by_cases h : i = j
  · subst i
    simp [sourceCoverRadialLinear_apply]
  · simp [sourceCoverRadialLinear_apply, h]
theorem sourceCoverRadialLinear_single_I
    {n : ℕ} (j : Fin n) :
    sourceCoverRadialLinear n (Pi.single j Complex.I) = 0 := by
  funext i
  by_cases h : i = j
  · subst i
    simp [sourceCoverRadialLinear_apply]
  · simp [sourceCoverRadialLinear_apply, h]
theorem fderiv_sourceCoverRadialComp_apply
    {n : ℕ}
    {ψ : Space n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun w : TorusCharacters.LogSpace n =>
        ψ (sourceCoverRadialLinear n w)) z) v =
      (fderiv ℝ ψ (sourceCoverRadialLinear n z))
        (sourceCoverRadialLinear n v) := by
  have hd := (hψ (sourceCoverRadialLinear n z)).hasFDerivAt.comp z
    (sourceCoverRadialLinear n).hasFDerivAt
  have hp := congrArg
    (fun A : TorusCharacters.LogSpace n →L[ℝ] ℝ => A v)
    hd.fderiv
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using hp
theorem fderiv_matrixSourceCoverPotential_apply
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (matrixSourceCoverPotential φ) z) v =
      (fderiv ℝ φ (sourceCoverRadialLinear n z))
        (sourceCoverRadialLinear n v) := by
  exact fderiv_sourceCoverRadialComp_apply hφ z v
theorem holomorphicCoordinate_matrixSourceCoverPotential
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ)
    (z : TorusCharacters.LogSpace n)
    (i : Fin n) :
    holomorphicCoordinate
      (fun w : TorusCharacters.LogSpace n =>
        (matrixSourceCoverPotential φ w : ℂ)) z i =
      ((fderiv ℝ φ (sourceCoverRadialLinear n z))
        (Pi.single i (1 : ℝ)) : ℂ) := by
  have hrad : Differentiable ℝ (matrixSourceCoverPotential φ) := by
    exact hφ.comp (sourceCoverRadialLinear n).differentiable
  unfold holomorphicCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hrad z (Pi.single i (1 : ℂ)),
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hrad z (Pi.single i Complex.I),
    fderiv_matrixSourceCoverPotential_apply hφ,
    fderiv_matrixSourceCoverPotential_apply hφ,
    sourceCoverRadialLinear_single_one,
    sourceCoverRadialLinear_single_I]
  simp
theorem contDiff_sourceRealDirectional
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (i : Fin n) :
    ContDiff ℝ 1
      (fun x : Space n =>
        (fderiv ℝ φ x) (Pi.single i (1 : ℝ))) := by
  have hp : ContDiff ℝ 1
      (fun q : Space n × Space n =>
        (fderiv ℝ φ q.1) q.2) :=
    hφ.contDiff_fderiv_apply (by norm_num)
  exact hp.comp (contDiff_id.prodMk contDiff_const)
theorem barPartialCoordinate_sourceCoverRadialComp
    {n : ℕ}
    {ψ : Space n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate
      (fun w : TorusCharacters.LogSpace n =>
        (ψ (sourceCoverRadialLinear n w) : ℂ)) z j =
      ((fderiv ℝ ψ (sourceCoverRadialLinear n z))
        (Pi.single j (1 : ℝ)) : ℂ) := by
  have hrad : Differentiable ℝ
      (fun w : TorusCharacters.LogSpace n =>
        ψ (sourceCoverRadialLinear n w)) :=
    hψ.comp (sourceCoverRadialLinear n).differentiable
  unfold barPartialCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hrad z (Pi.single j (1 : ℂ)),
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hrad z (Pi.single j Complex.I),
    fderiv_sourceCoverRadialComp_apply hψ,
    fderiv_sourceCoverRadialComp_apply hψ,
    sourceCoverRadialLinear_single_one,
    sourceCoverRadialLinear_single_I]
  simp
theorem complexHessian_matrixSourceCoverPotential_eq_real_transpose
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    complexHessian (matrixSourceCoverPotential φ) z i j =
      (sourceMatrixHessian φ
        (sourceCoverRadialLinear n z) j i : ℂ) := by
  let g : Space n → ℝ :=
    fun x => (fderiv ℝ φ x) (Pi.single i (1 : ℝ))
  have hg : Differentiable ℝ g :=
    (contDiff_sourceRealDirectional hφ i).differentiable
      (by norm_num)
  have hhol :
      (fun w : TorusCharacters.LogSpace n =>
        holomorphicCoordinate
          (fun ξ => (matrixSourceCoverPotential φ ξ : ℂ)) w i) =
      (fun w : TorusCharacters.LogSpace n =>
        (g (sourceCoverRadialLinear n w) : ℂ)) := by
    funext w
    exact holomorphicCoordinate_matrixSourceCoverPotential
      (hφ.differentiable (by norm_num)) w i
  unfold complexHessian
  rw [hhol, barPartialCoordinate_sourceCoverRadialComp hg z j]
  change
    ((fderiv ℝ
      (fun x : Space n =>
        (fderiv ℝ φ x) (Pi.single i (1 : ℝ)))
      (sourceCoverRadialLinear n z))
        (Pi.single j (1 : ℝ)) : ℂ) =
      (sourceMatrixHessian φ
        (sourceCoverRadialLinear n z) j i : ℂ)
  rw [WeightedBochner.fderiv_coordinate_eval
    hφ (sourceCoverRadialLinear n z)
    (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))]
  unfold sourceMatrixHessian
    BergmanAsymptotics.actualHessianMatrix
  rw [LinearMap.toMatrix₂'_apply]
  rfl
theorem sourceMatrixHessian_entry_symm
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (x : Space n)
    (i j : Fin n) :
    sourceMatrixHessian φ x i j =
      sourceMatrixHessian φ x j i := by
  unfold sourceMatrixHessian
    BergmanAsymptotics.actualHessianMatrix
  rw [LinearMap.toMatrix₂'_apply,
    LinearMap.toMatrix₂'_apply]
  change
    ((fderiv ℝ (fderiv ℝ φ) x)
      (Pi.single i (1 : ℝ))) (Pi.single j (1 : ℝ)) =
      ((fderiv ℝ (fderiv ℝ φ) x)
        (Pi.single j (1 : ℝ))) (Pi.single i (1 : ℝ))
  exact (hφ.contDiffAt.isSymmSndFDerivAt
    (by norm_num)).eq (Pi.single i (1 : ℝ))
      (Pi.single j (1 : ℝ))
theorem complexHessian_matrixSourceCoverPotential_eq_real
    {n : ℕ}
    {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    complexHessian (matrixSourceCoverPotential φ) z i j =
      (sourceMatrixHessian φ
        (sourceCoverRadialLinear n z) i j : ℂ) := by
  rw [complexHessian_matrixSourceCoverPotential_eq_real_transpose
    hφ z i j,
    sourceMatrixHessian_entry_symm hφ
      (sourceCoverRadialLinear n z) j i]
end MatrixTorusBochnerCore
namespace MatrixTorusBochnerCoreDensity
open Set Function MeasureTheory Filter Matrix
open MatrixTorusBochnerCore WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
def sourceRadialCutoff {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) : ℝ :=
  growingBump m p.1
def sourceCoverRadialCutoff {n : ℕ} (m : ℕ)
    (z : TorusCharacters.LogSpace n) : ℝ :=
  growingBump m (sourceCoverRadialLinear n z)
theorem sourceRadialCutoff_hasCompactSupport
    {n : ℕ} (m : ℕ) :
    HasCompactSupport (sourceRadialCutoff (n := n) m) := by
  let K : Set (WeightedTorusHilbert.LogTorus n) :=
    tsupport (fun x : Space n => growingBump m x) ×ˢ
      (Set.univ : Set (TorusCharacters.AngularTorus n))
  have hK : IsCompact K :=
    (growingBump (n := n) m).hasCompactSupport.prod isCompact_univ
  apply HasCompactSupport.intro hK
  intro p hp
  have hrad :
      p.1 ∉ tsupport
        (fun x : Space n => growingBump m x) := by
    intro hx
    apply hp
    exact ⟨hx, Set.mem_univ p.2⟩
  change growingBump m p.1 = 0
  exact image_eq_zero_of_notMem_tsupport hrad
theorem contDiff_sourceCoverRadialCutoff
    {n : ℕ} (m : ℕ) :
    ContDiff ℝ 2 (sourceCoverRadialCutoff (n := n) m) := by
  exact (growingBump (n := n) m).contDiff.comp
    (sourceCoverRadialLinear n).contDiff
theorem sourceCoverRadialLinear_imaginaryShift
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (q : Fin n → ℤ) :
    sourceCoverRadialLinear n
        (z + TorusCharacters.imaginaryShift q) =
      sourceCoverRadialLinear n z := by
  funext i
  simp [sourceCoverRadialLinear_apply,
    TorusCharacters.imaginaryShift, Complex.mul_re]
theorem sourceCoverRadialCutoff_periodic
    {n : ℕ} (m : ℕ) (q : Fin n → ℤ) :
    Function.Periodic (sourceCoverRadialCutoff (n := n) m)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  simp [sourceCoverRadialCutoff,
    sourceCoverRadialLinear_imaginaryShift]
end MatrixTorusBochnerCoreDensity
namespace MatrixTorusBochnerCoreApproximation
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
def complexSourceCoverRadialCutoff {n : ℕ} (m : ℕ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  (sourceCoverRadialCutoff m z : ℂ)
theorem contDiff_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ) :
    ContDiff ℝ 2 (complexSourceCoverRadialCutoff (n := n) m) := by
  change ContDiff ℝ 2
    (Complex.ofRealCLM ∘ sourceCoverRadialCutoff (n := n) m)
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_sourceCoverRadialCutoff m)
theorem complexSourceCoverRadialCutoff_periodic
    {n : ℕ} (m : ℕ) (q : Fin n → ℤ) :
    Function.Periodic (complexSourceCoverRadialCutoff (n := n) m)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  exact congrArg Complex.ofReal
    (sourceCoverRadialCutoff_periodic m q z)
theorem torusScalarRepresentative_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    torusScalarRepresentative
      (complexSourceCoverRadialCutoff (n := n) m) p =
      (sourceRadialCutoff m p : ℂ) := by
  unfold torusScalarRepresentative
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
    complexSourceCoverRadialCutoff sourceCoverRadialCutoff
    sourceRadialCutoff
  congr 2
  funext i
  simp [sourceCoverRadialLinear_apply, Complex.mul_re]
  ring
theorem complexSourceRadialCutoff_hasCompactSupport
    {n : ℕ} (m : ℕ) :
    HasCompactSupport
      (fun p : WeightedTorusHilbert.LogTorus n =>
        (sourceRadialCutoff m p : ℂ)) := by
  apply (sourceRadialCutoff_hasCompactSupport m).mono
  intro p hp
  change (sourceRadialCutoff m p : ℂ) ≠ 0 at hp
  change sourceRadialCutoff m p ≠ 0
  intro hzero
  apply hp
  simp [hzero]
def cutoffPhysicalField {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (z : TorusCharacters.LogSpace n) :
    TorusCharacters.LogSpace n :=
  fun i => complexSourceCoverRadialCutoff m z * W z i
theorem contDiff_cutoffPhysicalField {n : ℕ} (m : ℕ)
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ContDiff ℝ 2 W) :
    ContDiff ℝ 2 (cutoffPhysicalField m W) := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_complexSourceCoverRadialCutoff m).mul
    (contDiff_pi.mp hW i)
theorem cutoffPhysicalField_periodic {n : ℕ} (m : ℕ)
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ∀ q : Fin n → ℤ,
      Function.Periodic W
        (TorusCharacters.imaginaryShift q))
    (q : Fin n → ℤ) :
    Function.Periodic (cutoffPhysicalField m W)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  funext i
  unfold cutoffPhysicalField
  rw [complexSourceCoverRadialCutoff_periodic m q z,
    congrFun (hW q z) i]
theorem torusScalarRepresentative_cutoffPhysicalField
    {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (i : Fin n)
    (p : WeightedTorusHilbert.LogTorus n) :
    torusScalarRepresentative
      (fun z => cutoffPhysicalField m W z i) p =
      (sourceRadialCutoff m p : ℂ) *
        torusScalarRepresentative (fun z => W z i) p := by
  rw [← torusScalarRepresentative_complexSourceCoverRadialCutoff m p]
  rfl
theorem cutoffPhysicalField_coordinate_hasCompactSupport
    {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (i : Fin n) :
    HasCompactSupport
      (torusScalarRepresentative
        (fun z => cutoffPhysicalField m W z i)) := by
  have hcompact :=
    (complexSourceRadialCutoff_hasCompactSupport (n := n) m).mul_right
      (f' := torusScalarRepresentative (fun z => W z i))
  have hfunction :
      torusScalarRepresentative
        (fun z => cutoffPhysicalField m W z i) =
      (fun p : WeightedTorusHilbert.LogTorus n =>
        (sourceRadialCutoff m p : ℂ) *
          torusScalarRepresentative (fun z => W z i) p) := by
    funext p
    exact torusScalarRepresentative_cutoffPhysicalField m W i p
  rw [hfunction]
  exact hcompact
theorem torusFormRepresentative_cutoffPhysicalField
    {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (p : WeightedTorusHilbert.LogTorus n) :
    torusFormRepresentative (cutoffPhysicalField m W) p =
      (sourceRadialCutoff m p : ℂ) •
        torusFormRepresentative W p := by
  ext i
  change torusScalarRepresentative
    (fun z => cutoffPhysicalField m W z i) p =
      (sourceRadialCutoff m p : ℂ) *
        torusScalarRepresentative (fun z => W z i) p
  exact torusScalarRepresentative_cutoffPhysicalField m W i p
theorem continuous_torusFormRepresentative_of_smooth_periodic
    {n : ℕ}
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (hWp : ∀ q : Fin n → ℤ,
      Function.Periodic W
        (TorusCharacters.imaginaryShift q)) :
    Continuous (torusFormRepresentative W) := by
  have hcoordinate (i : Fin n) :
      Continuous
        (torusScalarRepresentative (fun z => W z i)) := by
    apply continuous_torusScalarRepresentative_of_periodic
      (contDiff_pi.mp hW i).continuous
    intro q z
    exact congrFun (hWp q z) i
  change Continuous
    (fun p : WeightedTorusHilbert.LogTorus n =>
      WithLp.toLp 2
        (fun i : Fin n =>
          torusScalarRepresentative (fun z => W z i) p))
  exact (PiLp.continuous_toLp 2
    (fun _ : Fin n => ℂ)).comp
      (continuous_pi hcoordinate)
theorem continuous_sourceRadialCutoff
    {n : ℕ} (m : ℕ) :
    Continuous (sourceRadialCutoff (n := n) m) := by
  exact ((growingBump (n := n) m).contDiff
    (n := 2)).continuous.comp continuous_fst
theorem sourceRadialCutoff_nonneg
    {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    0 ≤ sourceRadialCutoff m p :=
  (growingBump (n := n) m).nonneg
theorem sourceRadialCutoff_le_one
    {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceRadialCutoff m p ≤ 1 :=
  (growingBump (n := n) m).le_one
theorem barPartialCoordinate_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate
      (complexSourceCoverRadialCutoff (n := n) m) z j =
      ((fderiv ℝ
        (fun x : Space n => growingBump m x)
        (sourceCoverRadialLinear n z))
          (Pi.single j (1 : ℝ)) : ℂ) := by
  exact barPartialCoordinate_sourceCoverRadialComp
    (((growingBump (n := n) m).contDiff
      (n := 1)).differentiable (by norm_num)) z j
theorem sourceTorusBarPartial_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ)
    (j : Fin n)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceTorusBarPartial
      (complexSourceCoverRadialCutoff (n := n) m) j p =
      ((fderiv ℝ
        (fun x : Space n => growingBump m x) p.1)
          (Pi.single j (1 : ℝ)) : ℂ) := by
  unfold sourceTorusBarPartial torusScalarRepresentative
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
  change
    barPartialCoordinate
      (complexSourceCoverRadialCutoff m)
      (fun i : Fin n =>
        (p.1 i : ℂ) / 2 +
          (2 * (Real.pi : ℂ) * Complex.I) *
            ((AddCircle.equivIoc 1 0 (p.2 i)).1 : ℂ))
      j = _
  rw [barPartialCoordinate_complexSourceCoverRadialCutoff]
  have hrad :
      sourceCoverRadialLinear n
        (fun i : Fin n =>
          (p.1 i : ℂ) / 2 +
            (2 * (Real.pi : ℂ) * Complex.I) *
              ((AddCircle.equivIoc 1 0 (p.2 i)).1 : ℂ)) =
        p.1 := by
    funext i
    simp [sourceCoverRadialLinear_apply, Complex.mul_re]
    ring
  rw [hrad]
theorem torusScalarRepresentative_mul
    {n : ℕ}
    (F G : TorusCharacters.LogSpace n → ℂ)
    (p : WeightedTorusHilbert.LogTorus n) :
    torusScalarRepresentative (fun z => F z * G z) p =
      torusScalarRepresentative F p *
        torusScalarRepresentative G p := by
  rfl
end MatrixTorusBochnerCoreApproximation
namespace MatrixTorusBochnerCoreConvergence
open Set Function MeasureTheory Filter Matrix
open WeightedBrascampLieb EqualitySaturatingKillingPaths ComplexKillingSaturationBridge
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation WeightedResolventConstantCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
def complexEuclideanOuterProduct
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : EuclideanSpace ℂ ι)
    (w : EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 (fun ij : ι × κ => v ij.1 * w ij.2)
theorem complexEuclideanOuterProduct_norm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : EuclideanSpace ℂ ι)
    (w : EuclideanSpace ℂ κ) :
    ‖complexEuclideanOuterProduct v w‖ = ‖v‖ * ‖w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  calc
    ‖complexEuclideanOuterProduct v w‖ ^ 2 =
        ∑ ij : ι × κ,
          ‖(complexEuclideanOuterProduct v w) ij‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    _ = ∑ ij : ι × κ, ‖v ij.1‖ ^ 2 * ‖w ij.2‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro ij _
      change ‖v ij.1 * w ij.2‖ ^ 2 = _
      rw [norm_mul, mul_pow]
    _ = ∑ i : ι, ∑ j : κ, ‖v i‖ ^ 2 * ‖w j‖ ^ 2 :=
      Fintype.sum_prod_type _
    _ = (∑ i : ι, ‖v i‖ ^ 2) *
        (∑ j : κ, ‖w j‖ ^ 2) :=
      (Fintype.sum_mul_sum
        (fun i : ι => ‖v i‖ ^ 2)
        (fun j : κ => ‖w j‖ ^ 2)).symm
    _ = (‖v‖ * ‖w‖) ^ 2 := by
      rw [← EuclideanSpace.norm_sq_eq,
        ← EuclideanSpace.norm_sq_eq, mul_pow]
def sourceCutoffBarGradient {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun j : Fin n =>
    sourceTorusBarPartial
      (complexSourceCoverRadialCutoff m) j p)
theorem sourceCutoffBarGradient_norm_eq
    {n : ℕ} (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    ‖sourceCutoffBarGradient m p‖ =
      ‖euclideanGradient
        (fun x : Space n => growingBump m x) p.1‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _
  change
    ‖sourceTorusBarPartial
      (complexSourceCoverRadialCutoff m) j p‖ ^ 2 =
      ‖(fderiv ℝ
        (fun x : Space n => growingBump m x) p.1)
          (Pi.single j (1 : ℝ))‖ ^ 2
  rw [sourceTorusBarPartial_complexSourceCoverRadialCutoff,
    Complex.norm_real]
theorem sourceCutoffBarGradient_norm_le
    {n : ℕ} {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient
        (fun y : Space n => unitBump y) x‖ ≤ C)
    (m : ℕ)
    (p : WeightedTorusHilbert.LogTorus n) :
    ‖sourceCutoffBarGradient m p‖ ≤
      ((m : ℝ) + 1)⁻¹ * C := by
  rw [sourceCutoffBarGradient_norm_eq]
  exact growingBump_euclideanGradient_norm_le hC m p.1
def sourceCutoffDerivativeCommutator {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (p : WeightedTorusHilbert.LogTorus n) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun ij : Fin n × Fin n =>
    torusScalarRepresentative (fun z => W z ij.1) p *
      sourceTorusBarPartial
        (complexSourceCoverRadialCutoff m) ij.2 p)
theorem sourceCutoffDerivativeCommutator_eq_outerProduct
    {n : ℕ} (m : ℕ)
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (p : WeightedTorusHilbert.LogTorus n) :
    sourceCutoffDerivativeCommutator m W p =
      complexEuclideanOuterProduct
        (torusFormRepresentative W p)
        (sourceCutoffBarGradient m p) := by
  ext ij
  rfl
theorem continuous_sourceCutoffBarGradient
    {n : ℕ} (m : ℕ) :
    Continuous (sourceCutoffBarGradient (n := n) m) := by
  change Continuous
    (fun p : WeightedTorusHilbert.LogTorus n =>
      WithLp.toLp 2 (fun j : Fin n =>
        sourceTorusBarPartial
          (complexSourceCoverRadialCutoff m) j p))
  apply (PiLp.continuous_toLp 2
    (fun _ : Fin n => ℂ)).comp
  apply continuous_pi
  intro j
  exact continuous_sourceTorusBarPartial
    (contDiff_complexSourceCoverRadialCutoff m)
    (complexSourceCoverRadialCutoff_periodic m) j
theorem continuous_sourceCutoffDerivativeCommutator
    {n : ℕ} (m : ℕ)
    {W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (hWp : ∀ q : Fin n → ℤ,
      Function.Periodic W
        (TorusCharacters.imaginaryShift q)) :
    Continuous (sourceCutoffDerivativeCommutator m W) := by
  change Continuous
    (fun p : WeightedTorusHilbert.LogTorus n =>
      WithLp.toLp 2 (fun ij : Fin n × Fin n =>
        torusScalarRepresentative (fun z => W z ij.1) p *
          sourceTorusBarPartial
            (complexSourceCoverRadialCutoff m) ij.2 p))
  apply (PiLp.continuous_toLp 2
    (fun _ : Fin n × Fin n => ℂ)).comp
  apply continuous_pi
  intro ij
  apply (continuous_torusScalarRepresentative_of_periodic
    (contDiff_pi.mp hW ij.1).continuous
    (fun q z => congrFun (hWp q z) ij.1)).mul
  exact continuous_sourceTorusBarPartial
    (contDiff_complexSourceCoverRadialCutoff m)
    (complexSourceCoverRadialCutoff_periodic m) ij.2
end MatrixTorusBochnerCoreConvergence
namespace WeightedTorusDolbeault
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
def angularWeightedTorusDensity {n : ℕ}
    (a : LogTorus n → ℝ) (p : LogTorus n) : ℝ :=
  Real.exp (-a p)
def angularWeightedTorusMeasure {n : ℕ}
    (a : LogTorus n → ℝ) : Measure (LogTorus n) :=
  (sourceTorusBaseMeasure n).withDensity
    (fun p => ENNReal.ofReal (angularWeightedTorusDensity a p))
theorem continuous_angularWeightedTorusDensity {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a) :
    Continuous (angularWeightedTorusDensity a) :=
  Real.continuous_exp.comp ha.neg
theorem angularWeightedTorusMeasure_isLocallyFinite {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a) :
    IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (sourceTorusBaseMeasure n) := by
    simpa [sourceTorusBaseMeasure, unweightedTorusMeasure] using
      unweightedTorusMeasure_isLocallyFinite n
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_angularWeightedTorusDensity ha)
def angularCoverPotential {n : ℕ}
    (a : LogTorus n → ℝ) :
    TorusCharacters.LogSpace n → ℝ :=
  fun z => a (complexTorusCoverProjection n z)
theorem angularCoverPotential_periodic {n : ℕ}
    (a : LogTorus n → ℝ) (q : Fin n → ℤ) :
    Function.Periodic (angularCoverPotential a)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  simp [angularCoverPotential,
    complexTorusCoverProjection_imaginaryShift]
abbrev angularWeightedScalarL2 {n : ℕ}
    (a : LogTorus n → ℝ) :=
  MeasureTheory.Lp ℂ 2 (angularWeightedTorusMeasure a)
abbrev angularWeightedFormL2 {n : ℕ}
    (a : LogTorus n → ℝ) :=
  MeasureTheory.Lp (EuclideanSpace ℂ (Fin n)) 2
    (angularWeightedTorusMeasure a)
abbrev angularDolbeaultGraphAmbient {n : ℕ}
    (a : LogTorus n → ℝ) :=
  WithLp 2 (angularWeightedScalarL2 a × angularWeightedFormL2 a)
def angularScalarL2OfRepresentative {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    angularWeightedScalarL2 a :=
  hF.toLp (torusScalarRepresentative F)
def angularBarPartialL2OfRepresentative {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    angularWeightedFormL2 a :=
  hD.toLp (torusFunctionBarPartialRepresentative F)
def smoothAngularDolbeaultGraphSet {n : ℕ}
    (a : LogTorus n → ℝ) : Set (angularDolbeaultGraphAmbient a) :=
  {v | ∃ F : TorusCharacters.LogSpace n → ℂ,
    ContDiff ℝ 3 F ∧
    (∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q)) ∧
    HasCompactSupport (torusScalarRepresentative F) ∧
    ∃ hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a),
    ∃ hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a),
      v = WithLp.toLp 2
        (angularScalarL2OfRepresentative a F hF,
         angularBarPartialL2OfRepresentative a F hD)}
def angularDolbeaultGraph {n : ℕ}
    (a : LogTorus n → ℝ) :
    Submodule ℂ (angularDolbeaultGraphAmbient a) :=
  (Submodule.span ℂ (smoothAngularDolbeaultGraphSet a)).topologicalClosure
theorem angularDolbeaultGraph_isClosed {n : ℕ}
    (a : LogTorus n → ℝ) :
    IsClosed (angularDolbeaultGraph a :
      Set (angularDolbeaultGraphAmbient a)) :=
  Submodule.isClosed_topologicalClosure
    (Submodule.span ℂ (smoothAngularDolbeaultGraphSet a))
instance angularDolbeaultGraph_completeSpace {n : ℕ}
    (a : LogTorus n → ℝ) :
    CompleteSpace (angularDolbeaultGraph a) :=
  (angularDolbeaultGraph_isClosed a).completeSpace_coe
def angularWeakDolbeaultResolvent {n : ℕ}
    (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a) :
    angularDolbeaultGraph a :=
  (angularDolbeaultGraph a).orthogonalProjectionOnto
    (WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)))
end WeightedTorusDolbeault
namespace WeightedTorusBochner
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
def angularUnweightedTorusIntegrand {n : ℕ}
    (a : LogTorus n → ℝ) (f : LogTorus n → ℂ)
    (p : LogTorus n) : ℂ :=
  (angularWeightedTorusDensity a p : ℂ) * f p
theorem complexAngularCoverPotential_periodic {n : ℕ}
    (a : LogTorus n → ℝ) (q : Fin n → ℤ) :
    Function.Periodic
      (fun z : TorusCharacters.LogSpace n =>
        (angularCoverPotential a z : ℂ))
      (TorusCharacters.imaginaryShift q) := by
  intro z
  change
    (angularCoverPotential a
      (z + TorusCharacters.imaginaryShift q) : ℂ) =
      (angularCoverPotential a z : ℂ)
  rw [angularCoverPotential_periodic a q z]
theorem angularWeightedHolomorphicDerivative_periodic {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (j : Fin n) (q : Fin n → ℤ) :
    Function.Periodic
      (weightedHolomorphicDerivative (angularCoverPotential a) F j)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  have hFhol := holomorphicCoordinate_periodic F hperiod j q z
  have hahol := holomorphicCoordinate_periodic
    (fun w : TorusCharacters.LogSpace n =>
      (angularCoverPotential a w : ℂ))
    (complexAngularCoverPotential_periodic a) j q z
  change
    holomorphicCoordinate F
      (z + TorusCharacters.imaginaryShift q) j =
      holomorphicCoordinate F z j at hFhol
  change
    holomorphicCoordinate
      (fun w : TorusCharacters.LogSpace n =>
        (angularCoverPotential a w : ℂ))
      (z + TorusCharacters.imaginaryShift q) j =
      holomorphicCoordinate
        (fun w : TorusCharacters.LogSpace n =>
          (angularCoverPotential a w : ℂ)) z j at hahol
  unfold weightedHolomorphicDerivative
  rw [hFhol, hperiod q z, hahol]
theorem angularComplexHessian_periodic {n : ℕ}
    (a : LogTorus n → ℝ) (i j : Fin n) (q : Fin n → ℤ) :
    Function.Periodic
      (fun z : TorusCharacters.LogSpace n =>
        complexHessian (angularCoverPotential a) z i j)
      (TorusCharacters.imaginaryShift q) := by
  unfold complexHessian
  exact barPartialCoordinate_periodic
    (fun z : TorusCharacters.LogSpace n =>
      holomorphicCoordinate
        (fun w => (angularCoverPotential a w : ℂ)) z i)
    (fun r => holomorphicCoordinate_periodic
      (fun w : TorusCharacters.LogSpace n =>
        (angularCoverPotential a w : ℂ))
      (complexAngularCoverPotential_periodic a) i r)
    j q
def angularTorusWeightedHolomorphicDerivative {n : ℕ}
    (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n) : LogTorus n → ℂ :=
  torusScalarRepresentative
    (weightedHolomorphicDerivative (angularCoverPotential a) F j)
def angularTorusComplexHessian {n : ℕ}
    (a : LogTorus n → ℝ)
    (i j : Fin n) : LogTorus n → ℂ :=
  torusScalarRepresentative
    (fun z => complexHessian (angularCoverPotential a) z i j)
theorem continuous_angularTorusWeightedHolomorphicDerivative {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 2 (angularCoverPotential a))
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (j : Fin n) :
    Continuous (angularTorusWeightedHolomorphicDerivative a F j) := by
  unfold angularTorusWeightedHolomorphicDerivative
  exact continuous_torusScalarRepresentative_of_periodic
    (continuous_weightedHolomorphicDerivative
      (ha.of_le (by norm_num))
      (hF.of_le (by norm_num)) j)
    (fun q => angularWeightedHolomorphicDerivative_periodic
      a F hperiod j q)
theorem continuous_angularTorusComplexHessian {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 2 (angularCoverPotential a))
    (i j : Fin n) :
    Continuous (angularTorusComplexHessian a i j) := by
  unfold angularTorusComplexHessian
  exact continuous_torusScalarRepresentative_of_periodic
    (continuous_complexHessian ha i j)
    (fun q => angularComplexHessian_periodic a i j q)
theorem hasCompactSupport_angularTorusWeightedHolomorphicDerivative
    {n : ℕ} (a : LogTorus n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F))
    (j : Fin n) :
    HasCompactSupport (angularTorusWeightedHolomorphicDerivative a F j) := by
  have hh := hasCompactSupport_sourceTorusHolomorphicDerivative
    F hperiod hcompact j
  have hp := hcompact.mul_right
    (f' := sourceTorusHolomorphicDerivative
      (fun z : TorusCharacters.LogSpace n =>
        (angularCoverPotential a z : ℂ)) j)
  have hs := hh.sub hp
  change HasCompactSupport
    (fun q : LogTorus n =>
      sourceTorusHolomorphicDerivative F j q -
        torusScalarRepresentative F q *
          sourceTorusHolomorphicDerivative
            (fun z : TorusCharacters.LogSpace n =>
              (angularCoverPotential a z : ℂ)) j q) at hs
  have hfunction :
      (fun q : LogTorus n =>
        sourceTorusHolomorphicDerivative F j q -
          torusScalarRepresentative F q *
            sourceTorusHolomorphicDerivative
              (fun z : TorusCharacters.LogSpace n =>
                (angularCoverPotential a z : ℂ)) j q) =
        angularTorusWeightedHolomorphicDerivative a F j := by
    funext q
    rfl
  rw [hfunction] at hs
  exact hs
def angularTorusFormAdjoint {n : ℕ}
    (a : LogTorus n → ℝ)
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : LogTorus n) : ℂ :=
  ∑ i : Fin n,
    angularTorusWeightedHolomorphicDerivative a
      (fun z => W z i) i p
def angularTorusFormCurvatureDensity {n : ℕ}
    (a : LogTorus n → ℝ)
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (p : LogTorus n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (torusScalarRepresentative (fun z => W z i) p *
      angularTorusComplexHessian a i j p) *
        conj (torusScalarRepresentative (fun z => W z j) p)
theorem integrable_angularTorusWeightedHolomorphic_pair
    {n : ℕ} {a : LogTorus n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hF : ContDiff ℝ 2 F)
    (hG : ContDiff ℝ 2 G)
    (hFp : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hGp : ∀ q : Fin n → ℤ,
      Function.Periodic G (TorusCharacters.imaginaryShift q))
    (hGc : HasCompactSupport (torusScalarRepresentative G))
    (i j : Fin n) :
    Integrable
      (fun p : LogTorus n =>
        angularTorusWeightedHolomorphicDerivative a F i p *
          conj (angularTorusWeightedHolomorphicDerivative a G j p))
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  apply ((continuous_angularTorusWeightedHolomorphicDerivative
    ha2 hF hFp i).mul
      (Complex.continuous_conj.comp
        (continuous_angularTorusWeightedHolomorphicDerivative
          ha2 hG hGp j))).integrable_of_hasCompactSupport
  exact (hasCompactSupport_sourceTorusConj
    (hasCompactSupport_angularTorusWeightedHolomorphicDerivative
      a G hGp hGc j)).mul_left
end WeightedTorusBochner
namespace ComplexSaturatedKillingFieldBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedTorusHilbert WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open JointHolomorphicLaurentFourierCompatibility
def realFundamentalEmbedding (n : ℕ) :
    Space n × angularFundamentalCell n →
      Space n × Space n :=
  fun p => (p.1, p.2.1)
def weightOneZeroIndex {n : ℕ}
    (K : CenteredBody n) :
    LatticeAsymptotics.monomialIndex K 1 :=
  ⟨0, (LatticeAsymptotics.mem_monomialIndex_one_iff
    K 0).mpr rfl⟩
end ComplexSaturatedKillingFieldBridge
namespace WeightedTorusBrascampLieb
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open ComplexSaturatedKillingFieldBridge WeightedTorusWeylWeakRepresentativeBridge
open JointHolomorphicLaurentFourierCompatibility WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
def angularTorusComplexHessianMatrix {n : ℕ}
    (a : LogTorus n → ℝ) (p : LogTorus n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => angularTorusComplexHessian a i j p
theorem continuous_angularTorusComplexHessianMatrix {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 2 (angularCoverPotential a)) :
    Continuous (angularTorusComplexHessianMatrix a) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_angularTorusComplexHessian ha i j
theorem integrable_angularTorusFormAdjoint_mul_conj
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    Integrable
      (fun p : LogTorus n =>
        angularTorusFormAdjoint a W p *
          conj (angularTorusFormAdjoint a W p))
      (angularWeightedTorusMeasure a) := by
  have hpair (i j : Fin n) :
      Integrable
        (fun p : LogTorus n =>
          angularTorusWeightedHolomorphicDerivative a
            (fun z => W z i) i p *
            conj (angularTorusWeightedHolomorphicDerivative a
              (fun z => W z j) j p))
        (angularWeightedTorusMeasure a) :=
    integrable_angularTorusWeightedHolomorphic_pair
      ha ha2 (hW i) (hW j) (hWp i) (hWp j) (hWc j) i j
  have hsum :
      Integrable
        (fun p : LogTorus n =>
          ∑ i : Fin n, ∑ j : Fin n,
            angularTorusWeightedHolomorphicDerivative a
              (fun z => W z i) i p *
              conj (angularTorusWeightedHolomorphicDerivative a
                (fun z => W z j) j p))
        (angularWeightedTorusMeasure a) :=
    MeasureTheory.integrable_finsetSum Finset.univ
      (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
        (fun j _ => hpair i j))
  apply hsum.congr
  filter_upwards [] with p
  simp only [angularTorusFormAdjoint, map_sum,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
def angularScalarEmbeddingCLM {n : ℕ}
    (a : LogTorus n → ℝ) :
    angularWeightedScalarL2 a →L[ℂ]
      angularDolbeaultGraphAmbient a :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ
    (angularWeightedScalarL2 a)
    (angularWeightedFormL2 a)).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℂ
        (angularWeightedScalarL2 a)
        (angularWeightedFormL2 a))
def angularWeakScalarResolventCLM {n : ℕ}
    (a : LogTorus n → ℝ) :
    angularWeightedScalarL2 a →L[ℂ] angularWeightedScalarL2 a :=
  (WithLp.fstL 2 ℂ
    (angularWeightedScalarL2 a)
    (angularWeightedFormL2 a)).comp
      ((angularDolbeaultGraph a).starProjection.comp
        (angularScalarEmbeddingCLM a))
@[simp] theorem angularWeakScalarResolventCLM_apply {n : ℕ}
    (a : LogTorus n → ℝ) (f : angularWeightedScalarL2 a) :
    angularWeakScalarResolventCLM a f =
      WithLp.fst (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a) := rfl
def angularWeakResolventFixedSpace {n : ℕ}
    (a : LogTorus n → ℝ) :
    Submodule ℂ (angularWeightedScalarL2 a) :=
  LinearMap.eqLocus (angularWeakScalarResolventCLM a).toLinearMap 1
end WeightedTorusBrascampLieb
namespace ArbitraryBodyOneSidedAngularWeightedKernel
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation JetEnvelopeSlopeConvergence
open ComplexKillingSaturationBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
theorem radialWeightedTorusDensity_le_angular_of_upper
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (q : LogTorus n) :
    radialWeight 1 φ q.1 ≤
      ENNReal.ofReal (Real.exp C) *
        ENNReal.ofReal (angularWeightedTorusDensity a q) := by
  have hexp : Real.exp (-φ q.1) ≤
      Real.exp C * Real.exp (-a q) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hupper q]
  simpa [angularWeightedTorusDensity, radialWeight,
    ENNReal.ofReal_mul (Real.exp_pos C).le] using
    ENNReal.ofReal_le_ofReal hexp
theorem radialWeightedTorusMeasure_le_angular_of_upper
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    weightedTorusMeasure 1 φ ≤
      ENNReal.ofReal (Real.exp C) • angularWeightedTorusMeasure a := by
  rw [weightedTorusMeasure_eq_withDensity 1 hφ]
  change
    (sourceTorusBaseMeasure n).withDensity
        (fun q => radialWeight 1 φ q.1) ≤
      ENNReal.ofReal (Real.exp C) •
        (sourceTorusBaseMeasure n).withDensity
          (fun q => ENNReal.ofReal
            (angularWeightedTorusDensity a q))
  rw [← MeasureTheory.withDensity_smul'
    (ENNReal.ofReal (Real.exp C))
    (fun q : LogTorus n =>
      ENNReal.ofReal (angularWeightedTorusDensity a q))
    ENNReal.ofReal_ne_top]
  apply MeasureTheory.withDensity_mono
  filter_upwards [] with q
  simpa [Pi.smul_apply, smul_eq_mul] using
    radialWeightedTorusDensity_le_angular_of_upper hupper q
theorem memLp_radial_of_angular_upper
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    {f : LogTorus n → E}
    (hf : MemLp f 2 (angularWeightedTorusMeasure a)) :
    MemLp f 2 (weightedTorusMeasure 1 φ) :=
  hf.of_measure_le_smul ENNReal.ofReal_ne_top
    (radialWeightedTorusMeasure_le_angular_of_upper hφ hupper)
def angularToRadialLpOfUpper
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a)) :
    MeasureTheory.Lp E 2 (weightedTorusMeasure 1 φ) :=
  (memLp_radial_of_angular_upper hφ hupper
    (MeasureTheory.Lp.memLp f)).toLp f
def canonicalComplexLpTransfer {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ ν : Measure α}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : μ ≤ c • ν) :
    MeasureTheory.Lp E p ν →L[ℂ] MeasureTheory.Lp E p μ := by
  let L : MeasureTheory.Lp E p ν →L[ℝ] MeasureTheory.Lp E p μ :=
    MeasureTheory.Lp.LpToLpOfMeasureLeSMul hc h
  refine {toFun := L, map_add' := L.map_add, map_smul' := ?_, cont := L.cont}
  intro z f
  apply MeasureTheory.Lp.ext
  have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
  filter_upwards [
    MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul hc h (z • f),
    hac.ae_eq (MeasureTheory.Lp.coeFn_smul z f),
    MeasureTheory.Lp.coeFn_smul z (L f),
    MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul hc h f]
    with x hleft hsource hright hbase
  change L (z • f) x = (z • L f) x
  change L f x = f x at hbase
  rw [hleft, hsource, hright]
  change z • f x = z • L f x
  rw [hbase]
def angularToRadialLpCLMOfUpper
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a) →L[ℂ]
      MeasureTheory.Lp E 2 (weightedTorusMeasure 1 φ) :=
  canonicalComplexLpTransfer ENNReal.ofReal_ne_top
    (radialWeightedTorusMeasure_le_angular_of_upper hφ hupper)
@[simp] theorem angularToRadialLpCLMOfUpper_apply
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a)) :
    angularToRadialLpCLMOfUpper hφ hupper f =
      angularToRadialLpOfUpper hφ hupper f := rfl
@[simp] theorem angularToRadialLpOfUpper_zero
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    angularToRadialLpOfUpper hφ hupper
      (0 : MeasureTheory.Lp E 2
        (angularWeightedTorusMeasure a)) = 0 := by
  change angularToRadialLpCLMOfUpper hφ hupper 0 = 0
  exact map_zero _
def angularToRadialGraphAmbientCLMOfUpper
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    angularDolbeaultGraphAmbient a →L[ℂ]
      functionDolbeaultGraphAmbient 1 φ :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ
      (weightedTorusScalarL2 1 φ)
      (weightedTorusFormL2 1 φ)).symm.toContinuousLinearMap).comp
    (((angularToRadialLpCLMOfUpper
      (E := ℂ) hφ hupper).prodMap
      (angularToRadialLpCLMOfUpper
        (E := EuclideanSpace ℂ (Fin n)) hφ hupper)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ
        (angularWeightedScalarL2 a)
        (angularWeightedFormL2 a)).toContinuousLinearMap)
@[simp] theorem angularToRadialGraphAmbientCLMOfUpper_pair
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : angularWeightedScalarL2 a)
    (v : angularWeightedFormL2 a) :
    angularToRadialGraphAmbientCLMOfUpper hφ hupper
        (WithLp.toLp 2 (f, v)) =
      WithLp.toLp 2
        (angularToRadialLpOfUpper hφ hupper f,
         angularToRadialLpOfUpper hφ hupper v) := by
  simp [angularToRadialGraphAmbientCLMOfUpper,
    angularToRadialLpCLMOfUpper_apply]
end ArbitraryBodyOneSidedAngularWeightedKernel
namespace BergmanJetSpatialSmoothing
open Set Function Filter MeasureTheory
open TorusCharacters BergmanDiagonalBasisIndependence ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators Topology Convolution ContDiff
end BergmanJetSpatialSmoothing
namespace ArbitraryBodyOneSidedAngularResolventDefect
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity WeightedTorusDolbeault
open WeightedTorusBrascampLieb ArbitraryBodyOneSidedAngularWeightedKernel
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
theorem angularWeightedTorusMeasure_isFinite_of_integrable
    {n : ℕ} {a : LogTorus n → ℝ}
    (hintegrable :
      Integrable (angularWeightedTorusDensity a)
        (sourceTorusBaseMeasure n)) :
    IsFiniteMeasure (angularWeightedTorusMeasure a) := by
  unfold angularWeightedTorusMeasure
  exact isFiniteMeasure_withDensity_ofReal
    hintegrable.hasFiniteIntegral
theorem angularWeightedTorusDensity_integral_pos
    {n : ℕ} {a : LogTorus n → ℝ}
    (hintegrable :
      Integrable (angularWeightedTorusDensity a)
        (sourceTorusBaseMeasure n)) :
    0 < ∫ q : LogTorus n,
      angularWeightedTorusDensity a q
        ∂(sourceTorusBaseMeasure n) := by
  let : NeZero (sourceTorusBaseMeasure n) :=
    sourceTorusBaseMeasure_neZero n
  exact MeasureTheory.integral_exp_pos hintegrable
def sourceFreeAngularConstantL2
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (c : ℂ) : angularWeightedScalarL2 a :=
  (memLp_const c).toLp (fun _ : LogTorus n => c)
def sourceFreeAngularWeightedConstantSubmodule
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)] :
    Submodule ℂ (angularWeightedScalarL2 a) :=
  ℂ ∙ sourceFreeAngularConstantL2 a 1
def sourceFreeAngularWeightedMeanCLM
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)] :
    angularWeightedScalarL2 a →L[ℂ] ℂ :=
  innerSL ℂ (sourceFreeAngularConstantL2 a 1)
def sourceFreeAngularWeightedMeanZeroSubmodule
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)] :
    Submodule ℂ (angularWeightedScalarL2 a) :=
  (sourceFreeAngularWeightedMeanCLM a).ker
end ArbitraryBodyOneSidedAngularResolventDefect
namespace BergmanJetTorusCoercivity
open Set Function Filter MeasureTheory Metric
open SupportFunction MonomialIntegrability LatticeAsymptotics WeightedTorusHilbert
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentMoserTrudinger MomentWeakBergman
open BergmanJetTorusEnvelope BergmanJetMonomialEnvelopeLower WeightedTorusDolbeault
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology
def momentSignedUnitVector
    {n : ℕ} (k : ℕ) (σ : Fin n → Bool) : Space n :=
  fun i =>
    (if σ i = true then (1 : ℝ) else -1) / (k : ℝ)
theorem norm_momentSignedUnitVector_le
    {n : ℕ} {k : ℕ} (hk : 0 < k)
    (σ : Fin n → Bool) :
    ‖momentSignedUnitVector k σ‖ ≤
      (k : ℝ)⁻¹ := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (pi_norm_le_iff_of_nonneg
    (inv_nonneg.mpr hkreal.le)).mpr
  intro i
  unfold momentSignedUnitVector
  split_ifs <;> simp [div_eq_mul_inv]
theorem exists_momentSignedUnitMonomialDegree
    {n : ℕ} (K : CenteredBody n) :
    ∃ k : ℕ, 0 < k ∧
      ∀ σ : Fin n → Bool,
        momentSignedUnitVector k σ ∈
          monomialIndex K k := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior)
      (0 : Space n) (zero_mem_interior K)
  obtain ⟨k, hklarge⟩ := exists_nat_gt (1 / r)
  have hkinv : 0 < (1 / r : ℝ) := one_div_pos.mpr hr
  have hkreal : 0 < (k : ℝ) := lt_trans hkinv hklarge
  have hk : 0 < k := by exact_mod_cast hkreal
  have hradius : (k : ℝ)⁻¹ < r :=
    inv_lt_of_inv_lt₀ hr (by simpa only [one_div] using hklarge)
  refine ⟨k, hk, ?_⟩
  intro σ
  apply (mem_monomialIndex_iff K hk
    (momentSignedUnitVector k σ)).mpr
  constructor
  · apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt
      (norm_momentSignedUnitVector_le hk σ)
      hradius
  · intro i
    refine ⟨if σ i = true then (1 : ℤ) else -1, ?_⟩
    unfold momentSignedUnitVector
    split_ifs <;>
      simp [hkreal.ne', div_eq_mul_inv]
def momentCoerciveMonomialDegree
    {n : ℕ} (K : CenteredBody n) : ℕ :=
  (exists_momentSignedUnitMonomialDegree K).choose
theorem momentCoerciveMonomialDegree_pos
    {n : ℕ} (K : CenteredBody n) :
    0 < momentCoerciveMonomialDegree K :=
  (exists_momentSignedUnitMonomialDegree K).choose_spec.1
theorem momentSignedUnitVector_mem_monomialIndex
    {n : ℕ} (K : CenteredBody n)
    (σ : Fin n → Bool) :
    momentSignedUnitVector
        (momentCoerciveMonomialDegree K) σ ∈
      monomialIndex K (momentCoerciveMonomialDegree K) :=
  (exists_momentSignedUnitMonomialDegree K).choose_spec.2 σ
def momentCoerciveSignedMonomial
    {n : ℕ} (K : CenteredBody n)
    (σ : Fin n → Bool) :
    monomialIndex K (momentCoerciveMonomialDegree K) :=
  ⟨momentSignedUnitVector
      (momentCoerciveMonomialDegree K) σ,
    momentSignedUnitVector_mem_monomialIndex K σ⟩
def momentSignedMonomialLowerConstant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (σ : Fin n → Bool) : ℝ :=
  (exists_moment_fixedMonomial_torusEnvelope_lower
    K (momentCoerciveMonomialDegree_pos K)
    F htransport
    (momentCoerciveSignedMonomial K σ)).choose
theorem momentSignedMonomialLowerConstant_spec
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (σ : Fin n → Bool)
    (p : TorusCharacters.LogSpace n)
    (q : LogTorus n) {t : ℝ} (ht : 0 < t) :
    pairing (momentSignedUnitVector
      (momentCoerciveMonomialDegree K) σ) q.1 -
        momentSignedMonomialLowerConstant
          K F htransport σ ≤
      momentTorusEnvelopeTimeSlice
        K F htransport p q t := by
  exact
    (exists_moment_fixedMonomial_torusEnvelope_lower
      K (momentCoerciveMonomialDegree_pos K)
      F htransport
      (momentCoerciveSignedMonomial K σ)).choose_spec
        p q t ht
def momentTorusEnvelopeCoercivityConstant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) : ℝ :=
  ∑ σ : Fin n → Bool,
    |momentSignedMonomialLowerConstant
      K F htransport σ|
theorem momentSignedMonomialLowerConstant_le_coercivityConstant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (σ : Fin n → Bool) :
    momentSignedMonomialLowerConstant K F htransport σ ≤
      momentTorusEnvelopeCoercivityConstant K F htransport := by
  unfold momentTorusEnvelopeCoercivityConstant
  calc
    momentSignedMonomialLowerConstant K F htransport σ ≤
      |momentSignedMonomialLowerConstant
        K F htransport σ| :=
      le_abs_self _
    _ ≤ ∑ τ : Fin n → Bool,
      |momentSignedMonomialLowerConstant
        K F htransport τ| := by
      simpa using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin n → Bool)))
          (f := fun τ : Fin n → Bool =>
            |momentSignedMonomialLowerConstant
              K F htransport τ|)
          (fun τ _ => abs_nonneg _)
          (Finset.mem_univ σ))
def momentSpatialSign
    {n : ℕ} (x : Space n) : Fin n → Bool :=
  fun i => decide (0 ≤ x i)
theorem pairing_momentSignedUnitVector_spatialSign
    {n k : ℕ} (x : Space n) :
    pairing
      (momentSignedUnitVector k
        (momentSpatialSign x)) x =
      (k : ℝ)⁻¹ * ∑ i, |x i| := by
  classical
  unfold pairing momentSignedUnitVector momentSpatialSign
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ x i
  · simp [h, abs_of_nonneg h, div_eq_mul_inv]
  · have hnonpos : x i ≤ 0 := le_of_not_ge h
    simp [h, abs_of_nonpos hnonpos, div_eq_mul_inv]
theorem momentTorusEnvelope_norm_coercivity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : LogTorus n) {t : ℝ} (ht : 0 < t) :
    ((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹ *
          ‖q.1‖ -
        momentTorusEnvelopeCoercivityConstant K F htransport ≤
      momentTorusEnvelopeTimeSlice
        K F htransport p q t := by
  let σ := momentSpatialSign q.1
  have hsign := momentSignedMonomialLowerConstant_spec
    K F htransport σ p q ht
  have hconstant :=
    momentSignedMonomialLowerConstant_le_coercivityConstant
      K F htransport σ
  have hpair :=
    pairing_momentSignedUnitVector_spatialSign
      (k := momentCoerciveMonomialDegree K) q.1
  have hdegree :
      0 ≤
        (((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹) := by
    exact inv_nonneg.mpr
      (by exact_mod_cast
        (momentCoerciveMonomialDegree_pos K).le)
  have hnorm := mul_le_mul_of_nonneg_left
    (SupportFunction.norm_le_sum_abs q.1) hdegree
  dsimp [σ] at hsign
  rw [hpair] at hsign
  exact (sub_le_sub hnorm hconstant).trans hsign
theorem integrable_exp_neg_momentTorusEnvelopeTimeSlice_of_pos
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {t : ℝ} (ht : 0 < t) :
    Integrable
      (fun q : LogTorus n =>
        Real.exp
          (-momentTorusEnvelopeTimeSlice
            K F htransport p q t))
      (sourceTorusBaseMeasure n) := by
  let δ : ℝ :=
    ((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹
  let C : ℝ := momentTorusEnvelopeCoercivityConstant
    K F htransport
  have hδ : 0 < δ := by
    dsimp [δ]
    apply inv_pos.mpr
    exact_mod_cast momentCoerciveMonomialDegree_pos K
  have hrad :
      Integrable
        (fun x : Space n =>
          Real.exp (-δ * ‖x‖))
        (volume : Measure (Space n)) :=
    integrable_exp_neg_mul_norm_all hδ
  have hang :
      Integrable
        (fun _ : TorusCharacters.AngularTorus n =>
          (1 : ℝ))
        (angularMeasure n) :=
    integrable_const 1
  have hprod :
      Integrable
        (fun q : LogTorus n =>
          Real.exp (-δ * ‖q.1‖) * (1 : ℝ))
        (sourceTorusBaseMeasure n) := by
    simpa [sourceTorusBaseMeasure] using hrad.mul_prod hang
  have hmajor := hprod.const_mul (Real.exp C)
  have hmeas :
      AEStronglyMeasurable
        (fun q : LogTorus n =>
          Real.exp
            (-momentTorusEnvelopeTimeSlice
              K F htransport p q t))
        (sourceTorusBaseMeasure n) :=
    (Real.continuous_exp.measurable.comp
      (measurable_momentTorusEnvelopeTimeSlice
        K F htransport p t).neg).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with q
  change
    ‖Real.exp
        (-momentTorusEnvelopeTimeSlice
          K F htransport p q t)‖ ≤
      Real.exp C *
        (Real.exp (-δ * ‖q.1‖) * (1 : ℝ))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [mul_one]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcoerce :=
    momentTorusEnvelope_norm_coercivity
      K F htransport p q ht
  change
    δ * ‖q.1‖ - C ≤
      momentTorusEnvelopeTimeSlice
        K F htransport p q t at hcoerce
  simpa only [sub_eq_add_neg, neg_add_rev, neg_mul, neg_neg] using
    (neg_le_neg hcoerce)
theorem integrable_exp_neg_momentTorusEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (t : ℝ) :
    Integrable
      (fun q : LogTorus n =>
        Real.exp
          (-momentTorusEnvelopeTimeSlice
            K F htransport p q t))
      (sourceTorusBaseMeasure n) := by
  by_cases ht : 0 < t
  · exact
      integrable_exp_neg_momentTorusEnvelopeTimeSlice_of_pos
        K F htransport p ht
  · have hnonpos : t ≤ 0 := le_of_not_gt ht
    have hrad :=
      integrable_monomialWeight_momentNormalized_of_mem_interior
        F htransport (zero_mem_interior K)
        (k := (1 : ℝ)) zero_lt_one
    have hrad' :
        Integrable
          (fun x : Space n =>
            Real.exp (-momentNormalizedPotential F x))
          (volume : Measure (Space n)) := by
      apply hrad.congr
      filter_upwards [] with x
      simp [monomialWeight, SupportFunction.pairing]
    have hang :
        Integrable
          (fun _ : TorusCharacters.AngularTorus n =>
            (1 : ℝ))
          (angularMeasure n) :=
      integrable_const 1
    have hprod := hrad'.mul_prod hang
    change
      Integrable
        (fun q : LogTorus n =>
          Real.exp
            (-momentEnvelopeTimeSlice K F htransport p
              (sourceTorusCoverPoint q) t))
        (sourceTorusBaseMeasure n)
    have heq :
        (fun q : LogTorus n =>
          Real.exp
            (-momentEnvelopeTimeSlice K F htransport p
              (sourceTorusCoverPoint q) t)) =
        (fun q : LogTorus n =>
          Real.exp (-momentNormalizedPotential F q.1) *
            (1 : ℝ)) := by
      funext q
      rw [momentEnvelopeTimeSlice_of_nonpositive
        K F htransport p (sourceTorusCoverPoint q) hnonpos,
        JetEnvelopeRightDerivative.realLogCoordinate_sourceTorusCoverPoint]
      simp
    rw [heq]
    simpa [sourceTorusBaseMeasure] using hprod
theorem integrable_angularWeightedTorusDensity_momentEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (t : ℝ) :
    Integrable
      (angularWeightedTorusDensity
        (fun q : LogTorus n =>
          momentTorusEnvelopeTimeSlice
            K F htransport p q t))
      (sourceTorusBaseMeasure n) := by
  exact integrable_exp_neg_momentTorusEnvelopeTimeSlice
    K F htransport p t
theorem momentTorusEnvelopePartition_pos
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (t : ℝ) :
    0 < ∫ q : LogTorus n,
      Real.exp
        (-momentTorusEnvelopeTimeSlice
          K F htransport p q t)
        ∂(sourceTorusBaseMeasure n) := by
  exact angularWeightedTorusDensity_integral_pos
    (integrable_angularWeightedTorusDensity_momentEnvelope
      K F htransport p t)
end BergmanJetTorusCoercivity
namespace JetEnvelopeGlobalPlurisubharmonicClosure
open Set Filter Function MeasureTheory Metric
open ActualJetUpperEnvelope ActualJetPlurisubharmonicEnvelope ActualJetPlurisubharmonicClosure
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace
abbrev PositiveSourceJointComplexCover (n : ℕ) :=
  {q : SourceJointComplexCover n // 0 < sourceJointCoverTime q}
def sourcePositiveCoverExp {n : ℕ}
    (q : PositiveSourceJointComplexCover n) :
    PositiveJointLogSpace n :=
  sourceJointExpPositiveLift q.val q.property
def sourceJointCoverCirclePoint
    {n : ℕ} (q v : SourceJointComplexCover n)
    (R θ : ℝ) : SourceJointComplexCover n :=
  q + circleMap 0 R θ • v
theorem continuous_sourceJointCoverCirclePoint
    {n : ℕ} (q v : SourceJointComplexCover n) (R : ℝ) :
    Continuous (sourceJointCoverCirclePoint q v R) := by
  unfold sourceJointCoverCirclePoint
  fun_prop
theorem tendsto_sourceJointCoverCirclePoint
    {n : ℕ} (q : ℕ → SourceJointComplexCover n)
    (q₀ : SourceJointComplexCover n)
    (hq : Tendsto q atTop (𝓝 q₀))
    (v : SourceJointComplexCover n) (R θ : ℝ) :
    Tendsto
      (fun m : ℕ => sourceJointCoverCirclePoint (q m) v R θ)
      atTop
      (𝓝 (sourceJointCoverCirclePoint q₀ v R θ)) := by
  exact hq.add_const (circleMap 0 R θ • v)
theorem circleAverage_sourceJointCover_eq
    {n : ℕ} (u : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    Real.circleAverage
      (fun w : ℂ => u (q + w • v)) 0 R =
        (2 * Real.pi)⁻¹ *
          ∫ θ in 0..2 * Real.pi,
            u (sourceJointCoverCirclePoint q v R θ) := by
  rw [Real.circleAverage_def]
  rfl
theorem circleIntegrable_sourceJointCover_of_continuous
    {n : ℕ} (u : SourceJointComplexCover n → ℝ)
    (hu : Continuous u)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    CircleIntegrable
      (fun w : ℂ => u (q + w • v)) 0 R := by
  rw [circleIntegrable_def]
  exact (hu.comp
    (continuous_sourceJointCoverCirclePoint q v R)).intervalIntegrable
      0 (2 * Real.pi)
theorem circleIntegrable_sourceJointCover_of_upperSemicontinuous
    {n : ℕ} (u : SourceJointComplexCover n → ℝ)
    (hu : UpperSemicontinuous u)
    (q v : SourceJointComplexCover n) (R : ℝ)
    (L C : ℝ)
    (hbound : ∀ θ : ℝ,
      L ≤ u (sourceJointCoverCirclePoint q v R θ) ∧
        u (sourceJointCoverCirclePoint q v R θ) ≤ C) :
    CircleIntegrable
      (fun w : ℂ => u (q + w • v)) 0 R := by
  rw [circleIntegrable_def,
    intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le]
  change Integrable
    (fun θ : ℝ => u (sourceJointCoverCirclePoint q v R θ))
    (volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  have husc : UpperSemicontinuous
      (fun θ : ℝ =>
        u (sourceJointCoverCirclePoint q v R θ)) :=
    hu.comp (continuous_sourceJointCoverCirclePoint q v R)
  refine (integrable_const (|L| + |C|)).mono'
    husc.measurable.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [(hbound θ).1, neg_abs_le L, abs_nonneg C]
    · linarith [(hbound θ).2, le_abs_self C, abs_nonneg L]
theorem circleAverage_sourceJointCover_mono
    {n : ℕ} (f u : SourceJointComplexCover n → ℝ)
    (hf : Continuous f) (hu : UpperSemicontinuous u)
    (q v : SourceJointComplexCover n) (R : ℝ)
    (L C : ℝ)
    (hbound : ∀ θ : ℝ,
      L ≤ u (sourceJointCoverCirclePoint q v R θ) ∧
        u (sourceJointCoverCirclePoint q v R θ) ≤ C)
    (hle : ∀ z : SourceJointComplexCover n, f z ≤ u z) :
    Real.circleAverage
      (fun w : ℂ => f (q + w • v)) 0 R ≤
    Real.circleAverage
      (fun w : ℂ => u (q + w • v)) 0 R := by
  apply Real.circleAverage_mono
    (circleIntegrable_sourceJointCover_of_continuous f hf q v R)
    (circleIntegrable_sourceJointCover_of_upperSemicontinuous
      u hu q v R L C hbound)
  intro w _
  exact hle (q + w • v)
theorem tendsto_circleAverage_sourceJointCover_of_dominated
    {n : ℕ}
    (u : ℕ → SourceJointComplexCover n → ℝ)
    (u₀ : SourceJointComplexCover n → ℝ)
    (hu : ∀ r : ℕ, UpperSemicontinuous (u r))
    (hpoint : ∀ z : SourceJointComplexCover n,
      Tendsto (fun r : ℕ => u r z) atTop (𝓝 (u₀ z)))
    (q v : SourceJointComplexCover n) (R : ℝ)
    (L C : ℝ)
    (hbound : ∀ (r : ℕ) (θ : ℝ),
      L ≤ u r (sourceJointCoverCirclePoint q v R θ) ∧
        u r (sourceJointCoverCirclePoint q v R θ) ≤ C) :
    Tendsto
      (fun r : ℕ =>
        Real.circleAverage
          (fun w : ℂ => u r (q + w • v)) 0 R)
      atTop
      (𝓝 (Real.circleAverage
        (fun w : ℂ => u₀ (q + w • v)) 0 R)) := by
  have hγ := continuous_sourceJointCoverCirclePoint q v R
  have hdom :
      Tendsto
        (fun r : ℕ => ∫ θ,
          u r (sourceJointCoverCirclePoint q v R θ)
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))))
        atTop
        (𝓝 (∫ θ,
          u₀ (sourceJointCoverCirclePoint q v R θ)
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : ℝ => |L| + |C|)
    · intro r
      exact ((hu r).comp hγ).measurable.aestronglyMeasurable
    · exact integrable_const (|L| + |C|)
    · intro r
      exact Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs]
        apply abs_le.mpr
        constructor
        · linarith [(hbound r θ).1,
            neg_abs_le L, abs_nonneg C]
        · linarith [(hbound r θ).2,
            le_abs_self C, abs_nonneg L]
    · exact Filter.Eventually.of_forall fun θ =>
        hpoint (sourceJointCoverCirclePoint q v R θ)
  have hinter :
      Tendsto
        (fun r : ℕ =>
          ∫ θ in 0..2 * Real.pi,
            u r (sourceJointCoverCirclePoint q v R θ))
        atTop
        (𝓝 (∫ θ in 0..2 * Real.pi,
          u₀ (sourceJointCoverCirclePoint q v R θ))) := by
    simp_rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact hdom
  have hsource :
      (fun r : ℕ =>
        Real.circleAverage
          (fun w : ℂ => u r (q + w • v)) 0 R) =
        (fun r : ℕ =>
          (2 * Real.pi)⁻¹ *
            ∫ θ in 0..2 * Real.pi,
              u r (sourceJointCoverCirclePoint q v R θ)) := by
    funext r
    exact circleAverage_sourceJointCover_eq (u r) q v R
  have htarget :
      Real.circleAverage
        (fun w : ℂ => u₀ (q + w • v)) 0 R =
        (2 * Real.pi)⁻¹ *
          ∫ θ in 0..2 * Real.pi,
            u₀ (sourceJointCoverCirclePoint q v R θ) :=
    circleAverage_sourceJointCover_eq u₀ q v R
  rw [hsource, htarget]
  exact hinter.const_mul ((2 * Real.pi)⁻¹)
theorem exists_sourceJointCoverCircle_uniform_bounds
    {n : ℕ}
    (a b : SourceJointComplexCover n → ℝ)
    (ha : Continuous a) (hb : Continuous b)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    ∃ L C : ℝ,
      ∀ z : SourceJointComplexCover n,
        dist z q ≤ 1 →
          (L ≤ a z ∧ b z ≤ C) ∧
          ∀ θ : ℝ,
            L ≤ a (sourceJointCoverCirclePoint z v R θ) ∧
              b (sourceJointCoverCirclePoint z v R θ) ≤ C := by
  let S : ℝ := 1 + |R| * ‖v‖
  have hcompact :
      IsCompact (Metric.closedBall q S) :=
    isCompact_closedBall q S
  obtain ⟨L, hL⟩ := (hcompact.image ha).bddBelow
  obtain ⟨C, hC⟩ := (hcompact.image hb).bddAbove
  refine ⟨L, C, ?_⟩
  intro z hz
  have hzmem : z ∈ Metric.closedBall q S := by
    apply Metric.mem_closedBall.mpr
    dsimp [S]
    nlinarith [abs_nonneg R, norm_nonneg v,
      mul_nonneg (abs_nonneg R) (norm_nonneg v)]
  refine ⟨⟨hL ⟨_, hzmem, rfl⟩,
    hC ⟨_, hzmem, rfl⟩⟩, ?_⟩
  intro θ
  have hmem :
      sourceJointCoverCirclePoint z v R θ ∈
        Metric.closedBall q S := by
    apply Metric.mem_closedBall.mpr
    calc
      dist (sourceJointCoverCirclePoint z v R θ) q ≤
          dist (sourceJointCoverCirclePoint z v R θ) z +
            dist z q :=
        dist_triangle _ _ _
      _ = ‖circleMap 0 R θ • v‖ + dist z q := by
        simp [sourceJointCoverCirclePoint, dist_eq_norm]
      _ = |R| * ‖v‖ + dist z q := by
        rw [norm_smul, norm_circleMap_zero]
      _ ≤ S := by
        dsimp [S]
        linarith
  exact ⟨hL ⟨_, hmem, rfl⟩,
    hC ⟨_, hmem, rfl⟩⟩
theorem sourceJointCover_complex_line_submean_of_convergent_finite_approximants
    {n : ℕ} {ι : Type*}
    (F : ι → SourceJointComplexCover n → ℝ)
    (hFcont : ∀ i : ι, Continuous (F i))
    (u : SourceJointComplexCover n → ℝ)
    (hu : UpperSemicontinuous u)
    (q : ℕ → SourceJointComplexCover n)
    (i : ℕ → ι)
    (q₀ : SourceJointComplexCover n)
    (hq : Tendsto q atTop (𝓝 q₀))
    (hvalue : Tendsto (fun m : ℕ => F (i m) (q m))
      atTop (𝓝 (u q₀)))
    (v : SourceJointComplexCover n) (R : ℝ)
    (L C : ℝ)
    (hflower : ∀ m : ℕ, L ≤ F (i m) (q m))
    (hbound : ∀ (m : ℕ) (θ : ℝ),
      L ≤ u (sourceJointCoverCirclePoint (q m) v R θ) ∧
        u (sourceJointCoverCirclePoint (q m) v R θ) ≤ C)
    (hbound₀ : ∀ θ : ℝ,
      L ≤ u (sourceJointCoverCirclePoint q₀ v R θ) ∧
        u (sourceJointCoverCirclePoint q₀ v R θ) ≤ C)
    (hle : ∀ (j : ι) (z : SourceJointComplexCover n),
      F j z ≤ u z)
    (hsubmean : ∀ m : ℕ,
      F (i m) (q m) ≤
        Real.circleAverage
          (fun w : ℂ => F (i m) (q m + w • v)) 0 R) :
    u q₀ ≤
      Real.circleAverage
        (fun w : ℂ => u (q₀ + w • v)) 0 R := by
  let γ : ℕ → ℝ → SourceJointComplexCover n :=
    fun m θ => sourceJointCoverCirclePoint (q m) v R θ
  let γ₀ : ℝ → SourceJointComplexCover n :=
    fun θ => sourceJointCoverCirclePoint q₀ v R θ
  have hγ (m : ℕ) : Continuous (γ m) :=
    continuous_sourceJointCoverCirclePoint (q m) v R
  have hγ₀ : Continuous γ₀ :=
    continuous_sourceJointCoverCirclePoint q₀ v R
  have hγt (θ : ℝ) :
      Tendsto (fun m : ℕ => γ m θ) atTop (𝓝 (γ₀ θ)) :=
    tendsto_sourceJointCoverCirclePoint q q₀ hq v R θ
  have hangleint (m : ℕ) :
      IntervalIntegrable
        (fun θ : ℝ => u (γ m θ)) volume 0 (2 * Real.pi) := by
    have hc := circleIntegrable_sourceJointCover_of_upperSemicontinuous
      u hu (q m) v R L C (hbound m)
    rw [circleIntegrable_def] at hc
    exact hc
  have hangleint₀ :
      IntervalIntegrable
        (fun θ : ℝ => u (γ₀ θ)) volume 0 (2 * Real.pi) := by
    have hc := circleIntegrable_sourceJointCover_of_upperSemicontinuous
      u hu q₀ v R L C hbound₀
    rw [circleIntegrable_def] at hc
    exact hc
  have havg (m : ℕ) :
      F (i m) (q m) ≤
        Real.circleAverage
          (fun w : ℂ => u (q m + w • v)) 0 R :=
    (hsubmean m).trans
      (circleAverage_sourceJointCover_mono
        (F (i m)) u (hFcont (i m)) hu
          (q m) v R L C (hbound m) (hle (i m)))
  have hscaled (m : ℕ) :
      (2 * Real.pi) * (F (i m) (q m) - L) ≤
        ∫ θ,
          u (γ m θ) - L
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    have hm := havg m
    rw [circleAverage_sourceJointCover_eq
      u (q m) v R] at hm
    have hmdiv :
        F (i m) (q m) ≤
          (∫ θ in 0..2 * Real.pi,
            u (γ m θ)) / (2 * Real.pi) := by
      simpa [γ, div_eq_mul_inv, mul_comm] using hm
    have hmprod :
        (2 * Real.pi) * F (i m) (q m) ≤
          ∫ θ in 0..2 * Real.pi, u (γ m θ) := by
      nlinarith [(le_div_iff₀ Real.two_pi_pos).mp hmdiv]
    rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_sub
        (hangleint m) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,
      sub_zero, smul_eq_mul]
    nlinarith
  have hshiftint (m : ℕ) :
      Integrable
        (fun θ : ℝ => u (γ m θ) - L)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    have hmeas :
        Measurable (fun θ : ℝ => u (γ m θ) - L) :=
      (hu.comp (hγ m)).measurable.sub measurable_const
    refine (integrable_const (C - L)).mono'
      hmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hbound m θ).1)]
      exact sub_le_sub_right (hbound m θ).2 L
  have hintbound (m : ℕ) :
      (∫ θ,
        u (γ m θ) - L
          ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) ≤
        ∫ _ : ℝ, C - L
          ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    integral_mono (hshiftint m) (integrable_const (C - L))
      (fun θ => sub_le_sub_right (hbound m θ).2 L)
  have hseqbdd :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun m : ℕ => ∫ θ,
          u (γ m θ) - L
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall hintbound)
  have hseqcob :
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun m : ℕ =>
          (2 * Real.pi) * (F (i m) (q m) - L)) :=
    Filter.isCoboundedUnder_le_of_le atTop
      (fun m => mul_nonneg Real.two_pi_pos.le
        (sub_nonneg.mpr (hflower m)))
  have hscaledtendsto :
      Tendsto
        (fun m : ℕ =>
          (2 * Real.pi) * (F (i m) (q m) - L))
        atTop (𝓝 ((2 * Real.pi) * (u q₀ - L))) :=
    (hvalue.sub tendsto_const_nhds).const_mul
      (2 * Real.pi)
  have hfatou :=
    limsup_integral_sub_const_le_of_upperSemicontinuous
      (volume.restrict (Set.Ioc 0 (2 * Real.pi)))
      u hu γ γ₀ hγ hγ₀ hγt L C
      (by
        intro m θ
        exact hbound m θ)
      (by
        intro θ
        exact hbound₀ θ)
  have hmain :
      (2 * Real.pi) * (u q₀ - L) ≤
        ∫ θ,
          u (γ₀ θ) - L
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    calc
      (2 * Real.pi) * (u q₀ - L) =
          Filter.limsup
            (fun m : ℕ =>
              (2 * Real.pi) * (F (i m) (q m) - L)) atTop :=
        hscaledtendsto.limsup_eq.symm
      _ ≤ Filter.limsup
          (fun m : ℕ => ∫ θ,
            u (γ m θ) - L
              ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))))
            atTop :=
        Filter.limsup_le_limsup
          (Filter.Eventually.of_forall hscaled)
            hseqcob hseqbdd
      _ ≤ ∫ θ,
          u (γ₀ θ) - L
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
        hfatou
  have hmaininterval :
      (2 * Real.pi) * (u q₀ - L) ≤
        ∫ θ in 0..2 * Real.pi, u (γ₀ θ) - L := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact hmain
  rw [intervalIntegral.integral_sub
    hangleint₀ intervalIntegrable_const] at hmaininterval
  simp only [intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hmaininterval
  rw [circleAverage_sourceJointCover_eq u q₀ v R]
  have hprod :
      (2 * Real.pi) * u q₀ ≤
        ∫ θ in 0..2 * Real.pi, u (γ₀ θ) := by
    nlinarith
  have hdiv :
      u q₀ ≤
        (∫ θ in 0..2 * Real.pi, u (γ₀ θ)) /
          (2 * Real.pi) := by
    apply (le_div_iff₀ Real.two_pi_pos).mpr
    nlinarith
  simpa [γ₀, div_eq_mul_inv, mul_comm] using hdiv
theorem sourceJointCover_upperRegularization_family_complex_line_submean_all_radius
    {n : ℕ} {ι : Type*} [Nonempty ι]
    (F : ι → SourceJointComplexCover n → ℝ)
    (hFcont : ∀ i : ι, Continuous (F i))
    (a b : SourceJointComplexCover n → ℝ)
    (ha : Continuous a) (hb : Continuous b)
    (hlower : ∀ (i : ι) (z : SourceJointComplexCover n),
      a z ≤ F i z)
    (hmajor : ∀ (i : ι) (z : SourceJointComplexCover n),
      F i z ≤ b z)
    (hsubmean : ∀ (i : ι) (z v : SourceJointComplexCover n)
      (R : ℝ),
      F i z ≤
        Real.circleAverage
          (fun w : ℂ => F i (z + w • v)) 0 R)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    upperRegularization
        (fun z : SourceJointComplexCover n =>
          sSup (Set.range fun i : ι => F i z)) q ≤
      Real.circleAverage
        (fun w : ℂ => upperRegularization
          (fun z : SourceJointComplexCover n =>
            sSup (Set.range fun i : ι => F i z))
              (q + w • v)) 0 R := by
  let f : SourceJointComplexCover n → ℝ :=
    fun z => sSup (Set.range fun i : ι => F i z)
  let u : SourceJointComplexCover n → ℝ :=
    upperRegularization f
  have hbounded (z : SourceJointComplexCover n) :
      BddAbove (Set.range fun i : ι => F i z) := by
    refine ⟨b z, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hmajor i z
  have hfmajor (z : SourceJointComplexCover n) : f z ≤ b z := by
    apply csSup_le (Set.range_nonempty fun i : ι => F i z)
    rintro _ ⟨i, rfl⟩
    exact hmajor i z
  have hlocal (z : SourceJointComplexCover n) :
      (localUpperBounds f z).Nonempty :=
    localUpperBounds_nonempty_of_continuous_majorant
      f b hb hfmajor z
  have hu : UpperSemicontinuous u :=
    upperSemicontinuous_upperRegularization f hlocal
  have huupper (z : SourceJointComplexCover n) : u z ≤ b z :=
    upperRegularization_le_of_continuous_majorant
      f b hb hfmajor z
  have hfamily (i : ι) (z : SourceJointComplexCover n) :
      F i z ≤ u z := by
    calc
      F i z ≤ f z := le_csSup (hbounded z) ⟨i, rfl⟩
      _ ≤ u z := le_upperRegularization f z (hlocal z)
  have hulower (z : SourceJointComplexCover n) : a z ≤ u z := by
    let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    exact (hlower i₀ z).trans (hfamily i₀ z)
  obtain ⟨L, C, hcompact⟩ :=
    exists_sourceJointCoverCircle_uniform_bounds a b ha hb q v R
  have hcent :=
    tendsto_upperRegularizationFamilyApproximant_center F q
  have hval :=
    tendsto_upperRegularizationFamilyApproximant_value
      F q hbounded hlocal
  have hnear :
      ∀ᶠ m : ℕ in atTop,
        dist (upperRegularizationFamilyApproximant F q m).1 q < 1 :=
    Metric.tendsto_nhds.mp hcent 1 (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnear
  let qseq : ℕ → SourceJointComplexCover n :=
    fun m => (upperRegularizationFamilyApproximant F q (m + N)).1
  let iseq : ℕ → ι :=
    fun m => (upperRegularizationFamilyApproximant F q (m + N)).2
  have hqseq : Tendsto qseq atTop (𝓝 q) :=
    hcent.comp (Filter.tendsto_add_atTop_nat N)
  have hseqvalue :
      Tendsto (fun m : ℕ => F (iseq m) (qseq m))
        atTop (𝓝 (u q)) :=
    hval.comp (Filter.tendsto_add_atTop_nat N)
  have hqnear (m : ℕ) : dist (qseq m) q ≤ 1 :=
    (hN (m + N) (by omega)).le
  have hqself : dist q q ≤ (1 : ℝ) := by simp
  have hflower (m : ℕ) : L ≤ F (iseq m) (qseq m) :=
    ((hcompact (qseq m) (hqnear m)).1.1).trans
      (hlower (iseq m) (qseq m))
  have hbound (m : ℕ) (θ : ℝ) :
      L ≤ u (sourceJointCoverCirclePoint (qseq m) v R θ) ∧
        u (sourceJointCoverCirclePoint (qseq m) v R θ) ≤ C := by
    obtain ⟨hlo, hup⟩ :=
      (hcompact (qseq m) (hqnear m)).2 θ
    exact ⟨hlo.trans (hulower _),
      (huupper _).trans hup⟩
  have hbound₀ (θ : ℝ) :
      L ≤ u (sourceJointCoverCirclePoint q v R θ) ∧
        u (sourceJointCoverCirclePoint q v R θ) ≤ C := by
    obtain ⟨hlo, hup⟩ := (hcompact q hqself).2 θ
    exact ⟨hlo.trans (hulower _),
      (huupper _).trans hup⟩
  have hfinite (m : ℕ) :
      F (iseq m) (qseq m) ≤
        Real.circleAverage
          (fun w : ℂ => F (iseq m) (qseq m + w • v)) 0 R :=
    hsubmean (iseq m) (qseq m) v R
  exact sourceJointCover_complex_line_submean_of_convergent_finite_approximants
    F hFcont u hu qseq iseq q hqseq hseqvalue v R
    L C hflower hbound hbound₀ hfamily hfinite
end JetEnvelopeGlobalPlurisubharmonicClosure
namespace JetEnvelopeTrueRadialMollifier
open Set Filter Function MeasureTheory Metric
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff
local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (TorusCharacters.LogSpace n))
    (volume : Measure ℂ)
def sourceJointRadialNormSq {n : ℕ}
    (q : SourceJointComplexCover n) : ℝ :=
  (∑ i : Fin n, Complex.normSq (q.1 i)) + Complex.normSq q.2
theorem contDiff_sourceJointRadialNormSq (n : ℕ) :
    ContDiff ℝ ∞ (sourceJointRadialNormSq (n := n)) := by
  unfold sourceJointRadialNormSq
  apply ContDiff.add
  · apply ContDiff.sum
    intro i _
    simp_rw [Complex.normSq_apply]
    have hz : ContDiff ℝ ∞
        (fun q : SourceJointComplexCover n => q.1 i) := by
      fun_prop
    exact ((Complex.reCLM.contDiff.comp hz).mul
      (Complex.reCLM.contDiff.comp hz)).add
        ((Complex.imCLM.contDiff.comp hz).mul
          (Complex.imCLM.contDiff.comp hz))
  · simp_rw [Complex.normSq_apply]
    have hz : ContDiff ℝ ∞
        (fun q : SourceJointComplexCover n => q.2) := by
      fun_prop
    exact ((Complex.reCLM.contDiff.comp hz).mul
      (Complex.reCLM.contDiff.comp hz)).add
        ((Complex.imCLM.contDiff.comp hz).mul
          (Complex.imCLM.contDiff.comp hz))
theorem sourceJointRadialNormSq_coordinate_le {n : ℕ}
    (q : SourceJointComplexCover n) (i : Fin n) :
    Complex.normSq (q.1 i) ≤ sourceJointRadialNormSq q := by
  unfold sourceJointRadialNormSq
  calc
    Complex.normSq (q.1 i) ≤
      ∑ j : Fin n, Complex.normSq (q.1 j) :=
        Finset.single_le_sum
          (fun j _ => Complex.normSq_nonneg (q.1 j))
          (Finset.mem_univ i)
    _ ≤ (∑ j : Fin n, Complex.normSq (q.1 j)) +
          Complex.normSq q.2 :=
        le_add_of_nonneg_right (Complex.normSq_nonneg q.2)
theorem sourceJointRadialNormSq_auxiliary_le {n : ℕ}
    (q : SourceJointComplexCover n) :
    Complex.normSq q.2 ≤ sourceJointRadialNormSq q := by
  unfold sourceJointRadialNormSq
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
def sourceJointTrueRadialBump (n k : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  Real.smoothTransition
    (1 - (((k + 1 : ℕ) : ℝ) ^ 2) * sourceJointRadialNormSq q)
theorem contDiff_sourceJointTrueRadialBump (n k : ℕ) :
    ContDiff ℝ ∞ (sourceJointTrueRadialBump n k) := by
  unfold sourceJointTrueRadialBump
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub
      (contDiff_const.mul (contDiff_sourceJointRadialNormSq n)))
theorem sourceJointTrueRadialBump_nonneg (n k : ℕ)
    (q : SourceJointComplexCover n) :
    0 ≤ sourceJointTrueRadialBump n k q :=
  Real.smoothTransition.nonneg _
theorem support_sourceJointTrueRadialBump_subset_closedBall
    {n : ℕ} (k : ℕ) :
    Function.support (sourceJointTrueRadialBump n k) ⊆
      Metric.closedBall (0 : SourceJointComplexCover n)
        (1 / ((k + 1 : ℕ) : ℝ)) := by
  intro q hq
  have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ k
  have harg :
      0 < 1 - (((k + 1 : ℕ) : ℝ) ^ 2) *
        sourceJointRadialNormSq q := by
    apply lt_of_not_ge
    intro h
    apply hq
    exact Real.smoothTransition.zero_iff_nonpos.mpr h
  have hrad :
      (((k + 1 : ℕ) : ℝ) ^ 2) * sourceJointRadialNormSq q < 1 := by
    linarith
  have hcoord (i : Fin n) :
      ‖q.1 i‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
    have hs := sourceJointRadialNormSq_coordinate_le q i
    rw [Complex.normSq_eq_norm_sq] at hs
    have hsq :
        (((k + 1 : ℕ) : ℝ) * ‖q.1 i‖) ^ 2 < 1 := by
      rw [mul_pow]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) hrad
    have hprod : 0 ≤ (((k + 1 : ℕ) : ℝ) * ‖q.1 i‖) :=
      mul_nonneg hk.le (norm_nonneg _)
    apply (le_div_iff₀ hk).mpr
    nlinarith
  have haux :
      ‖q.2‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
    have hs := sourceJointRadialNormSq_auxiliary_le q
    rw [Complex.normSq_eq_norm_sq] at hs
    have hsq :
        (((k + 1 : ℕ) : ℝ) * ‖q.2‖) ^ 2 < 1 := by
      rw [mul_pow]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) hrad
    have hprod : 0 ≤ (((k + 1 : ℕ) : ℝ) * ‖q.2‖) :=
      mul_nonneg hk.le (norm_nonneg _)
    apply (le_div_iff₀ hk).mpr
    nlinarith
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def,
    max_le_iff]
  exact ⟨(pi_norm_le_iff_of_nonneg (by positivity)).mpr hcoord,
    haux⟩
theorem hasCompactSupport_sourceJointTrueRadialBump (n k : ℕ) :
    HasCompactSupport (sourceJointTrueRadialBump n k) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : SourceJointComplexCover n)
      (1 / ((k + 1 : ℕ) : ℝ)))
    (support_sourceJointTrueRadialBump_subset_closedBall k)
def sourceJointTrueRadialBumpMass (n k : ℕ) : ℝ :=
  ∫ q : SourceJointComplexCover n,
    sourceJointTrueRadialBump n k q
theorem sourceJointTrueRadialBumpMass_pos (n k : ℕ) :
    0 < sourceJointTrueRadialBumpMass n k := by
  unfold sourceJointTrueRadialBumpMass
  apply (contDiff_sourceJointTrueRadialBump n k).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_sourceJointTrueRadialBump n k)
    (fun q => sourceJointTrueRadialBump_nonneg n k q)
    (x := (0 : SourceJointComplexCover n))
  simp [sourceJointTrueRadialBump, sourceJointRadialNormSq]
def sourceJointTrueRadialMollifier (n k : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  sourceJointTrueRadialBump n k q / sourceJointTrueRadialBumpMass n k
theorem contDiff_sourceJointTrueRadialMollifier (n k : ℕ) :
    ContDiff ℝ ∞ (sourceJointTrueRadialMollifier n k) := by
  unfold sourceJointTrueRadialMollifier
  exact (contDiff_sourceJointTrueRadialBump n k).div_const _
theorem sourceJointTrueRadialMollifier_nonneg (n k : ℕ)
    (q : SourceJointComplexCover n) :
    0 ≤ sourceJointTrueRadialMollifier n k q :=
  div_nonneg (sourceJointTrueRadialBump_nonneg n k q)
    (sourceJointTrueRadialBumpMass_pos n k).le
theorem support_sourceJointTrueRadialMollifier_subset_closedBall
    {n : ℕ} (k : ℕ) :
    Function.support (sourceJointTrueRadialMollifier n k) ⊆
      Metric.closedBall (0 : SourceJointComplexCover n)
        (1 / ((k + 1 : ℕ) : ℝ)) := by
  intro q hq
  apply support_sourceJointTrueRadialBump_subset_closedBall k
  intro hzero
  apply hq
  simp [sourceJointTrueRadialMollifier, hzero]
theorem hasCompactSupport_sourceJointTrueRadialMollifier (n k : ℕ) :
    HasCompactSupport (sourceJointTrueRadialMollifier n k) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : SourceJointComplexCover n)
      (1 / ((k + 1 : ℕ) : ℝ)))
    (support_sourceJointTrueRadialMollifier_subset_closedBall k)
theorem integrable_sourceJointTrueRadialMollifier (n k : ℕ) :
    Integrable (sourceJointTrueRadialMollifier n k)
      (volume : Measure (SourceJointComplexCover n)) :=
  (contDiff_sourceJointTrueRadialMollifier n k).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_sourceJointTrueRadialMollifier n k)
theorem integral_sourceJointTrueRadialMollifier (n k : ℕ) :
    (∫ q : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k q) = 1 := by
  unfold sourceJointTrueRadialMollifier
  rw [integral_div]
  change sourceJointTrueRadialBumpMass n k /
    sourceJointTrueRadialBumpMass n k = 1
  exact div_self (ne_of_gt (sourceJointTrueRadialBumpMass_pos n k))
def sourceJointTrueRadialSmoothed {n : ℕ}
    (f : SourceJointComplexCover n → ℝ) (k : ℕ) :
    SourceJointComplexCover n → ℝ :=
  sourceJointTrueRadialMollifier n k
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (SourceJointComplexCover n))] f
theorem integrable_sourceJointTrueRadialMollifier_mul_translate
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (k : ℕ) (q : SourceJointComplexCover n) :
    Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y * f (q - y))
      (volume : Measure (SourceJointComplexCover n)) := by
  have h :=
    (hasCompactSupport_sourceJointTrueRadialMollifier n k).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (contDiff_sourceJointTrueRadialMollifier n k).continuous hf q
  refine h.integrable.congr
    (Filter.Eventually.of_forall fun y => ?_)
  change sourceJointTrueRadialMollifier n k y * f (q - y) =
    sourceJointTrueRadialMollifier n k y * f (q - y)
  rfl
theorem contDiff_sourceJointTrueRadialSmoothed {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (k : ℕ) :
    ContDiff ℝ ∞ (sourceJointTrueRadialSmoothed f k) := by
  exact (hasCompactSupport_sourceJointTrueRadialMollifier n k).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (contDiff_sourceJointTrueRadialMollifier n k) hf
theorem sourceJointTrueRadialSmoothed_periodic {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    {d : SourceJointComplexCover n}
    (hf : Function.Periodic f d)
    (k : ℕ) :
    Function.Periodic (sourceJointTrueRadialSmoothed f k) d := by
  intro x
  unfold sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with y
  change
    sourceJointTrueRadialMollifier n k y * f (x + d - y) =
      sourceJointTrueRadialMollifier n k y * f (x - y)
  rw [show x + d - y = (x - y) + d by abel,
    hf (x - y)]
end JetEnvelopeTrueRadialMollifier
namespace JetEnvelopeTrueRadialHessian
open Set Filter Function MeasureTheory Metric Matrix
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff
theorem hasDerivAt_intervalIntegral_of_joint_continuous
    (F F' : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hdiff : ∀ x θ : ℝ,
      HasDerivAt (fun r : ℝ => F r θ) (F' x θ) x)
    (x₀ a b : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∫ θ in a..b, F x θ)
      (∫ θ in a..b, F' x₀ θ) x₀ := by
  have hFslice (x : ℝ) : Continuous (F x) := by
    change Continuous (fun θ : ℝ => (Function.uncurry F) (x, θ))
    fun_prop
  have hF'slice (x : ℝ) : Continuous (F' x) := by
    change Continuous (fun θ : ℝ => (Function.uncurry F') (x, θ))
    fun_prop
  obtain ⟨C, hC⟩ :=
    (((isCompact_closedBall x₀ (1 : ℝ)).prod
      (isCompact_uIcc : IsCompact (Set.uIcc a b))).image
        hF'.norm).bddAbove
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ))
    (s := Metric.closedBall x₀ (1 : ℝ))
    (bound := fun _ : ℝ => C)
    (Metric.closedBall_mem_nhds x₀ (by norm_num))
    (Eventually.of_forall fun x =>
      (hFslice x).measurable.aestronglyMeasurable)
    ((hFslice x₀).intervalIntegrable a b)
    ((hF'slice x₀).measurable.aestronglyMeasurable)
    (Eventually.of_forall fun θ hθ x hx =>
      hC ⟨(x, θ), ⟨hx, Set.uIoc_subset_uIcc hθ⟩, rfl⟩)
    ((continuous_const : Continuous (fun _ : ℝ => C)).intervalIntegrable
      a b)
    (Eventually.of_forall fun θ _ x _ => hdiff x θ)).2
theorem sourceJoint_ofReal_smul {n : ℕ}
    (r : ℝ) (v : SourceJointComplexCover n) :
    (r : ℂ) • v = r • v := by
  apply Prod.ext
  · funext i
    change (r : ℂ) * v.1 i = r • v.1 i
    simp [Complex.real_smul]
  · change (r : ℂ) * v.2 = r • v.2
    simp [Complex.real_smul]
theorem sourceJointCircleMap_radius_smul {n : ℕ}
    (v : SourceJointComplexCover n) (r θ : ℝ) :
    circleMap 0 r θ • v = r • (circleMap 0 1 θ • v) := by
  simp only [circleMap, zero_add]
  simpa [Complex.real_smul] using
    (smul_assoc r (Complex.exp ((θ : ℂ) * Complex.I)) v)
theorem sourceJointCircleMap_unit_direction {n : ℕ}
    (v : SourceJointComplexCover n) (θ : ℝ) :
    circleMap 0 1 θ • v =
      Real.cos θ • v + Real.sin θ • (Complex.I • v) := by
  have hcircle : circleMap 0 1 θ =
      Complex.exp ((θ : ℂ) * Complex.I) := by
    simp [circleMap]
  rw [hcircle, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos θ, ← Complex.ofReal_sin θ,
    add_smul, ← smul_smul,
    sourceJoint_ofReal_smul (Real.cos θ) v,
    sourceJoint_ofReal_smul (Real.sin θ) (Complex.I • v)]
theorem hasDerivAt_sourceJointRealAffine {n : ℕ}
    (q d : SourceJointComplexCover n) (r : ℝ) :
    HasDerivAt (fun x : ℝ => q + x • d) d r := by
  simpa using ((hasDerivAt_id r).smul_const d).const_add q
theorem hasDerivAt_sourceJointCircleLine {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q d : SourceJointComplexCover n) (r : ℝ) :
    HasDerivAt (fun x : ℝ => f (q + x • d))
      ((fderiv ℝ f (q + r • d)) d) r := by
  exact ((hf.differentiable (by norm_num) (q + r • d)).hasFDerivAt).comp_hasDerivAt
    r (hasDerivAt_sourceJointRealAffine q d r)
theorem hasDerivAt_sourceJointCircleLineDerivative {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q d : SourceJointComplexCover n) (r : ℝ) :
    HasDerivAt (fun x : ℝ => (fderiv ℝ f (q + x • d)) d)
      (((fderiv ℝ (fderiv ℝ f) (q + r • d)) d) d) r := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have heval : HasFDerivAt
      (fun y : SourceJointComplexCover n => (fderiv ℝ f y) d)
      ((ContinuousLinearMap.apply ℝ ℝ d).comp
        (fderiv ℝ (fderiv ℝ f) (q + r • d)))
      (q + r • d) := by
    exact (ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp
      (q + r • d)
      (hfd.differentiable (by norm_num) (q + r • d)).hasFDerivAt
  have hcomp : HasDerivAt
      ((fun y : SourceJointComplexCover n => (fderiv ℝ f y) d) ∘
        (fun x : ℝ => q + x • d))
      (((ContinuousLinearMap.apply ℝ ℝ d).comp
        (fderiv ℝ (fderiv ℝ f) (q + r • d))) d) r := by
    exact heval.comp_hasDerivAt r
      (hasDerivAt_sourceJointRealAffine q d r)
  refine (hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  rfl
theorem local_min_second_derivative_nonnegative
    {g : ℝ → ℝ} {r : ℝ}
    (hmin : IsLocalMin g r)
    (hc : ContinuousAt g r) :
    0 ≤ deriv (deriv g) r := by
  by_contra h
  have hneg : deriv (deriv g) r < 0 := lt_of_not_ge h
  have hzero : deriv g r = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax g r :=
    isLocalMax_of_deriv_deriv_neg hneg hzero hc
  have heq : g =ᶠ[𝓝 r] (fun _ : ℝ => g r) := by
    filter_upwards [hmin, hmax] with x hxmin hxmax
    exact le_antisymm hxmax hxmin
  have hsecond : deriv (deriv g) r = 0 := by
    have hd := heq.deriv.deriv_eq
    simpa using hd
  linarith
def sourceJointCircleRadiusProfile {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n) (r : ℝ) : ℝ :=
  Real.circleAverage (fun w : ℂ => f (q + w • v)) 0 r
theorem continuous_sourceJointCircleRadiusProfile {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : Continuous f)
    (q v : SourceJointComplexCover n) :
    Continuous (sourceJointCircleRadiusProfile f q v) := by
  let F : ℝ → ℝ → ℝ :=
    fun r θ => f (q + circleMap 0 r θ • v)
  have hjoint : Continuous (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    fun_prop
  have hint :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := (volume : Measure ℝ)) hjoint 0 (2 * Real.pi)
  unfold sourceJointCircleRadiusProfile
  simp_rw [Real.circleAverage_def]
  change Continuous
    (fun r : ℝ => (2 * Real.pi)⁻¹ •
      ∫ θ in 0..2 * Real.pi, F r θ)
  exact hint.fun_const_smul ((2 * Real.pi)⁻¹)
theorem sourceJointCircleRadiusProfile_zero {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n) :
    sourceJointCircleRadiusProfile f q v 0 = f q := by
  simp [sourceJointCircleRadiusProfile]
theorem sourceJointCircleRadiusProfile_second_eq_integral
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q v : SourceJointComplexCover n) :
    deriv (deriv (sourceJointCircleRadiusProfile f q v)) 0 =
      (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi,
          ((fderiv ℝ (fderiv ℝ f) q)
            (circleMap 0 1 θ • v))
              (circleMap 0 1 θ • v) := by
  let d : ℝ → SourceJointComplexCover n :=
    fun θ => circleMap 0 1 θ • v
  let F : ℝ → ℝ → ℝ :=
    fun r θ => f (q + r • d θ)
  let F' : ℝ → ℝ → ℝ :=
    fun r θ => (fderiv ℝ f (q + r • d θ)) (d θ)
  let F'' : ℝ → ℝ → ℝ :=
    fun r θ =>
      ((fderiv ℝ (fderiv ℝ f) (q + r • d θ)) (d θ)) (d θ)
  have hd : Continuous d := by
    dsimp [d]
    fun_prop
  have hpoint :
      Continuous (fun x : ℝ × ℝ => q + x.1 • d x.2) := by
    have heq :
        (fun x : ℝ × ℝ => q + x.1 • d x.2) =
          (fun x : ℝ × ℝ => q + circleMap 0 x.1 x.2 • v) := by
      funext x
      change q + x.1 • (circleMap 0 1 x.2 • v) =
        q + circleMap 0 x.1 x.2 • v
      exact congrArg
        (fun w : SourceJointComplexCover n => q + w)
        (sourceJointCircleMap_radius_smul v x.1 x.2).symm
    rw [heq]
    fun_prop
  have hdir : Continuous (fun x : ℝ × ℝ => d x.2) :=
    hd.comp continuous_snd
  have hF : Continuous (Function.uncurry F) := by
    change Continuous (fun x : ℝ × ℝ => f (q + x.1 • d x.2))
    exact hf.continuous.comp hpoint
  have hF' : Continuous (Function.uncurry F') := by
    change Continuous
      (fun x : ℝ × ℝ =>
        (fderiv ℝ f (q + x.1 • d x.2)) (d x.2))
    exact ((hf.continuous_fderiv (by norm_num)).comp hpoint).clm_apply hdir
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hF'' : Continuous (Function.uncurry F'') := by
    change Continuous
      (fun x : ℝ × ℝ =>
        ((fderiv ℝ (fderiv ℝ f) (q + x.1 • d x.2))
          (d x.2)) (d x.2))
    exact (((hfd.continuous_fderiv (by norm_num)).comp hpoint).clm_apply
      hdir).clm_apply hdir
  have hdiff (r θ : ℝ) :
      HasDerivAt (fun x : ℝ => F x θ) (F' r θ) r := by
    exact hasDerivAt_sourceJointCircleLine hf q (d θ) r
  have hdiff' (r θ : ℝ) :
      HasDerivAt (fun x : ℝ => F' x θ) (F'' r θ) r := by
    exact hasDerivAt_sourceJointCircleLineDerivative hf q (d θ) r
  have hI (r : ℝ) :
      HasDerivAt
        (fun x : ℝ => ∫ θ in 0..2 * Real.pi, F x θ)
        (∫ θ in 0..2 * Real.pi, F' r θ) r :=
    hasDerivAt_intervalIntegral_of_joint_continuous
      F F' hF hF' hdiff r 0 (2 * Real.pi)
  have hI' (r : ℝ) :
      HasDerivAt
        (fun x : ℝ => ∫ θ in 0..2 * Real.pi, F' x θ)
        (∫ θ in 0..2 * Real.pi, F'' r θ) r :=
    hasDerivAt_intervalIntegral_of_joint_continuous
      F' F'' hF' hF'' hdiff' r 0 (2 * Real.pi)
  have hprofile :
      sourceJointCircleRadiusProfile f q v =
        fun r : ℝ =>
          (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, F r θ := by
    funext r
    simp only [sourceJointCircleRadiusProfile, Real.circleAverage_def,
      smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    change f (q + circleMap 0 r θ • v) =
      f (q + r • (circleMap 0 1 θ • v))
    rw [sourceJointCircleMap_radius_smul]
  have hfirst :
      deriv (sourceJointCircleRadiusProfile f q v) =
        fun r : ℝ =>
          (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, F' r θ := by
    funext r
    rw [hprofile]
    exact ((hI r).const_mul ((2 * Real.pi)⁻¹)).deriv
  rw [hfirst]
  calc
    _ = (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi, F'' 0 θ :=
      ((hI' 0).const_mul ((2 * Real.pi)⁻¹)).deriv
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      change
        ((fderiv ℝ (fderiv ℝ f) (q + (0 : ℝ) • d θ))
          (d θ)) (d θ) =
        ((fderiv ℝ (fderiv ℝ f) q) (d θ)) (d θ)
      have hz : (0 : ℝ) • d θ =
          (0 : SourceJointComplexCover n) := by
        change (0 : ℂ) • d θ = 0
        exact zero_smul ℂ (d θ)
      rw [hz, add_zero]
theorem sourceJointCircleQuadratic_expand {n : ℕ}
    (B : SourceJointComplexCover n →L[ℝ]
      SourceJointComplexCover n →L[ℝ] ℝ)
    (v : SourceJointComplexCover n) (θ : ℝ) :
    (B (circleMap 0 1 θ • v)) (circleMap 0 1 θ • v) =
      Real.cos θ ^ 2 * (B v v) +
        (Real.sin θ * Real.cos θ) *
          (B v (Complex.I • v) + B (Complex.I • v) v) +
        Real.sin θ ^ 2 * (B (Complex.I • v) (Complex.I • v)) := by
  rw [sourceJointCircleMap_unit_direction]
  simp [map_add, map_smul, smul_eq_mul]
  ring
theorem sourceJointIntegral_cos_sq_two_pi :
    (∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2) = Real.pi := by
  rw [integral_cos_sq]
  simp [Real.sin_two_pi, Real.cos_two_pi]
theorem sourceJointIntegral_sin_sq_two_pi :
    (∫ θ in 0..2 * Real.pi, Real.sin θ ^ 2) = Real.pi := by
  rw [integral_sin_sq]
  simp [Real.sin_two_pi, Real.cos_two_pi]
theorem sourceJointIntegral_sin_mul_cos_two_pi :
    (∫ θ in 0..2 * Real.pi,
      Real.sin θ * Real.cos θ) = 0 := by
  rw [integral_sin_mul_cos₁]
  simp [Real.sin_two_pi]
theorem sourceJointCircleQuadratic_average {n : ℕ}
    (B : SourceJointComplexCover n →L[ℝ]
      SourceJointComplexCover n →L[ℝ] ℝ)
    (v : SourceJointComplexCover n) :
    (2 * Real.pi)⁻¹ *
      (∫ θ in 0..2 * Real.pi,
        (B (circleMap 0 1 θ • v)) (circleMap 0 1 θ • v)) =
      ((B v v) + (B (Complex.I • v) (Complex.I • v))) / 2 := by
  let A : ℝ := B v v
  let C : ℝ := B v (Complex.I • v) + B (Complex.I • v) v
  let D : ℝ := B (Complex.I • v) (Complex.I • v)
  have hA : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ ^ 2 * A)
      (volume : Measure ℝ) 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hC : IntervalIntegrable
      (fun θ : ℝ => (Real.sin θ * Real.cos θ) * C)
      (volume : Measure ℝ) 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hD : IntervalIntegrable
      (fun θ : ℝ => Real.sin θ ^ 2 * D)
      (volume : Measure ℝ) 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    _ = (2 * Real.pi)⁻¹ *
      (∫ θ in 0..2 * Real.pi,
        (Real.cos θ ^ 2 * A +
          (Real.sin θ * Real.cos θ) * C +
          Real.sin θ ^ 2 * D)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      exact sourceJointCircleQuadratic_expand B v θ
    _ = (2 * Real.pi)⁻¹ *
      ((∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * A) +
        (∫ θ in 0..2 * Real.pi,
          (Real.sin θ * Real.cos θ) * C) +
        (∫ θ in 0..2 * Real.pi, Real.sin θ ^ 2 * D)) := by
      rw [intervalIntegral.integral_add (hA.add hC) hD,
        intervalIntegral.integral_add hA hC]
    _ = (2 * Real.pi)⁻¹ *
      (Real.pi * A + 0 * C + Real.pi * D) := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        sourceJointIntegral_cos_sq_two_pi,
        sourceJointIntegral_sin_mul_cos_two_pi,
        sourceJointIntegral_sin_sq_two_pi]
    _ = _ := by
      dsimp [A, C, D]
      field_simp
      ring
theorem sourceJointCircleRadiusProfile_second_eq_realHessian
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q v : SourceJointComplexCover n) :
    deriv (deriv (sourceJointCircleRadiusProfile f q v)) 0 =
      (((fderiv ℝ (fderiv ℝ f) q) v) v +
        ((fderiv ℝ (fderiv ℝ f) q) (Complex.I • v))
          (Complex.I • v)) / 2 := by
  rw [sourceJointCircleRadiusProfile_second_eq_integral hf q v]
  exact sourceJointCircleQuadratic_average (fderiv ℝ (fderiv ℝ f) q) v
def sourceJointRealLeviQuadratic {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n) : ℝ :=
  (((fderiv ℝ (fderiv ℝ f) q) v) v +
    ((fderiv ℝ (fderiv ℝ f) q) (Complex.I • v))
      (Complex.I • v)) / 4
end JetEnvelopeTrueRadialHessian
namespace JetEnvelopeTrueRadialComplexHessian
open Set Filter Function MeasureTheory Metric Matrix
open JetEnvelopeGlobalPlurisubharmonic EqualitySaturatingKillingPaths
open DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity SchurConvexity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff
theorem contDiff_sourceSpatialRealDirectional {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (u : TorusCharacters.LogSpace n) :
    ContDiff ℝ 1
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ a z) u) := by
  exact (ha.fderiv_right (by norm_num)).clm_apply contDiff_const
theorem fderiv_sourceSpatialRealDirectional {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z u w : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ a ξ) u) z) w =
      ((fderiv ℝ (fderiv ℝ a) z) w) u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ a) z :=
    (ha.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) z
  have he := fderiv_clm_apply hd
    (differentiableAt_const (c := u))
  have happly := congrArg
    (fun L : TorusCharacters.LogSpace n →L[ℝ] ℝ => L w)
    he
  simpa [ContinuousLinearMap.flip_apply] using happly
theorem fderiv_sourceSpatialComplexRealDirectional {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z u w : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        ((fderiv ℝ a ξ) u : ℂ)) z) w =
      (((fderiv ℝ (fderiv ℝ a) z) w) u : ℂ) := by
  rw [fderiv_complexOfReal
    ((contDiff_sourceSpatialRealDirectional ha u).differentiable
      (by norm_num))]
  rw [fderiv_sourceSpatialRealDirectional ha z u w]
theorem fderiv_holomorphicCoordinate_sourceSpatialReal {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z w : TorusCharacters.LogSpace n)
    (i : Fin n) :
    (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        holomorphicCoordinate
          (fun p : TorusCharacters.LogSpace n => (a p : ℂ))
          ξ i) z) w =
      ((((fderiv ℝ (fderiv ℝ a) z) w)
          (Pi.single i (1 : ℂ)) : ℂ) -
        Complex.I *
          (((fderiv ℝ (fderiv ℝ a) z) w)
            (Pi.single i Complex.I) : ℂ)) / 2 := by
  let e : TorusCharacters.LogSpace n :=
    Pi.single i (1 : ℂ)
  let ie : TorusCharacters.LogSpace n :=
    Pi.single i Complex.I
  let g : TorusCharacters.LogSpace n → ℂ :=
    fun ξ => ((fderiv ℝ a ξ) e : ℂ)
  let h : TorusCharacters.LogSpace n → ℂ :=
    fun ξ => ((fderiv ℝ a ξ) ie : ℂ)
  have had : Differentiable ℝ a :=
    ha.differentiable (by norm_num)
  have hg : Differentiable ℝ g :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_sourceSpatialRealDirectional ha e)).differentiable
      (by norm_num)
  have hh : Differentiable ℝ h :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_sourceSpatialRealDirectional ha ie)).differentiable
      (by norm_num)
  have hfun :
      (fun ξ : TorusCharacters.LogSpace n =>
        holomorphicCoordinate
          (fun p : TorusCharacters.LogSpace n => (a p : ℂ))
          ξ i) =
      (fun ξ : TorusCharacters.LogSpace n =>
        (g ξ - Complex.I * h ξ) * ((2 : ℂ)⁻¹)) := by
    funext ξ
    unfold holomorphicCoordinate
    rw [fderiv_complexOfReal had ξ (Pi.single i (1 : ℂ)),
      fderiv_complexOfReal had ξ (Pi.single i Complex.I)]
    rfl
  rw [hfun]
  have hder :=
    ((hg z).hasFDerivAt.sub
      ((hh z).hasFDerivAt.const_mul Complex.I)).mul_const
      ((2 : ℂ)⁻¹)
  have heval := congrArg
    (fun L : TorusCharacters.LogSpace n →L[ℝ] ℂ => L w)
    hder.fderiv
  calc
    _ = ((2 : ℂ)⁻¹) *
        ((fderiv ℝ g z) w -
          Complex.I * (fderiv ℝ h z) w) := by
      simpa [_root_.smul_apply,
        _root_.sub_apply, smul_eq_mul]
        using heval
    _ = _ := by
      change
        ((2 : ℂ)⁻¹) *
          ((fderiv ℝ
              (fun ξ : TorusCharacters.LogSpace n =>
                ((fderiv ℝ a ξ) e : ℂ)) z) w -
            Complex.I * (fderiv ℝ
              (fun ξ : TorusCharacters.LogSpace n =>
                ((fderiv ℝ a ξ) ie : ℂ)) z) w) = _
      rw [fderiv_sourceSpatialComplexRealDirectional ha z e w,
        fderiv_sourceSpatialComplexRealDirectional ha z ie w]
      dsimp [e, ie]
      ring
def sourceSpatialComplexHessianOfRealBilinear {n : ℕ}
    (B : TorusCharacters.LogSpace n →L[ℝ]
      TorusCharacters.LogSpace n →L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (((B (Pi.single j (1 : ℂ)) (Pi.single i (1 : ℂ)) : ℝ) : ℂ) +
      ((B (Pi.single j Complex.I) (Pi.single i Complex.I) : ℝ) : ℂ) +
      Complex.I *
        (((B (Pi.single j Complex.I) (Pi.single i (1 : ℂ)) : ℝ) : ℂ) -
          ((B (Pi.single j (1 : ℂ)) (Pi.single i Complex.I) : ℝ) : ℂ))) /
      4
theorem complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    complexHessian a z i j =
      sourceSpatialComplexHessianOfRealBilinear
        (fderiv ℝ (fderiv ℝ a) z) i j := by
  unfold sourceSpatialComplexHessianOfRealBilinear
  unfold complexHessian
  unfold barPartialCoordinate
  rw [fderiv_holomorphicCoordinate_sourceSpatialReal ha z
    (Pi.single j (1 : ℂ)) i,
    fderiv_holomorphicCoordinate_sourceSpatialReal ha z
      (Pi.single j Complex.I) i]
  ring_nf
  simp [Complex.I_sq]
  ring
theorem sourceSpatialComplexHessianOfRealBilinear_isHermitian {n : ℕ}
    (B : TorusCharacters.LogSpace n →L[ℝ]
      TorusCharacters.LogSpace n →L[ℝ] ℝ)
    (hB : ∀ u v : TorusCharacters.LogSpace n,
      B u v = B v u) :
    (sourceSpatialComplexHessianOfRealBilinear B).IsHermitian := by
  change (sourceSpatialComplexHessianOfRealBilinear B)ᴴ =
    sourceSpatialComplexHessianOfRealBilinear B
  ext i j
  simp only [Matrix.conjTranspose_apply,
    sourceSpatialComplexHessianOfRealBilinear, Complex.star_def,
    map_div₀, map_add, map_sub, map_mul, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I]
  rw [hB (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ)),
    hB (Pi.single i Complex.I) (Pi.single j Complex.I),
    hB (Pi.single i Complex.I) (Pi.single j (1 : ℂ)),
    hB (Pi.single i (1 : ℂ)) (Pi.single j Complex.I)]
  ring
theorem sourceCoverComplexHessian_isHermitian {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z : TorusCharacters.LogSpace n) :
    (sourceCoverComplexHessian a z).IsHermitian := by
  have hsym :
      ∀ u v : TorusCharacters.LogSpace n,
        ((fderiv ℝ (fderiv ℝ a) z) u) v =
          ((fderiv ℝ (fderiv ℝ a) z) v) u :=
    fun u v =>
      (ha.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq u v
  have hmatrix :
      sourceCoverComplexHessian a z =
        sourceSpatialComplexHessianOfRealBilinear
          (fderiv ℝ (fderiv ℝ a) z) := by
    ext i j
    exact complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      ha z i j
  rw [hmatrix]
  exact sourceSpatialComplexHessianOfRealBilinear_isHermitian _ hsym
def sourceJointSpatialSlice {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (τ : ℂ) (z : TorusCharacters.LogSpace n) : ℝ :=
  f (z, τ)
theorem contDiff_sourceJointSpatialSlice {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (τ : ℂ) :
    ContDiff ℝ 2 (sourceJointSpatialSlice f τ) := by
  exact hf.comp (contDiff_id.prodMk contDiff_const)
theorem fderiv_sourceJointSpatialSlice_apply {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : SourceJointComplexCover n → F}
    (hf : Differentiable ℝ f)
    (τ : ℂ)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n => f (ξ, τ)) z) v =
      (fderiv ℝ f (z, τ)) (v, 0) := by
  have hslice :=
    (hasFDerivAt_id (𝕜 := ℝ) z).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) τ z)
  have hcomp := (hf (z, τ)).hasFDerivAt.comp z hslice
  have heval := congrArg
    (fun L : TorusCharacters.LogSpace n →L[ℝ] F => L v)
    hcomp.fderiv
  simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    _root_.zero_apply] using heval
theorem fderiv_sourceJointRealDirectional {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q u w : SourceJointComplexCover n) :
    (fderiv ℝ
      (fun ξ : SourceJointComplexCover n => (fderiv ℝ f ξ) u) q) w =
      ((fderiv ℝ (fderiv ℝ f) q) w) u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) q
  have he := fderiv_clm_apply hd
    (differentiableAt_const (c := u))
  have happly := congrArg
    (fun L : SourceJointComplexCover n →L[ℝ] ℝ => L w) he
  simpa [ContinuousLinearMap.flip_apply] using happly
theorem sndFDeriv_sourceJointSpatialSlice {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (τ : ℂ)
    (z v w : TorusCharacters.LogSpace n) :
    ((fderiv ℝ
      (fderiv ℝ (sourceJointSpatialSlice f τ)) z) w) v =
      ((fderiv ℝ (fderiv ℝ f) (z, τ)) (w, 0)) (v, 0) := by
  have hslice := contDiff_sourceJointSpatialSlice hf τ
  have hfirst :
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ (sourceJointSpatialSlice f τ) ξ) v) =
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ f (ξ, τ)) (v, 0)) := by
    funext ξ
    exact fderiv_sourceJointSpatialSlice_apply
      (hf.differentiable (by norm_num)) τ ξ v
  have hdirectional : Differentiable ℝ
      (fun q : SourceJointComplexCover n =>
        (fderiv ℝ f q) (v, 0)) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num)
  calc
    _ = (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ (sourceJointSpatialSlice f τ) ξ) v) z) w :=
      (fderiv_sourceSpatialRealDirectional hslice z v w).symm
    _ = (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ f (ξ, τ)) (v, 0)) z) w := by rw [hfirst]
    _ = (fderiv ℝ
      (fun q : SourceJointComplexCover n =>
        (fderiv ℝ f q) (v, 0)) (z, τ)) (w, 0) :=
      fderiv_sourceJointSpatialSlice_apply hdirectional τ z w
    _ = _ :=
      fderiv_sourceJointRealDirectional hf (z, τ) (v, 0) (w, 0)
def sourceJointSpatialComplexHessian {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) :
    Matrix (Fin n) (Fin n) ℂ :=
  sourceCoverComplexHessian (sourceJointSpatialSlice f τ) z
theorem sourceJointSpatialComplexHessian_isHermitian {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) :
    (sourceJointSpatialComplexHessian f τ z).IsHermitian := by
  unfold sourceJointSpatialComplexHessian
  exact sourceCoverComplexHessian_isHermitian
    (contDiff_sourceJointSpatialSlice hf τ) z
end JetEnvelopeTrueRadialComplexHessian
namespace JetEnvelopeTrueRadialComplexHessianPositivity
open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian SchurConvexity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff
theorem sourceSpatialRealBasis_decomposition {n : ℕ}
    (x : TorusCharacters.LogSpace n) :
    x = ∑ i : Fin n,
      ((x i).re •
          (Pi.single i (1 : ℂ) : TorusCharacters.LogSpace n) +
        (x i).im •
          (Pi.single i Complex.I : TorusCharacters.LogSpace n)) := by
  classical
  calc
    x = ∑ i : Fin n, Pi.single i (x i) :=
      (Finset.univ_sum_single x).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      ext j
      by_cases h : j = i
      · subst j
        simp [Complex.real_smul, Complex.re_add_im]
      · simp [h]
theorem sourceSpatialRealBilinear_apply_eq_realBasis_sum {n : ℕ}
    (B : TorusCharacters.LogSpace n →L[ℝ]
      TorusCharacters.LogSpace n →L[ℝ] ℝ)
    (x y : TorusCharacters.LogSpace n) :
    B x y =
      ∑ i : Fin n, ∑ j : Fin n,
        ((x i).re * (y j).re *
          B (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ)) +
         (x i).re * (y j).im *
          B (Pi.single i (1 : ℂ)) (Pi.single j Complex.I) +
         (x i).im * (y j).re *
          B (Pi.single i Complex.I) (Pi.single j (1 : ℂ)) +
         (x i).im * (y j).im *
          B (Pi.single i Complex.I) (Pi.single j Complex.I)) := by
  classical
  let u : Fin n → TorusCharacters.LogSpace n := fun i =>
    (x i).re •
        (Pi.single i (1 : ℂ) : TorusCharacters.LogSpace n) +
      (x i).im •
        (Pi.single i Complex.I : TorusCharacters.LogSpace n)
  let v : Fin n → TorusCharacters.LogSpace n := fun j =>
    (y j).re •
        (Pi.single j (1 : ℂ) : TorusCharacters.LogSpace n) +
      (y j).im •
        (Pi.single j Complex.I : TorusCharacters.LogSpace n)
  have hx : x = ∑ i, u i := sourceSpatialRealBasis_decomposition x
  have hy : y = ∑ j, v j := sourceSpatialRealBasis_decomposition y
  calc
    B x y = B (∑ i, u i) (∑ j, v j) := by rw [← hx, ← hy]
    _ = ∑ i, B (u i) (∑ j, v j) := by
      simpa only [ContinuousLinearMap.flip_apply] using
        (map_sum (B.flip (∑ j, v j)) u Finset.univ)
    _ = ∑ i, ∑ j, B (u i) (v j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact map_sum (B (u i)) v Finset.univ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [u, v]
      simp only [map_add, map_smul, _root_.add_apply,
        _root_.smul_apply, smul_eq_mul]
      ring
theorem sourceSpatialComplexHessianOfRealBilinear_quadratic {n : ℕ}
    (B : TorusCharacters.LogSpace n →L[ℝ]
      TorusCharacters.LogSpace n →L[ℝ] ℝ)
    (hsymm : ∀ u v : TorusCharacters.LogSpace n,
      B u v = B v u)
    (x : TorusCharacters.LogSpace n) :
    star x ⬝ᵥ
        (sourceSpatialComplexHessianOfRealBilinear B *ᵥ x) =
      (((B (star x) (star x) +
        B (Complex.I • star x) (Complex.I • star x)) / 4 : ℝ) : ℂ) := by
  classical
  let Q : Fin n → Fin n → ℂ := fun i j =>
    star (x i) * (sourceSpatialComplexHessianOfRealBilinear B i j) * x j
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, Q i j) =
        ∑ i : Fin n, ∑ j : Fin n, Q j i := by
    rw [Finset.sum_comm]
  have havg :
      (∑ i : Fin n, ∑ j : Fin n, Q i j) =
        ∑ i : Fin n, ∑ j : Fin n, (Q i j + Q j i) / 2 := by
    calc
      _ = ((∑ i : Fin n, ∑ j : Fin n, Q i j) +
        (∑ i : Fin n, ∑ j : Fin n, Q j i)) / 2 := by
          rw [← hswap]
          ring
      _ = _ := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib, Finset.sum_div]
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, Q i j := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [Q]
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n, (Q i j + Q j i) / 2 :=
      havg
    _ = _ := by
      rw [sourceSpatialRealBilinear_apply_eq_realBasis_sum
          B (star x) (star x),
        sourceSpatialRealBilinear_apply_eq_realBasis_sum
          B (Complex.I • star x) (Complex.I • star x)]
      simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul,
        Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.I_mul_re, Complex.I_mul_im]
      push_cast
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [Q, sourceSpatialComplexHessianOfRealBilinear]
      rw [hsymm (Pi.single j (1 : ℂ)) (Pi.single i (1 : ℂ)),
        hsymm (Pi.single j Complex.I) (Pi.single i Complex.I),
        hsymm (Pi.single j Complex.I) (Pi.single i (1 : ℂ)),
        hsymm (Pi.single j (1 : ℂ)) (Pi.single i Complex.I)]
      rw [← Complex.re_add_im (x i), ← Complex.re_add_im (x j)]
      simp only [map_add, map_mul,
        Complex.conj_ofReal, Complex.conj_I,
        Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im,
        mul_zero, mul_one,
        add_zero, zero_add, sub_zero]
      ring_nf
      simp only [Complex.I_sq]
      ring
theorem sourceCoverComplexHessian_quadratic {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z x : TorusCharacters.LogSpace n) :
    star x ⬝ᵥ (sourceCoverComplexHessian a z *ᵥ x) =
      (((((fderiv ℝ (fderiv ℝ a) z) (star x)) (star x) +
          ((fderiv ℝ (fderiv ℝ a) z) (Complex.I • star x))
            (Complex.I • star x)) / 4 : ℝ) : ℂ) := by
  have hsymm :
      ∀ u v : TorusCharacters.LogSpace n,
        ((fderiv ℝ (fderiv ℝ a) z) u) v =
          ((fderiv ℝ (fderiv ℝ a) z) v) u :=
    fun u v =>
      (ha.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq u v
  have hmatrix :
      sourceCoverComplexHessian a z =
        sourceSpatialComplexHessianOfRealBilinear
          (fderiv ℝ (fderiv ℝ a) z) := by
    ext i j
    exact complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      ha z i j
  rw [hmatrix]
  exact sourceSpatialComplexHessianOfRealBilinear_quadratic
    (fderiv ℝ (fderiv ℝ a) z) hsymm x
theorem sourceJointSpatialComplexHessian_quadratic_eq_realLevi
    {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (τ : ℂ)
    (z x : TorusCharacters.LogSpace n) :
    star x ⬝ᵥ (sourceJointSpatialComplexHessian f τ z *ᵥ x) =
      (sourceJointRealLeviQuadratic f (z, τ) (star x, 0) : ℂ) := by
  unfold sourceJointSpatialComplexHessian
  rw [sourceCoverComplexHessian_quadratic
    (contDiff_sourceJointSpatialSlice hf τ) z x]
  unfold sourceJointRealLeviQuadratic
  rw [sndFDeriv_sourceJointSpatialSlice hf τ z (star x) (star x),
    sndFDeriv_sourceJointSpatialSlice hf τ z
      (Complex.I • star x) (Complex.I • star x)]
  simp
end JetEnvelopeTrueRadialComplexHessianPositivity
namespace JetEnvelopeTrueRadialPerturbedComplexHessianPositiveDefinite
open Set Function Matrix
open JetEnvelopeTrueRadialComplexHessian SchurConvexity WeightedDolbeaultBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
  Topology ContDiff
theorem sndFDeriv_sourceSpatialRealAffine {n : ℕ}
    {a b : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b)
    (c d : ℝ)
    (z u v : TorusCharacters.LogSpace n) :
    ((fderiv ℝ
      (fderiv ℝ
        (fun ξ : TorusCharacters.LogSpace n =>
          c * a ξ + d * b ξ)) z) u) v =
      c * ((fderiv ℝ (fderiv ℝ a) z) u) v +
        d * ((fderiv ℝ (fderiv ℝ b) z) u) v := by
  have hda : Differentiable ℝ a :=
    ha.differentiable (by norm_num)
  have hdb : Differentiable ℝ b :=
    hb.differentiable (by norm_num)
  have hcomb : ContDiff ℝ 2
      (fun ξ : TorusCharacters.LogSpace n =>
        c * a ξ + d * b ξ) :=
    (contDiff_const.mul ha).add (contDiff_const.mul hb)
  have hfirst :
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ
          (fun η : TorusCharacters.LogSpace n =>
            c * a η + d * b η) ξ) v) =
      (fun ξ : TorusCharacters.LogSpace n =>
        c * (fderiv ℝ a ξ) v + d * (fderiv ℝ b ξ) v) := by
    funext ξ
    change (fderiv ℝ
      ((fun η : TorusCharacters.LogSpace n => c * a η) +
        (fun η : TorusCharacters.LogSpace n => d * b η))
      ξ) v = _
    rw [fderiv_add ((hda ξ).const_mul c) ((hdb ξ).const_mul d),
      fderiv_const_mul (hda ξ) c,
      fderiv_const_mul (hdb ξ) d]
    simp [      smul_eq_mul]
  have hga : Differentiable ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ a ξ) v) :=
    (contDiff_sourceSpatialRealDirectional ha v).differentiable
      (by norm_num)
  have hgb : Differentiable ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ b ξ) v) :=
    (contDiff_sourceSpatialRealDirectional hb v).differentiable
      (by norm_num)
  calc
    _ = (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ
          (fun η : TorusCharacters.LogSpace n =>
            c * a η + d * b η) ξ) v) z) u :=
      (fderiv_sourceSpatialRealDirectional hcomb z v u).symm
    _ = (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        c * (fderiv ℝ a ξ) v + d * (fderiv ℝ b ξ) v) z) u := by
      rw [hfirst]
    _ = _ := by
      change (fderiv ℝ
        ((fun ξ : TorusCharacters.LogSpace n =>
          c * (fderiv ℝ a ξ) v) +
          (fun ξ : TorusCharacters.LogSpace n =>
            d * (fderiv ℝ b ξ) v)) z) u = _
      rw [fderiv_add ((hga z).const_mul c) ((hgb z).const_mul d),
        fderiv_const_mul (hga z) c,
        fderiv_const_mul (hgb z) d]
      simp only [_root_.add_apply,
        _root_.smul_apply, smul_eq_mul]
      rw [fderiv_sourceSpatialRealDirectional ha z v u,
        fderiv_sourceSpatialRealDirectional hb z v u]
theorem sourceCoverComplexHessian_realAffine {n : ℕ}
    {a b : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b)
    (c d : ℝ)
    (z : TorusCharacters.LogSpace n) :
    sourceCoverComplexHessian
        (fun ξ : TorusCharacters.LogSpace n =>
          c * a ξ + d * b ξ) z =
      c • sourceCoverComplexHessian a z +
        d • sourceCoverComplexHessian b z := by
  have hcomb : ContDiff ℝ 2
      (fun ξ : TorusCharacters.LogSpace n =>
        c * a ξ + d * b ξ) :=
    (contDiff_const.mul ha).add (contDiff_const.mul hb)
  ext i j
  change complexHessian
      (fun ξ : TorusCharacters.LogSpace n =>
        c * a ξ + d * b ξ) z i j =
    c • complexHessian a z i j + d • complexHessian b z i j
  rw [complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      hcomb z i j,
    complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      ha z i j,
    complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      hb z i j]
  unfold sourceSpatialComplexHessianOfRealBilinear
  rw [sndFDeriv_sourceSpatialRealAffine ha hb c d z
      (Pi.single j (1 : ℂ)) (Pi.single i (1 : ℂ)),
    sndFDeriv_sourceSpatialRealAffine ha hb c d z
      (Pi.single j Complex.I) (Pi.single i Complex.I),
    sndFDeriv_sourceSpatialRealAffine ha hb c d z
      (Pi.single j Complex.I) (Pi.single i (1 : ℂ)),
    sndFDeriv_sourceSpatialRealAffine ha hb c d z
      (Pi.single j (1 : ℂ)) (Pi.single i Complex.I)]
  push_cast
  simp only [Complex.real_smul]
  ring
end JetEnvelopeTrueRadialPerturbedComplexHessianPositiveDefinite
namespace EnvelopeTorusDescent
open Set Function Filter MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic EnvelopeSmoothing
open scoped Topology ContDiff
def sourceJointTimeDirection (n : ℕ) :
    SourceJointComplexCover n :=
  (0, (1 / 2 : ℂ))
theorem sourceRealFderiv_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (d : E)
    (hperiod : Function.Periodic F d) :
    Function.Periodic (fderiv ℝ F) d := by
  intro x
  have he : (fun y : E => F (y + d)) = F :=
    funext hperiod
  have hd := congrArg (fun G : E → ℝ => fderiv ℝ G x) he
  change fderiv ℝ (fun y : E => F (y + d)) x =
    fderiv ℝ F x at hd
  rw [fderiv_comp_add_right] at hd
  exact hd
end EnvelopeTorusDescent
namespace EnvelopeGeneralTorusDescent
open Set Function Filter MeasureTheory
open ComplexKillingSaturationBridge MatrixTorusBochnerIdentity JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeRightDerivative EnvelopeSmoothing EnvelopeTorusDescent
open scoped Topology ContDiff
def jointSourceCoverTimeSlice {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (z : TorusCharacters.LogSpace n) : ℝ :=
  F (sourceJointTimeEmbedding z t)
theorem continuous_jointSourceCoverTimeSlice {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : Continuous F) (t : ℝ) :
    Continuous (jointSourceCoverTimeSlice F t) := by
  unfold jointSourceCoverTimeSlice
  apply hF.comp
  unfold sourceJointTimeEmbedding
  fun_prop
theorem jointSourceCoverTimeSlice_spatial_periodic {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) (m : Fin n → ℤ) :
    Function.Periodic (jointSourceCoverTimeSlice F t)
      (TorusCharacters.imaginaryShift m) := by
  intro z
  have h := hperiod m (sourceJointTimeEmbedding z t)
  simpa [jointSourceCoverTimeSlice, sourceJointTimeEmbedding] using h
def jointSourceTorusWeight {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  (torusScalarRepresentative
    (fun z : TorusCharacters.LogSpace n =>
      (jointSourceCoverTimeSlice F t z : ℂ)) q).re
theorem jointSourceTorusWeight_eq_cover {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    jointSourceTorusWeight F t q =
      F (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
  rfl
theorem continuous_jointSourceTorusWeight {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : Continuous F)
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) :
    Continuous (jointSourceTorusWeight F t) := by
  unfold jointSourceTorusWeight
  apply Complex.continuous_re.comp
  apply continuous_torusScalarRepresentative_of_periodic
  · exact Complex.continuous_ofReal.comp
      (continuous_jointSourceCoverTimeSlice hF t)
  · intro m z
    exact congrArg Complex.ofReal
      (jointSourceCoverTimeSlice_spatial_periodic hperiod t m z)
def jointSourceCoverVelocity {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (q : SourceJointComplexCover n) : ℝ :=
  (fderiv ℝ F q) (sourceJointTimeDirection n)
def jointSourceCoverAcceleration {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (q : SourceJointComplexCover n) : ℝ :=
  (fderiv ℝ (jointSourceCoverVelocity F) q)
    (sourceJointTimeDirection n)
theorem contDiff_jointSourceCoverVelocity {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (jointSourceCoverVelocity F) := by
  unfold jointSourceCoverVelocity
  exact (hF.fderiv_right (m := 1) (by norm_num)).clm_apply
    contDiff_const
theorem jointSourceCoverVelocity_spatial_periodic {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (m : Fin n → ℤ) :
    Function.Periodic (jointSourceCoverVelocity F)
      (TorusCharacters.imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold jointSourceCoverVelocity
  exact congrArg (fun L => L (sourceJointTimeDirection n))
    (sourceRealFderiv_periodic F
      (TorusCharacters.imaginaryShift m, (0 : ℂ))
      (hperiod m) q)
def jointSourceTorusVelocity {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  jointSourceTorusWeight (jointSourceCoverVelocity F) t q
def jointSourceTorusAcceleration {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  jointSourceTorusWeight (jointSourceCoverAcceleration F) t q
theorem jointSourceTorusAcceleration_eq_cover {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    jointSourceTorusAcceleration F t q =
      jointSourceCoverAcceleration F
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
  rfl
theorem continuous_jointSourceTorusVelocity {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) :
    Continuous (jointSourceTorusVelocity F t) := by
  unfold jointSourceTorusVelocity
  exact continuous_jointSourceTorusWeight
    (contDiff_jointSourceCoverVelocity hF).continuous
    (jointSourceCoverVelocity_spatial_periodic hperiod) t
end EnvelopeGeneralTorusDescent
namespace TorusHessianPositiveDefinite
open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialComplexHessian
open EnvelopeGeneralTorusDescent WeightedTorusGraphWeakBridge WeightedTorusDolbeault
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology ContDiff
theorem angularCoverPotential_jointSourceTorusWeight_eq
    {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) :
    angularCoverPotential (jointSourceTorusWeight F t) =
      sourceJointSpatialSlice F (t / 2 : ℂ) := by
  funext z
  let G : TorusCharacters.LogSpace n → ℂ :=
    fun w => (jointSourceCoverTimeSlice F t w : ℂ)
  have hG : ∀ m : Fin n → ℤ,
      Function.Periodic G
        (TorusCharacters.imaginaryShift m) := by
    intro m w
    exact congrArg Complex.ofReal
      (jointSourceCoverTimeSlice_spatial_periodic hperiod t m w)
  have hrec := congrFun
    (complexTorusCoverLift_torusScalarRepresentative_eq G hG) z
  exact congrArg Complex.re hrec
end TorusHessianPositiveDefinite
namespace TorusMatrixSquareRootContinuity
open Set Function Filter Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology ContDiff
theorem continuous_complexMatrixSquareRoot
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    {H : X → Matrix (Fin n) (Fin n) ℂ}
    (hcont : Continuous H)
    (hH : ∀ x, (H x).PosSemidef) :
    Continuous (fun x => CFC.sqrt (H x)) := by
  have hnonneg : ∀ x : X,
      (0 : Matrix (Fin n) (Fin n) ℂ) ≤ H x :=
    fun x => (hH x).nonneg
  have hcfc : Continuous
      (fun x : X =>
        cfc (fun t : NNReal => NNReal.sqrt t) (H x)) := by
    exact Continuous.cfc_nnreal_of_mem_nhdsSet
      (A := Matrix (Fin n) (Fin n) ℂ)
      (X := X)
      (a := H)
      (s := (Set.univ : Set NNReal))
      (fun t : NNReal => NNReal.sqrt t)
      Filter.univ_mem
      hcont
      (ha' := hnonneg)
      (hf := NNReal.continuous_sqrt.continuousOn)
  simp_rw [CFC.sqrt_eq_cfc]
  exact hcfc
theorem continuous_complexMatrixSquareRoot_inverse
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    {H : X → Matrix (Fin n) (Fin n) ℂ}
    (hcont : Continuous H)
    (hH : ∀ x, (H x).PosDef) :
    Continuous (fun x => (CFC.sqrt (H x))⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hdet : (CFC.sqrt (H x)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (hH x).isStrictlyPositive.sqrt.posDef.isUnit).ne_zero
  have hinv : ContinuousAt Ring.inverse (CFC.sqrt (H x)).det := by
    simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ hdet)
  have hsqrt : ContinuousAt (fun y : X => CFC.sqrt (H y)) x :=
    (continuous_complexMatrixSquareRoot hcont
      (fun y => (hH y).posSemidef)).continuousAt
  have hcomp :
      ContinuousAt
        ((fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) ∘
          (fun y : X => CFC.sqrt (H y))) x :=
    ContinuousAt.comp
      (f := fun y : X => CFC.sqrt (H y))
      (g := fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹)
      (continuousAt_matrix_inv (CFC.sqrt (H x)) hinv) hsqrt
  exact hcomp
end TorusMatrixSquareRootContinuity
namespace BergmanJetStrictRadialRegularizer
open Set Function Filter MeasureTheory Matrix
open TorusCharacters SupportFunction LatticeAsymptotics BergmanAsymptotics
open ComplexMatrixWeightedHilbert MatrixTorusBochnerBridge MatrixTorusBochnerCore
open WeightedDolbeaultBochnerIdentity SchurConvexity
open scoped BigOperators ENNReal Topology ContDiff MatrixOrder
  ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
def momentBodyInteriorRadius
    {n : ℕ} (K : CenteredBody n) : ℝ :=
  ((Metric.isOpen_iff.mp isOpen_interior)
    (0 : Space n) (zero_mem_interior K)).choose
theorem momentBodyInteriorRadius_pos
    {n : ℕ} (K : CenteredBody n) :
    0 < momentBodyInteriorRadius K :=
  ((Metric.isOpen_iff.mp isOpen_interior)
    (0 : Space n) (zero_mem_interior K)).choose_spec.1
def momentBodyStrictScale
    {n : ℕ} (K : CenteredBody n) : ℝ :=
  momentBodyInteriorRadius K / 2
theorem momentBodyStrictScale_pos
    {n : ℕ} (K : CenteredBody n) :
    0 < momentBodyStrictScale K :=
  half_pos (momentBodyInteriorRadius_pos K)
def momentStrictRadialCoordinate (y : ℝ) : ℝ :=
  Real.log (Real.exp y + Real.exp (-y))
theorem momentStrictRadialCoordinate_denominator_pos
    (y : ℝ) : 0 < Real.exp y + Real.exp (-y) :=
  add_pos (Real.exp_pos y) (Real.exp_pos (-y))
theorem contDiff_momentStrictRadialCoordinate :
    ContDiff ℝ ∞ momentStrictRadialCoordinate := by
  unfold momentStrictRadialCoordinate
  apply (Real.contDiff_exp.add
    (Real.contDiff_exp.comp contDiff_neg)).log
  intro y
  exact (momentStrictRadialCoordinate_denominator_pos y).ne'
def momentStrictRadialCoordinateDerivative (y : ℝ) : ℝ :=
  (Real.exp y - Real.exp (-y)) /
    (Real.exp y + Real.exp (-y))
theorem hasDerivAt_momentStrictRadialCoordinate (y : ℝ) :
    HasDerivAt momentStrictRadialCoordinate
      (momentStrictRadialCoordinateDerivative y) y := by
  have hneg : HasDerivAt (fun x : ℝ => Real.exp (-x))
      (-Real.exp (-y)) y := by
    have hcomp : HasDerivAt
        (Real.exp ∘ fun x : ℝ => -x)
        (Real.exp (-y) * (-1)) y :=
      (Real.hasDerivAt_exp (-y)).comp y
        (hasDerivAt_id y).neg
    refine (hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    ring
  have hsum : HasDerivAt
      (fun x : ℝ => Real.exp x + Real.exp (-x))
      (Real.exp y - Real.exp (-y)) y := by
    refine ((Real.hasDerivAt_exp y).fun_add hneg).congr_deriv ?_
    ring
  exact hsum.log
    (momentStrictRadialCoordinate_denominator_pos y).ne'
def momentStrictRadialCoordinateSecond (y : ℝ) : ℝ :=
  4 / (Real.exp y + Real.exp (-y)) ^ 2
theorem hasDerivAt_momentStrictRadialCoordinateDerivative
    (y : ℝ) :
    HasDerivAt momentStrictRadialCoordinateDerivative
      (momentStrictRadialCoordinateSecond y) y := by
  have hneg : HasDerivAt (fun x : ℝ => Real.exp (-x))
      (-Real.exp (-y)) y := by
    have hcomp : HasDerivAt
        (Real.exp ∘ fun x : ℝ => -x)
        (Real.exp (-y) * (-1)) y :=
      (Real.hasDerivAt_exp (-y)).comp y
        (hasDerivAt_id y).neg
    refine (hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    ring
  have hnum : HasDerivAt
      (fun x : ℝ => Real.exp x - Real.exp (-x))
      (Real.exp y + Real.exp (-y)) y := by
    refine ((Real.hasDerivAt_exp y).fun_sub hneg).congr_deriv ?_
    ring
  have hden : HasDerivAt
      (fun x : ℝ => Real.exp x + Real.exp (-x))
      (Real.exp y - Real.exp (-y)) y := by
    refine ((Real.hasDerivAt_exp y).fun_add hneg).congr_deriv ?_
    ring
  have h := hnum.fun_div hden
    (momentStrictRadialCoordinate_denominator_pos y).ne'
  change HasDerivAt
    (fun x : ℝ =>
      (Real.exp x - Real.exp (-x)) /
        (Real.exp x + Real.exp (-x)))
    (4 / (Real.exp y + Real.exp (-y)) ^ 2) y
  have he : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add]
    simp
  refine h.congr_deriv ?_
  congr 1
  nlinarith [he]
theorem momentStrictRadialCoordinateSecond_pos (y : ℝ) :
    0 < momentStrictRadialCoordinateSecond y := by
  unfold momentStrictRadialCoordinateSecond
  positivity
theorem abs_le_momentStrictRadialCoordinate (y : ℝ) :
    |y| ≤ momentStrictRadialCoordinate y := by
  have hsum : Real.exp |y| ≤ Real.exp y + Real.exp (-y) := by
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      exact le_add_of_nonneg_right (Real.exp_pos (-y)).le
    · rw [abs_of_neg (lt_of_not_ge hy)]
      exact le_add_of_nonneg_left (Real.exp_pos y).le
  have hmono := Real.strictMonoOn_log.monotoneOn
    (show Real.exp |y| ∈ Set.Ioi (0 : ℝ) from Real.exp_pos _)
    (show Real.exp y + Real.exp (-y) ∈ Set.Ioi (0 : ℝ) from
      momentStrictRadialCoordinate_denominator_pos y)
    hsum
  simpa [momentStrictRadialCoordinate] using hmono
def momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) : ℝ :=
  ∑ i : Fin n,
    momentStrictRadialCoordinate
      (momentBodyStrictScale K * x i)
theorem contDiff_momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n) :
    ContDiff ℝ ∞ (momentBodyStrictRadialPotential K) := by
  unfold momentBodyStrictRadialPotential
  apply ContDiff.sum
  intro i _
  exact contDiff_momentStrictRadialCoordinate.comp
    (contDiff_const.mul (contDiff_apply ℝ ℝ i))
theorem momentBodyStrictRadialPotential_sum_abs_lower
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    momentBodyStrictScale K * (∑ i : Fin n, |x i|) ≤
      momentBodyStrictRadialPotential K x := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := abs_le_momentStrictRadialCoordinate
    (momentBodyStrictScale K * x i)
  rwa [abs_mul,
    abs_of_pos (momentBodyStrictScale_pos K)] at h
def momentBodyStrictRadialGradient
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) : Space n →L[ℝ] ℝ :=
  ∑ i : Fin n,
    (momentBodyStrictScale K *
      momentStrictRadialCoordinateDerivative
        (momentBodyStrictScale K * x i)) •
      (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ)
theorem hasFDerivAt_momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    HasFDerivAt (momentBodyStrictRadialPotential K)
      (momentBodyStrictRadialGradient K x) x := by
  unfold momentBodyStrictRadialPotential
    momentBodyStrictRadialGradient
  have hterm (i : Fin n) :
      HasFDerivAt
        (fun y : Space n =>
          momentStrictRadialCoordinate
            (momentBodyStrictScale K * y i))
        ((momentBodyStrictScale K *
          momentStrictRadialCoordinateDerivative
            (momentBodyStrictScale K * x i)) •
          (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
        x := by
    let c : ℝ := momentBodyStrictScale K
    let P : Space n →L[ℝ] ℝ :=
      ContinuousLinearMap.proj i
    have hc : HasFDerivAt (fun y : Space n => c * y i)
        (c • P) x := by
      exact P.hasFDerivAt.const_mul c
    have h :=
      (hasDerivAt_momentStrictRadialCoordinate (c * x i))
        |>.comp_hasFDerivAt x hc
    simpa [Function.comp_def, c, P, smul_smul, mul_comm] using h
  exact HasFDerivAt.fun_sum
    (u := Finset.univ) (fun i _ => hterm i)
theorem fderiv_momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    fderiv ℝ (momentBodyStrictRadialPotential K) x =
      momentBodyStrictRadialGradient K x :=
  (hasFDerivAt_momentBodyStrictRadialPotential K x).fderiv
def momentBodyStrictRadialHessianDiagonal
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) (i : Fin n) : ℝ :=
  momentBodyStrictScale K ^ 2 *
    momentStrictRadialCoordinateSecond
      (momentBodyStrictScale K * x i)
theorem momentBodyStrictRadialHessianDiagonal_pos
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) (i : Fin n) :
    0 < momentBodyStrictRadialHessianDiagonal K x i := by
  unfold momentBodyStrictRadialHessianDiagonal
  exact mul_pos (sq_pos_of_pos (momentBodyStrictScale_pos K))
    (momentStrictRadialCoordinateSecond_pos _)
theorem hasFDerivAt_momentBodyStrictRadialGradientCoefficient
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) (i : Fin n) :
    HasFDerivAt
      (fun y : Space n =>
        momentBodyStrictScale K *
          momentStrictRadialCoordinateDerivative
            (momentBodyStrictScale K * y i))
      (momentBodyStrictRadialHessianDiagonal K x i •
        (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
      x := by
  let c : ℝ := momentBodyStrictScale K
  let P : Space n →L[ℝ] ℝ :=
    ContinuousLinearMap.proj i
  have hinner : HasFDerivAt
      (fun y : Space n => c * y i) (c • P) x :=
    P.hasFDerivAt.const_mul c
  have hfirst :=
    (hasDerivAt_momentStrictRadialCoordinateDerivative
      (c * x i)).comp_hasFDerivAt x hinner
  have hscaled := hfirst.const_mul c
  simpa [Function.comp_def, c, P,
    momentBodyStrictRadialHessianDiagonal,
    smul_smul, pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled
theorem fderiv_momentBodyStrictRadialGradient_apply
    {n : ℕ} (K : CenteredBody n)
    (x v w : Space n) :
    ((fderiv ℝ (momentBodyStrictRadialGradient K) x) v) w =
      ∑ i : Fin n,
        momentBodyStrictRadialHessianDiagonal K x i *
          v i * w i := by
  have h : HasFDerivAt
      (momentBodyStrictRadialGradient K)
      (∑ i : Fin n,
        (momentBodyStrictRadialHessianDiagonal K x i •
          (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ)).smulRight
            (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
      x := by
    unfold momentBodyStrictRadialGradient
    have hterm (i : Fin n) :
        HasFDerivAt
          (fun y : Space n =>
            (momentBodyStrictScale K *
              momentStrictRadialCoordinateDerivative
                (momentBodyStrictScale K * y i)) •
              (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
          ((momentBodyStrictRadialHessianDiagonal K x i •
            (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ)).smulRight
              (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
          x :=
      (hasFDerivAt_momentBodyStrictRadialGradientCoefficient
        K x i).smul_const
        (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ)
    exact HasFDerivAt.fun_sum
      (u := Finset.univ) (fun i _ => hterm i)
  rw [h.fderiv]
  simp [mul_assoc]
theorem fderiv_fderiv_momentBodyStrictRadialPotential_apply
    {n : ℕ} (K : CenteredBody n)
    (x v w : Space n) :
    ((fderiv ℝ
      (fderiv ℝ (momentBodyStrictRadialPotential K)) x) v) w =
      ∑ i : Fin n,
        momentBodyStrictRadialHessianDiagonal K x i *
          v i * w i := by
  have heq :
      fderiv ℝ (momentBodyStrictRadialPotential K) =
        momentBodyStrictRadialGradient K := by
    funext y
    exact fderiv_momentBodyStrictRadialPotential K y
  rw [heq]
  exact fderiv_momentBodyStrictRadialGradient_apply K x v w
theorem sourceMatrixHessian_momentBodyStrictRadialPotential_eq_diagonal
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    sourceMatrixHessian (momentBodyStrictRadialPotential K) x =
      Matrix.diagonal
        (momentBodyStrictRadialHessianDiagonal K x) := by
  classical
  ext i j
  unfold sourceMatrixHessian actualHessianMatrix
  rw [LinearMap.toMatrix₂'_apply]
  change
    ((fderiv ℝ
      (fderiv ℝ (momentBodyStrictRadialPotential K)) x)
      (Pi.single i (1 : ℝ)))
      (Pi.single j (1 : ℝ)) =
      Matrix.diagonal
        (momentBodyStrictRadialHessianDiagonal K x) i j
  rw [fderiv_fderiv_momentBodyStrictRadialPotential_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have hz : (Pi.single i (1 : ℝ) : Space n) b = 0 := by
        simp [hb]
      simp [hz]
    · simp
  · rw [Matrix.diagonal_apply, if_neg hij,
      Finset.sum_eq_single i]
    · simp [hij]
    · intro b _ hb
      have hz : (Pi.single i (1 : ℝ) : Space n) b = 0 := by
        simp [hb]
      simp [hz]
    · simp
theorem sourceCoverComplexHessian_momentBodyStrictRadialPotential_eq_diagonal
    {n : ℕ} (K : CenteredBody n)
    (z : LogSpace n) :
    sourceCoverComplexHessian
      (matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)) z =
      Matrix.diagonal
        (fun i : Fin n =>
          (momentBodyStrictRadialHessianDiagonal K
            (sourceCoverRadialLinear n z) i : ℂ)) := by
  classical
  ext i j
  change
    complexHessian
      (matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)) z i j =
      Matrix.diagonal
        (fun k : Fin n =>
          (momentBodyStrictRadialHessianDiagonal K
            (sourceCoverRadialLinear n z) k : ℂ)) i j
  rw [complexHessian_matrixSourceCoverPotential_eq_real
    ((contDiff_infty.mp
      (contDiff_momentBodyStrictRadialPotential K)) 2) z i j,
    sourceMatrixHessian_momentBodyStrictRadialPotential_eq_diagonal]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]
theorem sourceCoverComplexHessian_momentBodyStrictRadialPotential_posDef
    {n : ℕ} (K : CenteredBody n)
    (z : LogSpace n) :
    (sourceCoverComplexHessian
      (matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)) z).PosDef := by
  rw [sourceCoverComplexHessian_momentBodyStrictRadialPotential_eq_diagonal]
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast
    momentBodyStrictRadialHessianDiagonal_pos
      K (sourceCoverRadialLinear n z) i
end BergmanJetStrictRadialRegularizer
namespace BergmanJetPartitionEndpoint
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentTargetDanskin
open MomentFirstVariation MomentRegularity BergmanJetTorusEnvelope BergmanJetTorusCoercivity
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative LogPartitionConvexity
open scoped BigOperators ENNReal Topology
def momentBodyOptimizer
    {n : ℕ} (K : CenteredBody n) :
    SourceFiniteEnergyPotential K :=
  Classical.choose (exists_exact_optimizer_gradientPushforward_eq K)
theorem momentBodyOptimizer_transport
    {n : ℕ} (K : CenteredBody n) :
    finiteEnergySourceGradientPushforward (momentBodyOptimizer K) =
      normalizedTargetBodyMeasure K := by
  exact (Classical.choose_spec
    (exists_exact_optimizer_gradientPushforward_eq K)).2.2
def momentBodyTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n)
    (t : ℝ) (q : LogTorus n) : ℝ :=
  momentTorusEnvelopeTimeSlice
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p q t
@[simp] theorem momentBodyTorusWeight_zero
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (q : LogTorus n) :
    momentBodyTorusWeight K p 0 q =
      momentNormalizedPotential (momentBodyOptimizer K) q.1 := by
  exact momentTorusEnvelopeTimeSlice_zero
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p q
theorem momentBodyTorusWeight_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : t ≤ 0)
    (q : LogTorus n) :
    momentBodyTorusWeight K p t q =
      momentNormalizedPotential (momentBodyOptimizer K) q.1 := by
  unfold momentBodyTorusWeight momentTorusEnvelopeTimeSlice
  rw [momentEnvelopeTimeSlice_of_nonpositive
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p
    (sourceTorusCoverPoint q) ht,
    realLogCoordinate_sourceTorusCoverPoint]
theorem integrable_exp_neg_momentBodyTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Integrable
      (fun q : LogTorus n =>
        Real.exp (-momentBodyTorusWeight K p t q))
      (sourceTorusBaseMeasure n) := by
  exact integrable_exp_neg_momentTorusEnvelopeTimeSlice
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p t
def momentBodyPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) : ℝ :=
  sourcePartition (momentBodyTorusWeight K p) t
theorem momentBodyPartition_eq_integral
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    momentBodyPartition K p t =
      ∫ q : LogTorus n,
        Real.exp (-momentBodyTorusWeight K p t q)
          ∂(sourceTorusBaseMeasure n) := by
  rfl
theorem momentBodyPartition_pos
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    0 < momentBodyPartition K p t := by
  exact momentTorusEnvelopePartition_pos
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p t
theorem momentBodyPartition_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : t ≤ 0) :
    momentBodyPartition K p t =
      normalizedVolume K.carrier := by
  rw [momentBodyPartition_eq_integral]
  calc
    (∫ q : LogTorus n,
        Real.exp (-momentBodyTorusWeight K p t q)
          ∂(sourceTorusBaseMeasure n)) =
        ∫ q : LogTorus n,
          Real.exp
            (-momentNormalizedPotential
              (momentBodyOptimizer K) q.1) * (1 : ℝ)
          ∂((volume : Measure (Space n)).prod
            (angularMeasure n)) := by
          unfold sourceTorusBaseMeasure
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with q
          rw [momentBodyTorusWeight_of_nonpositive K p ht q]
          simp
    _ = (∫ x : Space n,
          Real.exp
            (-momentNormalizedPotential
              (momentBodyOptimizer K) x)
            ∂(volume : Measure (Space n))) *
          (∫ _ : AngularTorus n, (1 : ℝ) ∂(angularMeasure n)) :=
      MeasureTheory.integral_prod_mul
        (μ := (volume : Measure (Space n)))
        (ν := angularMeasure n)
        (fun x : Space n =>
          Real.exp
            (-momentNormalizedPotential
              (momentBodyOptimizer K) x))
        (fun _ : AngularTorus n => (1 : ℝ))
    _ = normalizedVolume K.carrier := by
      rw [integral_exp_neg_momentNormalizedPotential
        (momentBodyOptimizer K)]
      simp
@[simp] theorem momentBodyPartition_zero
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    momentBodyPartition K p 0 =
      normalizedVolume K.carrier := by
  exact momentBodyPartition_of_nonpositive K p (le_refl 0)
def momentBodyNormalizedPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) : ℝ :=
  momentBodyPartition K p t /
    normalizedVolume K.carrier
theorem momentBodyNormalizedPartition_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : t ≤ 0) :
    momentBodyNormalizedPartition K p t = 1 := by
  unfold momentBodyNormalizedPartition
  rw [momentBodyPartition_of_nonpositive K p ht]
  exact div_self K.volume_pos.ne'
def momentBodyLogPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) : ℝ :=
  -Real.log (momentBodyNormalizedPartition K p t)
theorem momentBodyLogPartition_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : t ≤ 0) :
    momentBodyLogPartition K p t = 0 := by
  simp [momentBodyLogPartition,
    momentBodyNormalizedPartition_of_nonpositive K p ht]
@[simp] theorem momentBodyLogPartition_zero
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    momentBodyLogPartition K p 0 = 0 := by
  exact momentBodyLogPartition_of_nonpositive K p (le_refl 0)
theorem sourceNormalizedDensity_momentBody_pos
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (q : LogTorus n) :
    0 < sourceNormalizedDensity
      (momentBodyTorusWeight K p) t q := by
  exact div_pos (Real.exp_pos _)
    (momentBodyPartition_pos K p t)
theorem sourceNormalizedDensity_momentBody_integrable
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Integrable
      (sourceNormalizedDensity (momentBodyTorusWeight K p) t)
      (sourceTorusBaseMeasure n) := by
  exact (integrable_exp_neg_momentBodyTorusWeight
    K p t).div_const _
theorem integral_sourceNormalizedDensity_momentBody
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    (∫ q : LogTorus n,
      sourceNormalizedDensity (momentBodyTorusWeight K p) t q
        ∂(sourceTorusBaseMeasure n)) = 1 := by
  unfold sourceNormalizedDensity
  rw [MeasureTheory.integral_div]
  exact div_self (momentBodyPartition_pos K p t).ne'
theorem sourceProbability_momentBody_univ
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    sourceProbability (momentBodyTorusWeight K p) t Set.univ = 1 := by
  unfold sourceProbability
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (sourceNormalizedDensity_momentBody_integrable K p t)
    (Filter.Eventually.of_forall fun q =>
      (sourceNormalizedDensity_momentBody_pos K p t q).le),
    integral_sourceNormalizedDensity_momentBody K p t]
  exact ENNReal.ofReal_one
theorem sourceProbability_momentBody_isProbability
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    IsProbabilityMeasure
      (sourceProbability (momentBodyTorusWeight K p) t) :=
  ⟨sourceProbability_momentBody_univ K p t⟩
end BergmanJetPartitionEndpoint
namespace BergmanJetTorusSlopeBridge
open Set Function Filter MeasureTheory Module InnerProductSpace
open TorusCharacters WeightedTorusHilbert BergmanMonomials LatticeAsymptotics AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity BergmanJetBasis
open MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge JetEnvelopeRightDerivative
open scoped BigOperators ENNReal InnerProductSpace Topology
def momentNormalizedTorusMonomial
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (u : monomialIndex K k) (q : LogTorus n) : ℂ :=
  ((Real.sqrt (monomialNormSquared k (u : Space n)
      (momentNormalizedPotential F)) : ℂ)⁻¹) *
    torusMonomial (integerExponent K hk u) q
theorem continuous_momentNormalizedTorusMonomial
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (u : monomialIndex K k) :
    Continuous (momentNormalizedTorusMonomial K hk F u) := by
  unfold momentNormalizedTorusMonomial
  exact continuous_const.mul
    (continuous_torusMonomial (integerExponent K hk u))
theorem momentNormalizedTorusMonomial_ae
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    (fun q : LogTorus n =>
      momentNormalizedMonomialLp K hk F htransport u q)
      =ᵐ[weightedTorusMeasure k (momentNormalizedPotential F)]
        momentNormalizedTorusMonomial K hk F u := by
  let c : ℂ :=
    ((Real.sqrt (monomialNormSquared k (u : Space n)
      (momentNormalizedPotential F)) : ℂ)⁻¹)
  have hsmul := MeasureTheory.Lp.coeFn_smul c
    (momentIndexedMonomialLp K hk F htransport u)
  have hmono := momentIndexedMonomialLp_ae K hk F htransport u
  filter_upwards [hsmul, hmono] with q hq hindex
  change
    ((c • momentIndexedMonomialLp K hk F htransport u :
      weightedHilbert k (momentNormalizedPotential F)) :
        LogTorus n → ℂ) q =
      c * torusMonomial (integerExponent K hk u) q
  rw [hq, Pi.smul_apply, hindex, smul_eq_mul]
def momentTorusRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    momentMonomialSpan K hk F htransport →ₗ[ℂ]
      (LogTorus n → ℂ) :=
  (Finsupp.linearCombination ℂ
    (momentNormalizedTorusMonomial K hk F)).comp
      (momentLatticeMonomialBasis
        K hk F htransport).repr.toLinearMap
theorem continuous_momentTorusRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    Continuous (momentTorusRepresentative K hk F htransport s) := by
  classical
  unfold momentTorusRepresentative
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  rw [Finset.sum_fn]
  exact continuous_finsetSum _ (fun u _ =>
    (continuous_momentNormalizedTorusMonomial
      K hk F u).const_smul
        ((momentLatticeMonomialBasis
          K hk F htransport).repr s u))
theorem momentTorusRepresentative_ae
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    (fun q : LogTorus n =>
      ((s : weightedHilbert k (momentNormalizedPotential F)) :
        LogTorus n → ℂ) q)
      =ᵐ[weightedTorusMeasure k (momentNormalizedPotential F)]
        momentTorusRepresentative K hk F htransport s := by
  classical
  let := (monomialIndex_finite K hk).fintype
  let b := momentLatticeMonomialBasis K hk F htransport
  let c : monomialIndex K k → ℂ := fun u => b.repr s u
  let v : monomialIndex K k →
      weightedHilbert k (momentNormalizedPotential F) :=
    fun u => c u • momentNormalizedMonomialLp
      K hk F htransport u
  have hvsum : (∑ u, v u) =
      (s : weightedHilbert k (momentNormalizedPotential F)) := by
    have h := congrArg
      (fun w : momentMonomialSpan K hk F htransport =>
        (w : weightedHilbert k (momentNormalizedPotential F)))
      (b.sum_repr s)
    simpa only [v, c, b, Submodule.coe_sum, Submodule.coe_smul,
      momentLatticeMonomialBasis_apply] using h
  have hvpoint :
      ∀ᵐ q ∂(weightedTorusMeasure k (momentNormalizedPotential F)),
        ∀ u : monomialIndex K k,
          v u q = c u * momentNormalizedTorusMonomial K hk F u q := by
    apply Filter.eventually_all.mpr
    intro u
    have hsmul := MeasureTheory.Lp.coeFn_smul (c u)
      (momentNormalizedMonomialLp K hk F htransport u)
    have hrep := momentNormalizedTorusMonomial_ae
      K hk F htransport u
    filter_upwards [hsmul, hrep] with q hq hr
    change
      ((c u • momentNormalizedMonomialLp
        K hk F htransport u :
          weightedHilbert k (momentNormalizedPotential F)) :
            LogTorus n → ℂ) q =
        c u * momentNormalizedTorusMonomial K hk F u q
    rw [hq, Pi.smul_apply, hr, smul_eq_mul]
  have hsum := JetEnvelopeSlopeBridge.coeFn_finset_sum_ae
    (weightedTorusMeasure k (momentNormalizedPotential F))
    (Finset.univ : Finset (monomialIndex K k)) v
  filter_upwards [hsum, hvpoint] with q hq hall
  rw [← hvsum]
  rw [hq]
  simp only [Finset.sum_congr rfl (fun u _ => hall u)]
  simp [momentTorusRepresentative,
    Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b, c]
theorem integral_momentTorusRepresentative_normSq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    (∫ q : LogTorus n,
      Complex.normSq (momentTorusRepresentative
        K hk F htransport s q)
        ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
          ‖s‖ ^ 2 := by
  let f : weightedHilbert k (momentNormalizedPotential F) := s
  have hae := momentTorusRepresentative_ae
    K hk F htransport s
  have hcomplex :
      ((∫ q : LogTorus n,
        Complex.normSq (momentTorusRepresentative
          K hk F htransport s q)
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) : ℝ) : ℂ) =
        ((‖s‖ ^ 2 : ℝ) : ℂ) := by
    calc
      ((∫ q : LogTorus n,
        Complex.normSq (momentTorusRepresentative
          K hk F htransport s q)
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) : ℝ) : ℂ) =
        ∫ q : LogTorus n,
          (Complex.normSq (momentTorusRepresentative
            K hk F htransport s q) : ℂ)
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) := integral_ofReal.symm
      _ = ∫ q : LogTorus n,
          @inner ℂ ℂ _ (f q) (f q)
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hae] with q hq
          change
            (Complex.normSq (momentTorusRepresentative
              K hk F htransport s q) : ℂ) =
                @inner ℂ ℂ _
                  ((s : weightedHilbert k
                    (momentNormalizedPotential F)) q)
                  ((s : weightedHilbert k
                    (momentNormalizedPotential F)) q)
          rw [hq, RCLike.inner_apply,
            Complex.normSq_eq_conj_mul_self]
          ring
      _ = @inner ℂ (weightedHilbert k
            (momentNormalizedPotential F)) _ f f :=
          (MeasureTheory.L2.inner_def f f).symm
      _ = ((‖s‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]
        simp [f]
  exact Complex.ofReal_injective hcomplex
theorem integrable_momentTorusRepresentative_normSq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    Integrable
      (fun q : LogTorus n => Complex.normSq
        (momentTorusRepresentative K hk F htransport s q))
      (weightedTorusMeasure k (momentNormalizedPotential F)) := by
  have hmem : MemLp (momentTorusRepresentative
      K hk F htransport s) 2
        (weightedTorusMeasure k (momentNormalizedPotential F)) :=
    (MeasureTheory.memLp_congr_ae
      (momentTorusRepresentative_ae
        K hk F htransport s)).mp
          (MeasureTheory.Lp.memLp
            (s : weightedHilbert k (momentNormalizedPotential F)))
  have hint := (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (continuous_momentTorusRepresentative
      K hk F htransport s).aestronglyMeasurable).mp hmem
  simpa only [Complex.normSq_eq_norm_sq] using hint
def momentTorusJetBasisWeight
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n)
    (i : Fin (bergmanDimension K k)) : ℝ :=
  Complex.normSq
    (momentTorusRepresentative K hk F htransport
      (momentSimultaneousJetBasis
        K hk F htransport p i) q)
def momentTorusTruncatedJetOrderDensity
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) : ℝ :=
  ∑ i : Fin (bergmanDimension K k),
    (momentTruncatedJetOrder K hk F htransport p N i : ℝ) *
      momentTorusJetBasisWeight K hk F htransport p q i
theorem momentTorusRepresentative_eq_holomorphicRepresentative_cover
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport)
    (q : LogTorus n) :
    momentTorusRepresentative K hk F htransport s q =
      momentHolomorphicRepresentative K hk F htransport s
        (sourceTorusCoverPoint q) := by
  classical
  unfold momentTorusRepresentative
    momentHolomorphicRepresentative
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  unfold momentNormalizedTorusMonomial
    normalizedHolomorphicMonomial
  rw [torusCharacter_sourceTorusCoverPoint]
theorem sum_momentTorusRepresentative_normSq_eq_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (q : LogTorus n) :
    (∑ i, Complex.normSq
      (momentTorusRepresentative K hk F htransport
        (b i) q)) =
      diagonalKernel K k (momentNormalizedPotential F) q.1 := by
  calc
    (∑ i, Complex.normSq
      (momentTorusRepresentative K hk F htransport
        (b i) q)) =
      ∑ i, Complex.normSq
        (momentHolomorphicRepresentative K hk F htransport
          (b i) (sourceTorusCoverPoint q)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [momentTorusRepresentative_eq_holomorphicRepresentative_cover]
    _ = diagonalKernel K k (momentNormalizedPotential F)
      (BergmanDiagonalBasisIndependence.realLogCoordinate
        (sourceTorusCoverPoint q)) :=
      sum_momentHolomorphicBasisWeight_eq_diagonalKernel
        K hk F htransport b (sourceTorusCoverPoint q)
    _ = diagonalKernel K k (momentNormalizedPotential F) q.1 := by
      rw [realLogCoordinate_sourceTorusCoverPoint]
theorem integrable_momentDiagonalKernel_weightedTorus
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Integrable
      (fun q : LogTorus n =>
        diagonalKernel K k (momentNormalizedPotential F) q.1)
      (weightedTorusMeasure k (momentNormalizedPotential F)) := by
  let b := momentMonomialOrthonormalBasis K hk F htransport
  have hsum : Integrable
      (fun q : LogTorus n =>
        ∑ i : Fin (bergmanDimension K k),
          Complex.normSq
            (momentTorusRepresentative
              K hk F htransport (b i) q))
      (weightedTorusMeasure k (momentNormalizedPotential F)) :=
    integrable_finsetSum _ (fun i _ =>
      integrable_momentTorusRepresentative_normSq
        K hk F htransport (b i))
  exact hsum.congr
    (Filter.Eventually.of_forall fun q =>
      sum_momentTorusRepresentative_normSq_eq_diagonalKernel
        K hk F htransport b q)
theorem integral_momentDiagonalKernel_weightedTorus
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    (∫ q : LogTorus n,
      diagonalKernel K k (momentNormalizedPotential F) q.1
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
        (bergmanDimension K k : ℝ) := by
  let b := momentMonomialOrthonormalBasis K hk F htransport
  calc
    (∫ q : LogTorus n,
      diagonalKernel K k (momentNormalizedPotential F) q.1
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
      ∫ q : LogTorus n,
        (∑ i : Fin (bergmanDimension K k),
          Complex.normSq
            (momentTorusRepresentative K hk F htransport
              (b i) q))
        ∂(weightedTorusMeasure k (momentNormalizedPotential F)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with q
          exact (sum_momentTorusRepresentative_normSq_eq_diagonalKernel
            K hk F htransport b q).symm
    _ = ∑ i : Fin (bergmanDimension K k),
          ∫ q : LogTorus n,
            Complex.normSq
              (momentTorusRepresentative K hk F htransport
                (b i) q)
            ∂(weightedTorusMeasure k
              (momentNormalizedPotential F)) := by
          rw [MeasureTheory.integral_finsetSum]
          intro i _
          exact integrable_momentTorusRepresentative_normSq
            K hk F htransport (b i)
    _ = (bergmanDimension K k : ℝ) := by
      have hunit (i : Fin (bergmanDimension K k)) :
          (∫ q : LogTorus n,
            Complex.normSq
              (momentTorusRepresentative K hk F htransport
                (b i) q)
              ∂(weightedTorusMeasure k
                (momentNormalizedPotential F))) = 1 := by
        rw [integral_momentTorusRepresentative_normSq]
        rw [b.orthonormal.norm_eq_one i]
        norm_num
      simp_rw [hunit]
      simp
def momentTorusBergmanProbability
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) (k : ℕ) : Measure (LogTorus n) :=
  (weightedTorusMeasure k (momentNormalizedPotential F)).withDensity
    (fun q : LogTorus n =>
      ENNReal.ofReal
        (diagonalKernel K k (momentNormalizedPotential F) q.1 /
          (bergmanDimension K k : ℝ)))
theorem momentTorusBergmanProbability_univ
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    momentTorusBergmanProbability K F k Set.univ = 1 := by
  have hdim : 0 < (bergmanDimension K k : ℝ) := by
    exact_mod_cast bergmanDimension_pos K hk
  have hint : Integrable
      (fun q : LogTorus n =>
        diagonalKernel K k (momentNormalizedPotential F) q.1 /
          (bergmanDimension K k : ℝ))
      (weightedTorusMeasure k (momentNormalizedPotential F)) :=
    (integrable_momentDiagonalKernel_weightedTorus
      K hk F htransport).div_const _
  unfold momentTorusBergmanProbability
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun q =>
      div_nonneg
        (diagonalKernel_momentNormalized_pos
          K hk F htransport q.1).le hdim.le),
    MeasureTheory.integral_div,
    integral_momentDiagonalKernel_weightedTorus
      K hk F htransport]
  rw [div_self hdim.ne', ENNReal.ofReal_one]
theorem momentTorusBergmanProbability_isProbability
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    IsProbabilityMeasure (momentTorusBergmanProbability K F k) :=
  ⟨momentTorusBergmanProbability_univ K hk F htransport⟩
def momentPositiveTorusJetSlope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) : ℝ :=
  momentTorusTruncatedJetOrderDensity
      K hk F htransport p N q /
    ((k : ℝ) * diagonalKernel K k
      (momentNormalizedPotential F) q.1)
end BergmanJetTorusSlopeBridge
namespace JetEnvelopeTrueRadialLocalHessian
open Set Filter Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian JetEnvelopeTrueRadialComplexHessianPositivity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff
theorem sourceJointCircleRadiusProfile_isLocalMin_of_local_circle_submean
    {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n)
    (hmean : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r : ℝ, |r| < ρ →
        f q ≤ Real.circleAverage
          (fun w : ℂ => f (q + w • v)) 0 r) :
    IsLocalMin (sourceJointCircleRadiusProfile f q v) 0 := by
  obtain ⟨ρ, hρ, hmean⟩ := hmean
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, |r| < ρ := by
    have hzero : |(0 : ℝ)| < ρ := by simpa using hρ
    exact (continuous_abs.tendsto (0 : ℝ)).eventually
      (Iio_mem_nhds hzero)
  filter_upwards [hnear] with r hr
  rw [sourceJointCircleRadiusProfile_zero]
  exact hmean r hr
theorem sourceJointCircleRadiusProfile_second_derivative_nonnegative_of_local_circle_submean
    {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (hf : Continuous f)
    (q v : SourceJointComplexCover n)
    (hmean : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r : ℝ, |r| < ρ →
        f q ≤ Real.circleAverage
          (fun w : ℂ => f (q + w • v)) 0 r) :
    0 ≤ deriv (deriv (sourceJointCircleRadiusProfile f q v)) 0 :=
  local_min_second_derivative_nonnegative
    (sourceJointCircleRadiusProfile_isLocalMin_of_local_circle_submean
      f q v hmean)
    (continuous_sourceJointCircleRadiusProfile hf q v).continuousAt
theorem sourceJointRealLeviQuadratic_nonnegative_of_local_circle_submean
    {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q v : SourceJointComplexCover n)
    (hmean : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r : ℝ, |r| < ρ →
        f q ≤ Real.circleAverage
          (fun w : ℂ => f (q + w • v)) 0 r) :
    0 ≤ sourceJointRealLeviQuadratic f q v := by
  have hsecond :=
    sourceJointCircleRadiusProfile_second_derivative_nonnegative_of_local_circle_submean
      f hf.continuous q v hmean
  rw [sourceJointCircleRadiusProfile_second_eq_realHessian
    hf q v] at hsecond
  unfold sourceJointRealLeviQuadratic
  linarith
theorem sourceJointSpatialComplexHessian_posSemidef_of_local_circle_submean
    {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hmean : ∀ (q v : SourceJointComplexCover n),
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ r : ℝ, |r| < ρ →
          f q ≤ Real.circleAverage
            (fun w : ℂ => f (q + w • v)) 0 r)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) :
    (sourceJointSpatialComplexHessian f τ z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (sourceJointSpatialComplexHessian_isHermitian hf τ z)
  intro x
  rw [sourceJointSpatialComplexHessian_quadratic_eq_realLevi
    hf τ z x]
  apply (Complex.nonneg_iff).2
  constructor
  · simpa using
      sourceJointRealLeviQuadratic_nonnegative_of_local_circle_submean
        hf (z, τ) (star x, 0) (hmean (z, τ) (star x, 0))
  · simp
end JetEnvelopeTrueRadialLocalHessian
namespace RadialSchurBlock
open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic EnvelopeGeneralTorusDescent SchurConvexity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff
def sourceComplexRowSchurEnergyDensity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) : ℝ :=
  complexSchurEnergyDensity A (star b)
theorem sourceComplexRowSchurEnergyDensity_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) :
    sourceComplexRowSchurEnergyDensity A b =
      (b ⬝ᵥ (A⁻¹ *ᵥ star b)).re := by
  simp [sourceComplexRowSchurEnergyDensity,
    complexSchurEnergyDensity]
def sourceComplexRowSchurBlock {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) (c : ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks A (complexSchurColumn (star b))
    (complexSchurColumn (star b))ᴴ (complexSchurScalar c)
theorem sourceComplexRowSchurBlock_isHermitian {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian)
    (b : Fin n → ℂ) (c : ℝ) :
    (sourceComplexRowSchurBlock A b c).IsHermitian := by
  unfold sourceComplexRowSchurBlock
  apply Matrix.IsHermitian.fromBlocks hA rfl
  ext i j
  simp [complexSchurScalar, Matrix.conjTranspose_apply]
theorem sourceComplexRowSchurEnergy_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ) (c : ℝ)
    (hblock : (sourceComplexRowSchurBlock A b c).PosSemidef) :
    sourceComplexRowSchurEnergyDensity A b ≤ c := by
  exact complex_schur_energy_le hA (star b) c hblock
def sourceJointCoverAntiholomorphicVelocityGradient {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) : Fin n → ℂ :=
  sourceCoverAntiholomorphicGradient
    (fun w : TorusCharacters.LogSpace n =>
      (jointSourceCoverVelocity F (w, τ) : ℂ)) z
def sourceJointCoverHolomorphicVelocityGradient {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) : Fin n → ℂ :=
  fun i => holomorphicCoordinate
    (fun w : TorusCharacters.LogSpace n =>
      (jointSourceCoverVelocity F (w, τ) : ℂ)) z i
theorem star_sourceJointCoverAntiholomorphicVelocityGradient
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) :
    star (sourceJointCoverAntiholomorphicVelocityGradient F τ z) =
      sourceJointCoverHolomorphicVelocityGradient F τ z := by
  have hv : Differentiable ℝ
      (fun w : TorusCharacters.LogSpace n =>
        jointSourceCoverVelocity F (w, τ)) :=
    ((contDiff_jointSourceCoverVelocity hF).comp
      (contDiff_id.prodMk contDiff_const)).differentiable
        (by norm_num)
  ext i
  exact conj_barPartialCoordinate_real hv z i
theorem sourceComplexSchurBlock_quadratic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) (c : ℝ)
    (x : Fin n ⊕ Fin 1 → ℂ) :
    star x ⬝ᵥ
      (Matrix.fromBlocks A (complexSchurColumn b)
        (complexSchurColumn b)ᴴ (complexSchurScalar c) *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
      (star (x ∘ Sum.inl) ⬝ᵥ b) * x (Sum.inr 0) +
      star (x (Sum.inr 0)) *
        (star b ⬝ᵥ (x ∘ Sum.inl)) +
      star (x (Sum.inr 0)) * (c : ℂ) * x (Sum.inr 0) := by
  simp [dotProduct,
    complexSchurColumn, complexSchurScalar, Matrix.mulVec,
    Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    Finset.mul_sum, Finset.sum_mul,
    Function.comp_def, Pi.star_apply]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp [mul_assoc, mul_left_comm, mul_comm]
  ring
theorem sourceComplexRowSchurBlock_quadratic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) (c : ℝ)
    (x : Fin n ⊕ Fin 1 → ℂ) :
    star x ⬝ᵥ (sourceComplexRowSchurBlock A b c *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
      (star (x ∘ Sum.inl) ⬝ᵥ star b) * x (Sum.inr 0) +
      star (x (Sum.inr 0)) *
        (b ⬝ᵥ (x ∘ Sum.inl)) +
      star (x (Sum.inr 0)) * (c : ℂ) * x (Sum.inr 0) := by
  unfold sourceComplexRowSchurBlock
  simpa using sourceComplexSchurBlock_quadratic A (star b) c x
end RadialSchurBlock
namespace RadialFullLeviFoundations
open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian EnvelopeTorusDescent EnvelopeGeneralTorusDescent
open RadialSchurBlock WeightedDolbeaultBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff
theorem sourceJointImaginaryTime_fderiv_eq_zero
    {n : ℕ} {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ r : ℝ,
      Function.Periodic F
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I))
    (q : SourceJointComplexCover n) :
    (fderiv ℝ F q)
      ((0 : TorusCharacters.LogSpace n), Complex.I) = 0 := by
  let v : SourceJointComplexCover n :=
    ((0 : TorusCharacters.LogSpace n), Complex.I)
  have hline :
      (fun r : ℝ => F (q + r • v)) = fun _ : ℝ => F q := by
    funext r
    have hr : r • v =
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I) := by
      apply Prod.ext
      · ext i
        simp [v]
      · simp [v, Complex.real_smul]
    rw [hr]
    exact hperiod r q
  have hzero : q + (0 : ℝ) • v = q := by
    apply Prod.ext
    · ext i
      simp [v]
    · simp [v]
  have hder :=
    (hasDerivAt_sourceJointCircleLine hF q v 0).deriv
  rw [hline, hzero] at hder
  simpa [v] using hder.symm
theorem sourceJointImaginaryTime_sndFDeriv_eq_zero
    {n : ℕ} {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ r : ℝ,
      Function.Periodic F
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I))
    (q w : SourceJointComplexCover n) :
    ((fderiv ℝ (fderiv ℝ F) q) w)
      ((0 : TorusCharacters.LogSpace n), Complex.I) = 0 := by
  have hfun :
      (fun ξ : SourceJointComplexCover n =>
        (fderiv ℝ F ξ)
          ((0 : TorusCharacters.LogSpace n), Complex.I)) =
      (fun _ : SourceJointComplexCover n => (0 : ℝ)) := by
    funext ξ
    exact sourceJointImaginaryTime_fderiv_eq_zero hF hperiod ξ
  rw [← fderiv_sourceJointRealDirectional hF q
    ((0 : TorusCharacters.LogSpace n), Complex.I) w,
    hfun]
  simp
theorem sourceJointCoverHolomorphicVelocityGradient_eq_sndFDeriv
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n)
    (i : Fin n) :
    sourceJointCoverHolomorphicVelocityGradient F τ z i =
      ((((fderiv ℝ (fderiv ℝ F) (z, τ))
          (Pi.single i (1 : ℂ), (0 : ℂ))
          (sourceJointTimeDirection n) : ℝ) : ℂ) -
        Complex.I *
          (((fderiv ℝ (fderiv ℝ F) (z, τ))
            (Pi.single i Complex.I, (0 : ℂ))
            (sourceJointTimeDirection n) : ℝ) : ℂ)) / 2 := by
  have hv : Differentiable ℝ
      (fun w : TorusCharacters.LogSpace n =>
        jointSourceCoverVelocity F (w, τ)) :=
    ((contDiff_jointSourceCoverVelocity hF).comp
      (contDiff_id.prodMk contDiff_const)).differentiable
        (by norm_num)
  unfold sourceJointCoverHolomorphicVelocityGradient
    holomorphicCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hv z (Pi.single i (1 : ℂ)),
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hv z (Pi.single i Complex.I)]
  rw [fderiv_sourceJointSpatialSlice_apply
      ((contDiff_jointSourceCoverVelocity hF).differentiable
        (by norm_num)) τ z (Pi.single i (1 : ℂ)),
    fderiv_sourceJointSpatialSlice_apply
      ((contDiff_jointSourceCoverVelocity hF).differentiable
        (by norm_num)) τ z (Pi.single i Complex.I)]
  unfold jointSourceCoverVelocity
  rw [fderiv_sourceJointRealDirectional hF (z, τ)
      (sourceJointTimeDirection n)
      (Pi.single i (1 : ℂ), (0 : ℂ)),
    fderiv_sourceJointRealDirectional hF (z, τ)
      (sourceJointTimeDirection n)
      (Pi.single i Complex.I, (0 : ℂ))]
end RadialFullLeviFoundations
namespace RadialFullLeviSchur
open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian JetEnvelopeTrueRadialComplexHessianPositivity
open EnvelopeTorusDescent EnvelopeGeneralTorusDescent RadialSchurBlock RadialFullLeviFoundations
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff
theorem sourceJointRealBilinear_spatial_apply_eq_realBasis_sum
    {n : ℕ}
    (B : SourceJointComplexCover n →L[ℝ]
      SourceJointComplexCover n →L[ℝ] ℝ)
    (u : TorusCharacters.LogSpace n)
    (t : SourceJointComplexCover n) :
    (B (u, 0)) t =
      ∑ i : Fin n,
        ((u i).re * (B (Pi.single i (1 : ℂ), 0)) t +
          (u i).im * (B (Pi.single i Complex.I, 0)) t) := by
  classical
  let U : Fin n → SourceJointComplexCover n := fun i =>
    ((u i).re •
        (Pi.single i (1 : ℂ) : TorusCharacters.LogSpace n) +
      (u i).im •
        (Pi.single i Complex.I : TorusCharacters.LogSpace n), 0)
  have hu : (u, (0 : ℂ)) = ∑ i, U i := by
    apply Prod.ext
    · change u = (∑ i, U i).1
      have hfst :
          (∑ i, U i).1 = ∑ i, (U i).1 := by
        change
          (ContinuousLinearMap.fst ℝ
            (TorusCharacters.LogSpace n) ℂ) (∑ i, U i) =
            ∑ i,
              (ContinuousLinearMap.fst ℝ
                (TorusCharacters.LogSpace n) ℂ) (U i)
        exact map_sum
          (ContinuousLinearMap.fst ℝ
            (TorusCharacters.LogSpace n) ℂ)
          U Finset.univ
      rw [hfst]
      simpa only [U] using sourceSpatialRealBasis_decomposition u
    · change (0 : ℂ) = (∑ i, U i).2
      have hsnd :
          (∑ i, U i).2 = ∑ i, (U i).2 := by
        change
          (ContinuousLinearMap.snd ℝ
            (TorusCharacters.LogSpace n) ℂ) (∑ i, U i) =
            ∑ i,
              (ContinuousLinearMap.snd ℝ
                (TorusCharacters.LogSpace n) ℂ) (U i)
        exact map_sum
          (ContinuousLinearMap.snd ℝ
            (TorusCharacters.LogSpace n) ℂ)
          U Finset.univ
      rw [hsnd]
      simp [U]
  calc
    (B (u, 0)) t = (B (∑ i, U i)) t := by rw [hu]
    _ = ∑ i, (B (U i)) t := by
      simpa only [ContinuousLinearMap.flip_apply] using
        (map_sum (B.flip t) U Finset.univ)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hp :
          U i =
            (u i).re •
                ((Pi.single i (1 : ℂ) :
                  TorusCharacters.LogSpace n), (0 : ℂ)) +
              (u i).im •
                ((Pi.single i Complex.I :
                  TorusCharacters.LogSpace n), (0 : ℂ)) := by
        apply Prod.ext
        · rfl
        · simp [U]
      calc
        (B (U i)) t =
            (B ((u i).re •
              ((Pi.single i (1 : ℂ) :
                TorusCharacters.LogSpace n), (0 : ℂ)) +
                (u i).im •
                  ((Pi.single i Complex.I :
                    TorusCharacters.LogSpace n), (0 : ℂ)))) t := by
              rw [hp]
        _ = _ := by
          rw [map_add, map_smul, map_smul]
          simp [            smul_eq_mul]
theorem sourceJointCoverHolomorphicVelocityGradient_dot_eq_sndFDeriv
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (τ : ℂ)
    (z u : TorusCharacters.LogSpace n) :
    u ⬝ᵥ sourceJointCoverHolomorphicVelocityGradient F τ z =
      ((↑(((fderiv ℝ (fderiv ℝ F) (z, τ)) (u, 0))
          (sourceJointTimeDirection n)) : ℂ) -
        Complex.I *
          (↑(((fderiv ℝ (fderiv ℝ F) (z, τ))
            (Complex.I • u, 0))
            (sourceJointTimeDirection n)) : ℂ)) / 2 := by
  classical
  simp only [dotProduct]
  simp_rw [sourceJointCoverHolomorphicVelocityGradient_eq_sndFDeriv hF τ z]
  rw [sourceJointRealBilinear_spatial_apply_eq_realBasis_sum
      (fderiv ℝ (fderiv ℝ F) (z, τ)) u
      (sourceJointTimeDirection n),
    sourceJointRealBilinear_spatial_apply_eq_realBasis_sum
      (fderiv ℝ (fderiv ℝ F) (z, τ)) (Complex.I • u)
      (sourceJointTimeDirection n)]
  simp only [Pi.smul_apply, smul_eq_mul,
    Complex.I_mul_re, Complex.I_mul_im]
  push_cast
  let A : Fin n → ℝ := fun i =>
    ((fderiv ℝ (fderiv ℝ F) (z, τ))
      (Pi.single i (1 : ℂ), 0)) (sourceJointTimeDirection n)
  let C : Fin n → ℝ := fun i =>
    ((fderiv ℝ (fderiv ℝ F) (z, τ))
      (Pi.single i Complex.I, 0)) (sourceJointTimeDirection n)
  have hpoint (i : Fin n) :
      u i * (((A i : ℂ) - Complex.I * (C i : ℂ)) / 2) =
        (((u i).re : ℂ) * (A i : ℂ) +
          ((u i).im : ℂ) * (C i : ℂ) -
          Complex.I *
            (-((u i).im : ℂ) * (A i : ℂ) +
              ((u i).re : ℂ) * (C i : ℂ))) / 2 := by
    rw [← Complex.re_add_im (u i)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.mul_re, Complex.mul_im,
      mul_zero, mul_one,
      add_zero, zero_add, sub_zero]
    ring_nf
    simp only [Complex.I_sq]
    ring
  change
    (∑ i : Fin n,
      u i * (((A i : ℂ) - Complex.I * (C i : ℂ)) / 2)) =
      ((∑ i : Fin n,
          (((u i).re : ℂ) * (A i : ℂ) +
            ((u i).im : ℂ) * (C i : ℂ))) -
        Complex.I *
          (∑ i : Fin n,
            (-((u i).im : ℂ) * (A i : ℂ) +
              ((u i).re : ℂ) * (C i : ℂ)))) / 2
  simp_rw [hpoint]
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
theorem jointSourceCoverAcceleration_eq_sndFDeriv
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (q : SourceJointComplexCover n) :
    jointSourceCoverAcceleration F q =
      ((fderiv ℝ (fderiv ℝ F) q)
        (sourceJointTimeDirection n))
        (sourceJointTimeDirection n) := by
  unfold jointSourceCoverAcceleration jointSourceCoverVelocity
  exact fderiv_sourceJointRealDirectional hF q
    (sourceJointTimeDirection n) (sourceJointTimeDirection n)
theorem sourceJointComplexTime_decomposition
    {n : ℕ} (s : ℂ) :
    ((0 : TorusCharacters.LogSpace n), s) =
      (2 * s.re) • sourceJointTimeDirection n +
        s.im • ((0 : TorusCharacters.LogSpace n), Complex.I) := by
  apply Prod.ext
  · ext i
    simp [sourceJointTimeDirection]
  · simp [sourceJointTimeDirection, Complex.real_smul]
    simpa [mul_comm] using (Complex.re_add_im s).symm
theorem sourceJointCoverAntiholomorphicVelocityGradient_dot_eq_star_holomorphic
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (τ : ℂ)
    (z y : TorusCharacters.LogSpace n) :
    sourceJointCoverAntiholomorphicVelocityGradient F τ z ⬝ᵥ y =
      star ((star y) ⬝ᵥ
        sourceJointCoverHolomorphicVelocityGradient F τ z) := by
  rw [← star_sourceJointCoverAntiholomorphicVelocityGradient hF τ z]
  simp [dotProduct, Pi.star_apply, mul_comm]
theorem sourceJointRealLeviQuadratic_eq_spatial_mixed_time
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ r : ℝ,
      Function.Periodic F
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I))
    (τ : ℂ)
    (z u : TorusCharacters.LogSpace n)
    (s : ℂ) :
    sourceJointRealLeviQuadratic F (z, τ) (u, s) =
      sourceJointRealLeviQuadratic F (z, τ) (u, 0) +
        s.re *
          ((fderiv ℝ (fderiv ℝ F) (z, τ))
            (u, 0)) (sourceJointTimeDirection n) -
        s.im *
          ((fderiv ℝ (fderiv ℝ F) (z, τ))
            (Complex.I • u, 0)) (sourceJointTimeDirection n) +
        (s.re ^ 2 + s.im ^ 2) *
          ((fderiv ℝ (fderiv ℝ F) (z, τ))
            (sourceJointTimeDirection n))
            (sourceJointTimeDirection n) := by
  let B : SourceJointComplexCover n →L[ℝ]
      SourceJointComplexCover n →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ F) (z, τ)
  let T : SourceJointComplexCover n := sourceJointTimeDirection n
  let J : SourceJointComplexCover n :=
    ((0 : TorusCharacters.LogSpace n), Complex.I)
  let U : SourceJointComplexCover n := (u, 0)
  let V : SourceJointComplexCover n := (Complex.I • u, 0)
  have hsymm (a b : SourceJointComplexCover n) :
      (B a) b = (B b) a :=
    (hF.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq a b
  have hJ (w : SourceJointComplexCover n) : (B w) J = 0 := by
    exact sourceJointImaginaryTime_sndFDeriv_eq_zero hF hperiod
      (z, τ) w
  have hJleft (w : SourceJointComplexCover n) : (B J) w = 0 := by
    rw [hsymm]
    exact hJ w
  have hv :
      (u, s) = U + (2 * s.re) • T + s.im • J := by
    calc
      (u, s) = (u, 0) + ((0 : TorusCharacters.LogSpace n), s) := by
        ext <;> simp
      _ = U + (2 * s.re) • T + s.im • J := by
        rw [sourceJointComplexTime_decomposition s]
        dsimp [U, T, J]
        abel
  have hi :
      Complex.I • (u, s) =
        V + (-2 * s.im) • T + s.re • J := by
    change (Complex.I • u, Complex.I * s) =
      V + (-2 * s.im) • T + s.re • J
    calc
      (Complex.I • u, Complex.I * s) =
          (Complex.I • u, 0) +
            ((0 : TorusCharacters.LogSpace n),
              Complex.I * s) := by
          ext <;> simp
      _ = V + (-2 * s.im) • T + s.re • J := by
        rw [sourceJointComplexTime_decomposition (Complex.I * s)]
        simp only [Complex.I_mul_re, Complex.I_mul_im]
        dsimp [V, T, J]
        module
  have hIU : Complex.I • U = V := by
    ext <;> simp [U, V]
  unfold sourceJointRealLeviQuadratic
  change
    ((B (u, s)) (u, s) +
      (B (Complex.I • (u, s))) (Complex.I • (u, s))) / 4 =
      ((B U) U + (B (Complex.I • U)) (Complex.I • U)) / 4 +
        s.re * (B U) T - s.im * (B V) T +
        (s.re ^ 2 + s.im ^ 2) * (B T) T
  rw [hi, hv, hIU]
  simp only [map_add, map_smul, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul,
    hJ, hJleft, mul_zero, add_zero]
  rw [hsymm T U, hsymm T V]
  ring
theorem complex_sourceRowSchurMixedScalar_eq_real
    (a : ℂ) (L P Q R : ℝ) :
    (L : ℂ) +
        (((P : ℂ) - Complex.I * (Q : ℂ)) / 2) * a +
        star a * star (((P : ℂ) - Complex.I * (Q : ℂ)) / 2) +
        star a * (R : ℂ) * a =
      (↑(L + (star a).re * P - (star a).im * Q +
        ((star a).re ^ 2 + (star a).im ^ 2) * R) : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring
theorem sourceJointCoverRowSchurBlock_quadratic_eq_realLevi
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ r : ℝ,
      Function.Periodic F
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I))
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n)
    (x : Fin n ⊕ Fin 1 → ℂ) :
    star x ⬝ᵥ
      (sourceComplexRowSchurBlock
        (sourceJointSpatialComplexHessian F τ z)
        (sourceJointCoverAntiholomorphicVelocityGradient F τ z)
        (jointSourceCoverAcceleration F (z, τ)) *ᵥ x) =
      (sourceJointRealLeviQuadratic F (z, τ)
        (star (x ∘ Sum.inl), star (x (Sum.inr 0))) : ℂ) := by
  rw [sourceComplexRowSchurBlock_quadratic]
  rw [sourceJointSpatialComplexHessian_quadratic_eq_realLevi
      hF τ z (x ∘ Sum.inl)]
  rw [star_sourceJointCoverAntiholomorphicVelocityGradient hF τ z]
  rw [sourceJointCoverAntiholomorphicVelocityGradient_dot_eq_star_holomorphic
      hF τ z (x ∘ Sum.inl)]
  rw [sourceJointCoverHolomorphicVelocityGradient_dot_eq_sndFDeriv
      hF τ z (star (x ∘ Sum.inl))]
  rw [jointSourceCoverAcceleration_eq_sndFDeriv hF (z, τ)]
  rw [sourceJointRealLeviQuadratic_eq_spatial_mixed_time hF hperiod τ z
      (star (x ∘ Sum.inl)) (star (x (Sum.inr 0)))]
  exact complex_sourceRowSchurMixedScalar_eq_real
    (x (Sum.inr 0))
    (sourceJointRealLeviQuadratic F (z, τ)
      (star (x ∘ Sum.inl), 0))
    (((fderiv ℝ (fderiv ℝ F) (z, τ))
      (star (x ∘ Sum.inl), 0)) (sourceJointTimeDirection n))
    (((fderiv ℝ (fderiv ℝ F) (z, τ))
      (Complex.I • star (x ∘ Sum.inl), 0))
      (sourceJointTimeDirection n))
    (((fderiv ℝ (fderiv ℝ F) (z, τ))
      (sourceJointTimeDirection n)) (sourceJointTimeDirection n))
end RadialFullLeviSchur
namespace BergmanJetJointEnvelopeRegularization
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters BergmanDiagonalBasisIndependence MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation BergmanJetEnvelopeLimit BergmanJetTorusEnvelope JetEnvelopeRightDerivative
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal Topology ContDiff Convolution ComplexOrder
def momentWeakJointCoverEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n) : ℝ :=
  momentEnvelopeTimeSlice K F htransport p q.1
    (sourceJointCoverTime q)
theorem continuous_momentWeakJointRealLogCoordinate (n : ℕ) :
    Continuous (fun q : SourceJointComplexCover n =>
      realLogCoordinate q.1) := by
  apply continuous_pi
  intro j
  change Continuous
    (fun q : SourceJointComplexCover n => 2 * (q.1 j).re)
  fun_prop
end BergmanJetJointEnvelopeRegularization
namespace BergmanJetJointHolomorphicPhase
open Set Function Filter MeasureTheory
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetJointEnvelopeRegularization
open ActualJetUpperEnvelope JetEnvelopeRightDerivative JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal Topology
end BergmanJetJointHolomorphicPhase
namespace BergmanJetJointHolomorphicClosure
open Set Function Filter MeasureTheory Metric
open TorusCharacters BergmanMonomials BergmanDiagonalBasisIndependence MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman BergmanJetGeodesic
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetEnvelopePlurisubharmonic
open BergmanJetEnvelopeLimit BergmanJetJointEnvelopeRegularization BergmanJetJointHolomorphicPhase
open ActualJetUpperEnvelope ActualJetPlurisubharmonicEnvelope JetEnvelopeRightDerivative
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeGlobalPlurisubharmonicClosure
open BergmanGeodesicConvexity
open scoped BigOperators ENNReal Topology InnerProductSpace
def momentWeakJointCoverFiniteGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  momentJetGeodesic K (Nat.zero_lt_succ k) F htransport p
    (Nat.floor (BodyScale.canonicalScale K *
      ((k + 1 : ℕ) : ℝ))) q.1 (sourceJointCoverTime q)
theorem momentWeakJointCoverFiniteGeodesic_eq_log_diagonal
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteGeodesic K F htransport p k q =
      Real.log
        (momentJointJetDiagonal
          K (Nat.zero_lt_succ k) F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) (sourceJointCoverExp q)) /
        ((k + 1 : ℕ) : ℝ) := by
  have hnorm :
      Complex.normSq (Complex.exp q.2) =
        Real.exp (sourceJointCoverTime q) := by
    simpa [sourceJointCoverExp] using
      (normSq_sourceJointCoverExp q)
  have hrad := momentJointJetDiagonal_eq_radial
    K (Nat.zero_lt_succ k) F htransport p q.1
    (Nat.floor (BodyScale.canonicalScale K *
      ((k + 1 : ℕ) : ℝ))) (Complex.exp_ne_zero q.2)
  rw [hnorm, Real.log_exp] at hrad
  unfold momentWeakJointCoverFiniteGeodesic
  rw [momentJetGeodesic_eq_log_jointJetDiagonal, ← hrad]
  rfl
theorem continuous_momentWeakJointCoverFiniteGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) :
    Continuous (momentWeakJointCoverFiniteGeodesic
      K F htransport p k) := by
  have heq :
      momentWeakJointCoverFiniteGeodesic K F htransport p k =
        fun q : SourceJointComplexCover n =>
          Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p
              (Nat.floor (BodyScale.canonicalScale K *
                ((k + 1 : ℕ) : ℝ))) (sourceJointCoverExp q)) /
              ((k + 1 : ℕ) : ℝ) := by
    funext q
    exact momentWeakJointCoverFiniteGeodesic_eq_log_diagonal
      K F htransport p k q
  rw [heq]
  apply Continuous.div_const
  apply Continuous.log
    ((continuous_momentJointJetDiagonal
      K (Nat.zero_lt_succ k) F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ)))).comp
            (continuous_sourceJointCoverExp n))
  intro q
  exact (momentJointJetDiagonal_pos
    K (Nat.zero_lt_succ k) F htransport p
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ))) (sourceJointCoverExp q).1
        (show (sourceJointCoverExp q).2 ≠ 0 from
          Complex.exp_ne_zero q.2)).ne'
theorem momentWeakJointCoverFiniteGeodesic_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakJointCoverFiniteGeodesic K F htransport p k q ≤
      Real.circleAverage
        (fun w : ℂ => momentWeakJointCoverFiniteGeodesic
          K F htransport p k (q + w • v)) 0 R := by
  let N := Nat.floor (BodyScale.canonicalScale K *
    ((k + 1 : ℕ) : ℝ))
  let G : ℂ → EuclideanSpace ℂ
      (Fin (bergmanDimension K (k + 1))) :=
    fun w => momentJointJetSectionVector
      K (Nat.zero_lt_succ k) F htransport p N
        (sourceJointCoverExp (q + w • v))
  have hline : Differentiable ℂ
      (fun w : ℂ => q + w • v) := by
    fun_prop
  have hG : Differentiable ℂ G := by
    simpa [G, Function.comp_def] using
      (differentiable_momentJointJetSectionVector
        K (Nat.zero_lt_succ k) F htransport p N).comp
          ((differentiable_sourceJointCoverExp n).comp hline)
  have hsection (y : SourceJointComplexCover n) :
      momentJointJetSectionVector
        K (Nat.zero_lt_succ k) F htransport p N
          (sourceJointCoverExp y) ≠ 0 := by
    intro hzero
    have hsquare := momentJointJetSectionVector_norm_sq
      K (Nat.zero_lt_succ k) F htransport p N
        (sourceJointCoverExp y)
    rw [hzero, norm_zero, zero_pow (by norm_num)] at hsquare
    have hpositive := momentJointJetDiagonal_pos
      K (Nat.zero_lt_succ k) F htransport p N
        (sourceJointCoverExp y).1
          (show (sourceJointCoverExp y).2 ≠ 0 from
            Complex.exp_ne_zero y.2)
    linarith
  have hzero : G 0 ≠ 0 := by
    simpa [G] using hsection q
  have hboundary :
      ∀ w ∈ Metric.sphere (0 : ℂ) |R|, G w ≠ 0 := by
    intro w _
    exact hsection (q + w • v)
  have hmean := log_hilbert_norm_sq_le_circleAverage_all_radius
    hG hzero R hboundary
  have hbase :
      Real.log
        (momentJointJetDiagonal
          K (Nat.zero_lt_succ k) F htransport p N
            (sourceJointCoverExp q)) ≤
        Real.circleAverage
          (fun w : ℂ => Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p N
                (sourceJointCoverExp (q + w • v)))) 0 R := by
    simpa only [G, zero_smul, add_zero,
      momentJointJetSectionVector_norm_sq] using hmean
  have hkreal : 0 < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ k
  have hscaled := (div_le_div_iff_of_pos_right hkreal).mpr hbase
  have havg :
      Real.circleAverage
          (fun w : ℂ => Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p N
                (sourceJointCoverExp (q + w • v)))) 0 R /
            ((k + 1 : ℕ) : ℝ) =
        Real.circleAverage
          (fun w : ℂ =>
            Real.log
              (momentJointJetDiagonal
                K (Nat.zero_lt_succ k) F htransport p N
                  (sourceJointCoverExp (q + w • v))) /
                ((k + 1 : ℕ) : ℝ)) 0 R := by
    rw [show
      (fun w : ℂ =>
        Real.log
          (momentJointJetDiagonal
            K (Nat.zero_lt_succ k) F htransport p N
              (sourceJointCoverExp (q + w • v))) /
            ((k + 1 : ℕ) : ℝ)) =
        (fun w : ℂ => (((k + 1 : ℕ) : ℝ)⁻¹) •
          Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p N
                (sourceJointCoverExp (q + w • v)))) by
        funext w
        simp [div_eq_mul_inv, smul_eq_mul, mul_comm],
      Real.circleAverage_fun_smul]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [momentWeakJointCoverFiniteGeodesic_eq_log_diagonal
    K F htransport p k q]
  change
    Real.log
      (momentJointJetDiagonal
        K (Nat.zero_lt_succ k) F htransport p N
          (sourceJointCoverExp q)) /
        ((k + 1 : ℕ) : ℝ) ≤ _
  calc
    Real.log
        (momentJointJetDiagonal
          K (Nat.zero_lt_succ k) F htransport p N
            (sourceJointCoverExp q)) /
        ((k + 1 : ℕ) : ℝ) ≤
      Real.circleAverage
        (fun w : ℂ => Real.log
          (momentJointJetDiagonal
            K (Nat.zero_lt_succ k) F htransport p N
              (sourceJointCoverExp (q + w • v)))) 0 R /
            ((k + 1 : ℕ) : ℝ) := hscaled
    _ = Real.circleAverage
        (fun w : ℂ =>
          Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p N
                (sourceJointCoverExp (q + w • v))) /
              ((k + 1 : ℕ) : ℝ)) 0 R := havg
    _ = Real.circleAverage
        (fun w : ℂ => momentWeakJointCoverFiniteGeodesic
          K F htransport p k (q + w • v)) 0 R := by
      congr 1
      funext w
      exact (momentWeakJointCoverFiniteGeodesic_eq_log_diagonal
        K F htransport p k (q + w • v)).symm
theorem differentiable_momentWeakBodyScaleJetGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) :
    Differentiable ℝ
      (momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z) := by
  intro t
  unfold momentJetGeodesic
  exact (hasDerivAt_logarithmicPotential
    (momentHolomorphicBasisWeight
      K (Nat.zero_lt_succ k) F htransport
      (momentSimultaneousJetBasis
        K (Nat.zero_lt_succ k) F htransport p) z)
    (momentTruncatedJetOrder K (Nat.zero_lt_succ k)
      F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))))
    (momentHolomorphicBasisWeight_nonneg
      K (Nat.zero_lt_succ k) F htransport
        (momentSimultaneousJetBasis
          K (Nat.zero_lt_succ k) F htransport p) z)
    (exists_positive_momentHolomorphicBasisWeight
      K (Nat.zero_lt_succ k) F htransport
        (momentSimultaneousJetBasis
          K (Nat.zero_lt_succ k) F htransport p) z)
    ((k + 1 : ℕ) : ℝ) t).differentiableAt
theorem momentWeakBodyScaleJetGeodesic_time_shift_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ)
    {s t : ℝ} (hst : s ≤ t) :
    momentJetGeodesic K (Nat.zero_lt_succ k)
      F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) z t ≤
      momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z s +
        BodyScale.canonicalScale K * (t - s) := by
  rcases hst.eq_or_lt with rfl | hst
  · simp
  · let g := momentJetGeodesic K (Nat.zero_lt_succ k)
      F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) z
    have hg : Differentiable ℝ g :=
      differentiable_momentWeakBodyScaleJetGeodesic
        K F htransport p z k
    obtain ⟨c, _, hc⟩ := exists_deriv_eq_slope g hst
      hg.continuous.continuousOn hg.differentiableOn
    have hbound := momentJetGeodesic_deriv_le_floor_cutoff
      K (Nat.zero_lt_succ k) F htransport p
        (BodyScale.canonicalScale_pos K).le z c
    change deriv g c ≤ BodyScale.canonicalScale K at hbound
    rw [hc] at hbound
    have hpositive : 0 < t - s := sub_pos.mpr hst
    have hmul := (div_le_iff₀ hpositive).mp hbound
    change g t ≤ g s + BodyScale.canonicalScale K * (t - s)
    linarith
theorem momentJointGlobalLowerBound_le_coverFiniteGeodesic_zero
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) :
    momentJointGlobalLowerBound K F ≤
      momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z 0 := by
  calc
    momentJointGlobalLowerBound K F ≤
        Real.log
          (diagonalKernel K (k + 1)
            (momentNormalizedPotential F)
            (realLogCoordinate z)) / ((k + 1 : ℕ) : ℝ) :=
      momentJointGlobalLowerBound_le_log_diagonalKernel
        K (Nat.zero_lt_succ k) F htransport (realLogCoordinate z)
    _ = momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z 0 :=
      (momentJetGeodesic_zero_eq_log_diagonalKernel
        K (Nat.zero_lt_succ k) F htransport p z
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ)))).symm
def momentWeakJointCoverFiniteMinorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  momentJointGlobalLowerBound K F +
    BodyScale.canonicalScale K *
      min (sourceJointCoverTime q) 0
theorem continuous_momentWeakJointCoverFiniteMinorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentWeakJointCoverFiniteMinorant K F) := by
  unfold momentWeakJointCoverFiniteMinorant
  exact continuous_const.add
    (continuous_const.mul
      ((continuous_sourceJointCoverTime n).min continuous_const))
theorem momentWeakJointCoverFiniteMinorant_le_finiteGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteMinorant K F q ≤
      momentWeakJointCoverFiniteGeodesic
        K F htransport p k q := by
  have hzero := momentJointGlobalLowerBound_le_coverFiniteGeodesic_zero
    K F htransport p q.1 k
  by_cases ht : 0 ≤ sourceJointCoverTime q
  · have hmono := monotone_momentJetGeodesic
      K (Nat.zero_lt_succ k) F htransport p q.1
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) ht
    simpa [momentWeakJointCoverFiniteMinorant,
      momentWeakJointCoverFiniteGeodesic, min_eq_right ht]
        using hzero.trans hmono
  · have hneg : sourceJointCoverTime q ≤ 0 := le_of_not_ge ht
    have hshift := momentWeakBodyScaleJetGeodesic_time_shift_le
      K F htransport p q.1 k hneg
    unfold momentWeakJointCoverFiniteMinorant
      momentWeakJointCoverFiniteGeodesic
    rw [min_eq_left hneg]
    linarith
theorem momentWeakJointCoverFiniteGeodesic_zero_le_of_tail
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ)
    (hk : momentJointTailStart K F htransport p ≤ k) :
    momentJetGeodesic K (Nat.zero_lt_succ k)
      F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) z 0 ≤
      momentNormalizedPotential F (realLogCoordinate z) +
        BodyScale.canonicalScale K + 1 := by
  let hunit : (0 : ℝ) < 1 := by norm_num
  let q₁ : PositiveJointLogSpace n :=
    sourcePositiveJointTimePoint z 1 hunit
  have htail := momentPositiveJointGeodesic_le_majorant_add_one_of_tail
    K F htransport p k hk q₁
  have hmono := monotone_momentJetGeodesic
    K (Nat.zero_lt_succ k) F htransport p z
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ)))
      (show (0 : ℝ) ≤ 1 by norm_num)
  have htime :
      momentPositiveJointGeodesic K F htransport p k q₁ =
        momentJetGeodesic K (Nat.zero_lt_succ k)
          F htransport p
            (Nat.floor (BodyScale.canonicalScale K *
              ((k + 1 : ℕ) : ℝ))) z 1 := by
    rw [momentPositiveJointGeodesic_eq_momentJetGeodesic]
    change
      momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z (jointLogTime q₁) = _
    rw [show jointLogTime q₁ = 1 by
      exact jointLogTime_sourcePositiveJointTimePoint z 1 hunit]
  have hmajor :
      momentJointMajorant K F q₁ =
        momentNormalizedPotential F (realLogCoordinate z) +
          BodyScale.canonicalScale K := by
    unfold momentJointMajorant
    rw [jointRealCoordinate_sourcePositiveJointTimePoint,
      jointLogTime_sourcePositiveJointTimePoint]
    ring
  rw [htime, hmajor] at htail
  exact hmono.trans htail
def momentWeakJointCoverFiniteMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  momentNormalizedPotential F (realLogCoordinate q.1) +
    BodyScale.canonicalScale K + 1 +
    BodyScale.canonicalScale K *
      max (sourceJointCoverTime q) 0
theorem continuous_momentWeakJointCoverFiniteMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentWeakJointCoverFiniteMajorant K F) := by
  unfold momentWeakJointCoverFiniteMajorant
  exact (((((continuous_momentNormalizedPotential F).comp
    (continuous_momentWeakJointRealLogCoordinate n)).add
      continuous_const).add continuous_const)).add
        (continuous_const.mul
          ((continuous_sourceJointCoverTime n).max continuous_const))
theorem momentWeakJointCoverFiniteGeodesic_le_majorant_of_tail
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (hk : momentJointTailStart K F htransport p ≤ k)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteGeodesic K F htransport p k q ≤
      momentWeakJointCoverFiniteMajorant K F q := by
  have hzero := momentWeakJointCoverFiniteGeodesic_zero_le_of_tail
    K F htransport p q.1 k hk
  by_cases ht : 0 ≤ sourceJointCoverTime q
  · have hshift := momentWeakBodyScaleJetGeodesic_time_shift_le
      K F htransport p q.1 k ht
    unfold momentWeakJointCoverFiniteGeodesic
      momentWeakJointCoverFiniteMajorant
    rw [max_eq_left ht]
    linarith
  · have hneg : sourceJointCoverTime q ≤ 0 := le_of_not_ge ht
    have hmono := monotone_momentJetGeodesic
      K (Nat.zero_lt_succ k) F htransport p q.1
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) hneg
    unfold momentWeakJointCoverFiniteGeodesic
      momentWeakJointCoverFiniteMajorant
    rw [max_eq_right hneg, mul_zero, add_zero]
    exact hmono.trans hzero
def momentWeakJointCoverTailSup
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  sSup (Set.range fun j : ℕ =>
    momentWeakJointCoverFiniteGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r + j) q)
def momentWeakJointCoverTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) : SourceJointComplexCover n → ℝ :=
  upperRegularization (momentWeakJointCoverTailSup
    K F htransport p r)
theorem momentWeakJointCoverTailSup_range_bddAbove
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    BddAbove (Set.range fun j : ℕ =>
      momentWeakJointCoverFiniteGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r + j) q) := by
  refine ⟨momentWeakJointCoverFiniteMajorant K F q, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact momentWeakJointCoverFiniteGeodesic_le_majorant_of_tail
    K F htransport p
      (momentJointTailStart K F htransport p + r + j)
        (by omega) q
theorem momentWeakJointCoverTailSup_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailSup K F htransport p r q ≤
      momentWeakJointCoverFiniteMajorant K F q := by
  unfold momentWeakJointCoverTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact momentWeakJointCoverFiniteGeodesic_le_majorant_of_tail
    K F htransport p
      (momentJointTailStart K F htransport p + r + j)
        (by omega) q
theorem momentWeakJointCoverTailSup_localUpperBounds_nonempty
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    (localUpperBounds
      (momentWeakJointCoverTailSup K F htransport p r) q).Nonempty :=
  localUpperBounds_nonempty_of_continuous_majorant
    (momentWeakJointCoverTailSup K F htransport p r)
    (momentWeakJointCoverFiniteMajorant K F)
    (continuous_momentWeakJointCoverFiniteMajorant K F)
    (momentWeakJointCoverTailSup_le_majorant
      K F htransport p r) q
theorem upperSemicontinuous_momentWeakJointCoverTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) :
    UpperSemicontinuous
      (momentWeakJointCoverTailUpperEnvelope
        K F htransport p r) :=
  upperSemicontinuous_upperRegularization
    (momentWeakJointCoverTailSup K F htransport p r)
    (momentWeakJointCoverTailSup_localUpperBounds_nonempty
      K F htransport p r)
theorem momentWeakJointCoverTailUpperEnvelope_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p r q ≤
        momentWeakJointCoverFiniteMajorant K F q :=
  upperRegularization_le_of_continuous_majorant
    (momentWeakJointCoverTailSup K F htransport p r)
    (momentWeakJointCoverFiniteMajorant K F)
    (continuous_momentWeakJointCoverFiniteMajorant K F)
    (momentWeakJointCoverTailSup_le_majorant
      K F htransport p r) q
theorem momentWeakJointCoverFiniteMinorant_le_tailSup
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteMinorant K F q ≤
      momentWeakJointCoverTailSup K F htransport p r q := by
  calc
    momentWeakJointCoverFiniteMinorant K F q ≤
        momentWeakJointCoverFiniteGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r) q :=
      momentWeakJointCoverFiniteMinorant_le_finiteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r) q
    _ ≤ momentWeakJointCoverTailSup K F htransport p r q := by
      unfold momentWeakJointCoverTailSup
      apply le_csSup
        (momentWeakJointCoverTailSup_range_bddAbove
          K F htransport p r q)
      exact ⟨0, by simp⟩
theorem momentWeakJointCoverFiniteMinorant_le_tailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteMinorant K F q ≤
      momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q := by
  calc
    momentWeakJointCoverFiniteMinorant K F q ≤
        momentWeakJointCoverTailSup K F htransport p r q :=
      momentWeakJointCoverFiniteMinorant_le_tailSup
        K F htransport p r q
    _ ≤ momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q :=
      le_upperRegularization
        (momentWeakJointCoverTailSup K F htransport p r) q
        (momentWeakJointCoverTailSup_localUpperBounds_nonempty
          K F htransport p r q)
theorem momentWeakJointCoverTailSup_antitone
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {r s : ℕ} (hrs : r ≤ s)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailSup K F htransport p s q ≤
      momentWeakJointCoverTailSup K F htransport p r q := by
  unfold momentWeakJointCoverTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  apply le_csSup
    (momentWeakJointCoverTailSup_range_bddAbove
      K F htransport p r q)
  have hindex :
      momentJointTailStart K F htransport p + r + (s - r + j) =
        momentJointTailStart K F htransport p + s + j := by
    omega
  refine ⟨s - r + j, ?_⟩
  change
    momentWeakJointCoverFiniteGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r +
        (s - r + j)) q =
    momentWeakJointCoverFiniteGeodesic K F htransport p
      (momentJointTailStart K F htransport p + s + j) q
  rw [hindex]
theorem momentWeakJointCoverTailUpperEnvelope_antitone
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {r s : ℕ} (hrs : r ≤ s)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p s q ≤
        momentWeakJointCoverTailUpperEnvelope
          K F htransport p r q :=
  upperRegularization_mono
    (momentWeakJointCoverTailSup K F htransport p s)
    (momentWeakJointCoverTailSup K F htransport p r) q
    (momentWeakJointCoverTailSup_antitone
      K F htransport p hrs)
    (momentWeakJointCoverTailSup_localUpperBounds_nonempty
      K F htransport p r q)
theorem momentWeakJointCoverTailUpperEnvelope_bddBelow
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n) :
    BddBelow (Set.range fun r : ℕ =>
      momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q) := by
  refine ⟨momentWeakJointCoverFiniteMinorant K F q, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact momentWeakJointCoverFiniteMinorant_le_tailUpperEnvelope
    K F htransport p r q
def momentWeakJointCoverUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n) : ℝ :=
  ⨅ r : ℕ,
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p r q
theorem upperSemicontinuous_momentWeakJointCoverUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) :
    UpperSemicontinuous
      (momentWeakJointCoverUpperEnvelope
        K F htransport p) :=
  upperSemicontinuous_ciInf
    (momentWeakJointCoverTailUpperEnvelope_bddBelow
      K F htransport p)
    (upperSemicontinuous_momentWeakJointCoverTailUpperEnvelope
      K F htransport p)
theorem tendsto_momentWeakJointCoverTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n) :
    Tendsto
      (fun r : ℕ => momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q) atTop
          (𝓝 (momentWeakJointCoverUpperEnvelope
            K F htransport p q)) :=
  tendsto_atTop_ciInf
    (fun _ _ hrs =>
      momentWeakJointCoverTailUpperEnvelope_antitone
        K F htransport p hrs q)
    (momentWeakJointCoverTailUpperEnvelope_bddBelow
      K F htransport p q)
theorem momentWeakJointCoverFiniteMinorant_le_upperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteMinorant K F q ≤
      momentWeakJointCoverUpperEnvelope
        K F htransport p q :=
  (le_ciInf_iff
    (momentWeakJointCoverTailUpperEnvelope_bddBelow
      K F htransport p q)).mpr
      (fun r => momentWeakJointCoverFiniteMinorant_le_tailUpperEnvelope
        K F htransport p r q)
theorem momentWeakJointCoverUpperEnvelope_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverUpperEnvelope
      K F htransport p q ≤
        momentWeakJointCoverFiniteMajorant K F q := by
  calc
    momentWeakJointCoverUpperEnvelope
        K F htransport p q ≤
      momentWeakJointCoverTailUpperEnvelope
        K F htransport p 0 q :=
      ciInf_le (momentWeakJointCoverTailUpperEnvelope_bddBelow
        K F htransport p q) 0
    _ ≤ momentWeakJointCoverFiniteMajorant K F q :=
      momentWeakJointCoverTailUpperEnvelope_le_majorant
        K F htransport p 0 q
theorem momentWeakJointCoverTailUpperEnvelope_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p r q ≤
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverTailUpperEnvelope
              K F htransport p r (q + w • v)) 0 R := by
  let G : ℕ → SourceJointComplexCover n → ℝ :=
    fun j => momentWeakJointCoverFiniteGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r + j)
  have hGcont (j : ℕ) : Continuous (G j) :=
    continuous_momentWeakJointCoverFiniteGeodesic
      K F htransport p
        (momentJointTailStart K F htransport p + r + j)
  have hlower (j : ℕ) (z : SourceJointComplexCover n) :
      momentWeakJointCoverFiniteMinorant K F z ≤ G j z :=
    momentWeakJointCoverFiniteMinorant_le_finiteGeodesic
      K F htransport p
        (momentJointTailStart K F htransport p + r + j) z
  have hmajor (j : ℕ) (z : SourceJointComplexCover n) :
      G j z ≤ momentWeakJointCoverFiniteMajorant K F z :=
    momentWeakJointCoverFiniteGeodesic_le_majorant_of_tail
      K F htransport p
        (momentJointTailStart K F htransport p + r + j)
          (by omega) z
  have hsub (j : ℕ) (z v' : SourceJointComplexCover n)
      (R' : ℝ) :
      G j z ≤ Real.circleAverage
        (fun w : ℂ => G j (z + w • v')) 0 R' :=
    momentWeakJointCoverFiniteGeodesic_complex_line_submean_all_radius
      K F htransport p
        (momentJointTailStart K F htransport p + r + j)
          z v' R'
  have h :=
    sourceJointCover_upperRegularization_family_complex_line_submean_all_radius
      G hGcont
      (momentWeakJointCoverFiniteMinorant K F)
      (momentWeakJointCoverFiniteMajorant K F)
      (continuous_momentWeakJointCoverFiniteMinorant K F)
      (continuous_momentWeakJointCoverFiniteMajorant K F)
      hlower hmajor hsub q v R
  have hsup :
      (fun z : SourceJointComplexCover n =>
        sSup (Set.range fun j : ℕ => G j z)) =
        momentWeakJointCoverTailSup K F htransport p r := by
    funext z
    rfl
  change
    upperRegularization
        (momentWeakJointCoverTailSup K F htransport p r) q ≤
      Real.circleAverage
        (fun w : ℂ =>
          upperRegularization
            (momentWeakJointCoverTailSup K F htransport p r)
            (q + w • v)) 0 R
  rw [← hsup]
  exact h
theorem momentWeakJointCoverUpperEnvelope_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakJointCoverUpperEnvelope
      K F htransport p q ≤
        Real.circleAverage
          (fun w : ℂ => momentWeakJointCoverUpperEnvelope
            K F htransport p (q + w • v)) 0 R := by
  obtain ⟨L, C, hcompact⟩ :=
    exists_sourceJointCoverCircle_uniform_bounds
      (momentWeakJointCoverFiniteMinorant K F)
      (momentWeakJointCoverFiniteMajorant K F)
      (continuous_momentWeakJointCoverFiniteMinorant K F)
      (continuous_momentWeakJointCoverFiniteMajorant K F)
      q v R
  have hqself : dist q q ≤ (1 : ℝ) := by simp
  have hbound (r : ℕ) (θ : ℝ) :
      L ≤ momentWeakJointCoverTailUpperEnvelope
          K F htransport p r
            (sourceJointCoverCirclePoint q v R θ) ∧
        momentWeakJointCoverTailUpperEnvelope
          K F htransport p r
            (sourceJointCoverCirclePoint q v R θ) ≤ C := by
    obtain ⟨hlo, hup⟩ := (hcompact q hqself).2 θ
    exact ⟨hlo.trans
      (momentWeakJointCoverFiniteMinorant_le_tailUpperEnvelope
        K F htransport p r _),
      (momentWeakJointCoverTailUpperEnvelope_le_majorant
        K F htransport p r _).trans hup⟩
  have havg := tendsto_circleAverage_sourceJointCover_of_dominated
    (fun r : ℕ => momentWeakJointCoverTailUpperEnvelope
      K F htransport p r)
    (momentWeakJointCoverUpperEnvelope K F htransport p)
    (fun r => upperSemicontinuous_momentWeakJointCoverTailUpperEnvelope
      K F htransport p r)
    (fun z => tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p z)
    q v R L C hbound
  exact le_of_tendsto_of_tendsto
    (tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p q)
    havg
    (Filter.Eventually.of_forall fun r =>
      momentWeakJointCoverTailUpperEnvelope_complex_line_submean_all_radius
        K F htransport p r q v R)
end BergmanJetJointHolomorphicClosure
namespace BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicClosure JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeGlobalPlurisubharmonicClosure JetEnvelopeTrueRadialMollifier
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (LogSpace n)) (volume : Measure ℂ)
def momentWeakHolomorphicJointAbsoluteMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  |momentWeakJointCoverFiniteMinorant K F q| +
    |momentWeakJointCoverFiniteMajorant K F q|
theorem continuous_momentWeakHolomorphicJointAbsoluteMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentWeakHolomorphicJointAbsoluteMajorant K F) := by
  unfold momentWeakHolomorphicJointAbsoluteMajorant
  exact (continuous_momentWeakJointCoverFiniteMinorant K F).abs.add
    (continuous_momentWeakJointCoverFiniteMajorant K F).abs
theorem norm_momentWeakJointCoverUpperEnvelope_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n) :
    ‖momentWeakJointCoverUpperEnvelope
        K F htransport p q‖ ≤
      momentWeakHolomorphicJointAbsoluteMajorant K F q := by
  rw [Real.norm_eq_abs]
  unfold momentWeakHolomorphicJointAbsoluteMajorant
  have hl := momentWeakJointCoverFiniteMinorant_le_upperEnvelope
    K F htransport p q
  have hu := momentWeakJointCoverUpperEnvelope_le_majorant
    K F htransport p q
  have hminor := neg_abs_le
    (momentWeakJointCoverFiniteMinorant K F q)
  have hmajor := le_abs_self
    (momentWeakJointCoverFiniteMajorant K F q)
  have hm := abs_nonneg
    (momentWeakJointCoverFiniteMinorant K F q)
  have hM := abs_nonneg
    (momentWeakJointCoverFiniteMajorant K F q)
  exact abs_le.mpr ⟨by linarith, by linarith⟩
theorem measurable_momentWeakJointCoverUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) :
    Measurable (momentWeakJointCoverUpperEnvelope
      K F htransport p) :=
  (upperSemicontinuous_momentWeakJointCoverUpperEnvelope
    K F htransport p).measurable
theorem locallyIntegrable_momentWeakJointCoverUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) :
    LocallyIntegrable
      (momentWeakJointCoverUpperEnvelope K F htransport p)
      (volume : Measure (SourceJointComplexCover n)) := by
  apply locallyIntegrable_iff.mpr
  intro A hA
  have hmajor : IntegrableOn
      (momentWeakHolomorphicJointAbsoluteMajorant K F) A
      (volume : Measure (SourceJointComplexCover n)) :=
    (continuous_momentWeakHolomorphicJointAbsoluteMajorant K F)
      |>.continuousOn.integrableOn_compact hA
  apply hmajor.mono'
    (measurable_momentWeakJointCoverUpperEnvelope
      K F htransport p).aestronglyMeasurable
  filter_upwards [] with q
  exact norm_momentWeakJointCoverUpperEnvelope_le_majorant
    K F htransport p q
def momentWeakHolomorphicJointTrueRadialMollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) : SourceJointComplexCover n → ℝ :=
  sourceJointTrueRadialSmoothed
    (momentWeakJointCoverUpperEnvelope K F htransport p) k
theorem contDiff_momentWeakHolomorphicJointTrueRadialMollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) :
    ContDiff ℝ ∞
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k) := by
  exact contDiff_sourceJointTrueRadialSmoothed
    (locallyIntegrable_momentWeakJointCoverUpperEnvelope
      K F htransport p) k
theorem integrable_momentWeakHolomorphicJointComplexLineIntegrand
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    Integrable
      (fun z : SourceJointComplexCover n × ℝ =>
        sourceJointTrueRadialMollifier n k z.1 *
          momentWeakJointCoverUpperEnvelope K F htransport p
            ((q - z.1) + circleMap 0 R z.2 • v))
      ((volume : Measure (SourceJointComplexCover n)).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  obtain ⟨L, C, hbound⟩ :=
    exists_sourceJointCoverCircle_uniform_bounds
      (fun _ : SourceJointComplexCover n => 0)
      (momentWeakHolomorphicJointAbsoluteMajorant K F)
      continuous_const
      (continuous_momentWeakHolomorphicJointAbsoluteMajorant K F)
      q v R
  have hdom :
      Integrable
        (fun z : SourceJointComplexCover n × ℝ =>
          sourceJointTrueRadialMollifier n k z.1 * C)
        ((volume : Measure (SourceJointComplexCover n)).prod ν) := by
    exact (integrable_sourceJointTrueRadialMollifier n k).mul_prod
      (integrable_const C)
  have hmap : Continuous
      (fun z : SourceJointComplexCover n × ℝ =>
        (q - z.1) + circleMap 0 R z.2 • v) := by
    fun_prop
  have hmeas : Measurable
      (fun z : SourceJointComplexCover n × ℝ =>
        sourceJointTrueRadialMollifier n k z.1 *
          momentWeakJointCoverUpperEnvelope K F htransport p
            ((q - z.1) + circleMap 0 R z.2 • v)) :=
    ((contDiff_sourceJointTrueRadialMollifier n k).continuous.measurable.comp
      measurable_fst).mul
        ((measurable_momentWeakJointCoverUpperEnvelope
          K F htransport p).comp hmap.measurable)
  change Integrable _
    ((volume : Measure (SourceJointComplexCover n)).prod ν)
  apply hdom.mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : sourceJointTrueRadialMollifier n k z.1 = 0
    · simp [hz]
    · have hsupp :=
        support_sourceJointTrueRadialMollifier_subset_closedBall k hz
      have hnorm : ‖z.1‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hsupp
      have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_lt_succ k
      have hradius : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
        apply (div_le_iff₀ hk).mpr
        norm_num
      have hdist : dist (q - z.1) q ≤ 1 := by
        simpa [dist_eq_norm, sub_eq_add_neg,
          add_assoc, add_left_comm, add_comm] using
          hnorm.trans hradius
      have hmaj :
          momentWeakHolomorphicJointAbsoluteMajorant K F
            ((q - z.1) + circleMap 0 R z.2 • v) ≤ C := by
        simpa [sourceJointCoverCirclePoint] using
          ((hbound (q - z.1) hdist).2 z.2).2
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (sourceJointTrueRadialMollifier_nonneg n k z.1)]
      exact mul_le_mul_of_nonneg_left
        ((norm_momentWeakJointCoverUpperEnvelope_le_majorant
          K F htransport p _).trans hmaj)
        (sourceJointTrueRadialMollifier_nonneg n k z.1)
theorem integrable_momentWeakHolomorphicJointComplexLineAverage
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y *
          Real.circleAverage
            (fun w : ℂ =>
              momentWeakJointCoverUpperEnvelope K F htransport p
                ((q - y) + w • v)) 0 R)
      (volume : Measure (SourceJointComplexCover n)) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have hinner :
      Integrable
        (fun y : SourceJointComplexCover n =>
          ∫ θ : ℝ,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope
                K F htransport p
                  ((q - y) + circleMap 0 R θ • v) ∂ν)
        (volume : Measure (SourceJointComplexCover n)) :=
    (integrable_momentWeakHolomorphicJointComplexLineIntegrand
      K F htransport p k q v R).integral_prod_left
  refine (hinner.const_mul ((2 * Real.pi)⁻¹)).congr ?_
  filter_upwards [] with y
  rw [Real.circleAverage_def]
  change
    (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) ∂ν) =
      sourceJointTrueRadialMollifier n k y *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in 0..2 * Real.pi,
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v)))
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  change
    (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) ∂ν) =
      sourceJointTrueRadialMollifier n k y *
        ((2 * Real.pi)⁻¹ *
          (∫ θ : ℝ,
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) ∂ν))
  rw [MeasureTheory.integral_const_mul]
  ring
theorem momentWeakHolomorphicJointComplexLineAverage_integral_eq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverUpperEnvelope K F htransport p
              ((q - y) + w • v)) 0 R) =
      Real.circleAverage
        (fun w : ℂ =>
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (q + w • v)) 0 R := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have hswap :
      (∫ y : SourceJointComplexCover n,
        ∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) ∂ν) =
        ∫ θ : ℝ,
          (∫ y : SourceJointComplexCover n,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope
                K F htransport p
                  ((q - y) + circleMap 0 R θ • v)) ∂ν := by
    exact MeasureTheory.integral_integral_swap
      (integrable_momentWeakHolomorphicJointComplexLineIntegrand
        K F htransport p k q v R)
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverUpperEnvelope
              K F htransport p ((q - y) + w • v)) 0 R) =
      ∫ y : SourceJointComplexCover n,
        (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope
                K F htransport p
                  ((q - y) + circleMap 0 R θ • v) ∂ν := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        rw [Real.circleAverage_def]
        change
          sourceJointTrueRadialMollifier n k y *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in 0..2 * Real.pi,
                momentWeakJointCoverUpperEnvelope
                  K F htransport p
                    ((q - y) + circleMap 0 R θ • v))) =
            (2 * Real.pi)⁻¹ *
              (∫ θ : ℝ,
                sourceJointTrueRadialMollifier n k y *
                  momentWeakJointCoverUpperEnvelope
                    K F htransport p
                      ((q - y) + circleMap 0 R θ • v) ∂ν)
        rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
        change
          sourceJointTrueRadialMollifier n k y *
            ((2 * Real.pi)⁻¹ *
              (∫ θ : ℝ,
                momentWeakJointCoverUpperEnvelope
                  K F htransport p
                    ((q - y) + circleMap 0 R θ • v) ∂ν)) = _
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = (2 * Real.pi)⁻¹ *
          ∫ y : SourceJointComplexCover n,
            ∫ θ : ℝ,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope
                  K F htransport p
                    ((q - y) + circleMap 0 R θ • v) ∂ν := by
      rw [MeasureTheory.integral_const_mul]
    _ = (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            (∫ y : SourceJointComplexCover n,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope
                  K F htransport p
                    ((q - y) + circleMap 0 R θ • v)) ∂ν := by
      rw [hswap]
    _ = (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k
                (q + circleMap 0 R θ • v) ∂ν := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with θ
      unfold momentWeakHolomorphicJointTrueRadialMollification
        sourceJointTrueRadialSmoothed
      rw [MeasureTheory.convolution_def]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      change
        sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) =
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q + circleMap 0 R θ • v) - y)
      congr 2
      abel
    _ = Real.circleAverage
          (fun w : ℂ =>
            momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k (q + w • v)) 0 R := by
      rw [Real.circleAverage_def,
        intervalIntegral.integral_of_le Real.two_pi_pos.le]
      rfl
theorem momentWeakHolomorphicJointTrueRadialMollification_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k q ≤
      Real.circleAverage
        (fun w : ℂ =>
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (q + w • v)) 0 R := by
  rw [← momentWeakHolomorphicJointComplexLineAverage_integral_eq
    K F htransport p k q v R]
  unfold momentWeakHolomorphicJointTrueRadialMollification
    sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  change
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope
          K F htransport p (q - y)) ≤
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          Real.circleAverage
            (fun w : ℂ =>
              momentWeakJointCoverUpperEnvelope
                K F htransport p ((q - y) + w • v)) 0 R
  apply MeasureTheory.integral_mono
    (integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p) k q)
    (integrable_momentWeakHolomorphicJointComplexLineAverage
      K F htransport p k q v R)
  intro y
  exact mul_le_mul_of_nonneg_left
    (momentWeakJointCoverUpperEnvelope_complex_line_submean_all_radius
      K F htransport p (q - y) v R)
    (sourceJointTrueRadialMollifier_nonneg n k y)
end BergmanJetJointHolomorphicPlurisubharmonicSmoothing
namespace BergmanJetJointHolomorphicStrictSchur
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetUpperEnvelope BergmanJetSpatialPeriodicity BergmanJetStrictRadialRegularizer
open BergmanJetJointHolomorphicClosure BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open ActualJetUpperEnvelope JetEnvelopeRightDerivative JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeTrueRadialMollifier JetEnvelopeTrueRadialComplexHessian
open JetEnvelopeTrueRadialLocalHessian JetEnvelopeTrueRadialPerturbedComplexHessianPositiveDefinite
open EnvelopeGeneralTorusDescent TorusHessianPositiveDefinite SchurConvexity
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBrascampLieb MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder MatrixOrder
theorem upperRegularization_sourceJointCover_periodic
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    {d : SourceJointComplexCover n}
    (hf : Function.Periodic f d) :
    Function.Periodic (upperRegularization f) d := by
  intro q
  let h : SourceJointComplexCover n ≃ₜ SourceJointComplexCover n :=
    Homeomorph.addRight d
  have hfun : (fun z : SourceJointComplexCover n => f (h z)) = f := by
    funext z
    exact hf z
  change upperRegularization f (h q) = upperRegularization f q
  rw [← upperRegularization_comp_homeomorph f h q, hfun]
theorem momentWeakJointCoverFiniteGeodesic_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakJointCoverFiniteGeodesic K F htransport p k)
      (imaginaryShift m, (0 : ℂ)) := by
  intro q
  simpa [momentWeakJointCoverFiniteGeodesic,
    sourceJointCoverTime] using
      momentJetGeodesic_spatial_periodic
        K (Nat.zero_lt_succ k) F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ)))
          (sourceJointCoverTime q) m q.1
theorem momentWeakJointCoverFiniteGeodesic_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakJointCoverFiniteGeodesic K F htransport p k)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  intro q
  simp [momentWeakJointCoverFiniteGeodesic,
    sourceJointCoverTime, Complex.add_re, Complex.mul_re]
theorem momentWeakJointCoverTailSup_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakJointCoverTailSup K F htransport p r)
      (imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold momentWeakJointCoverTailSup
  have hfun :
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j)
            (q + (imaginaryShift m, (0 : ℂ)))) =
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j) q) := by
    funext j
    exact momentWeakJointCoverFiniteGeodesic_spatial_periodic
      K F htransport p
        (momentJointTailStart K F htransport p + r + j) m q
  rw [hfun]
theorem momentWeakJointCoverTailSup_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (s : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakJointCoverTailSup K F htransport p s)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  intro q
  unfold momentWeakJointCoverTailSup
  have hfun :
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + s + j)
            (q + ((0 : LogSpace n), (r : ℂ) * Complex.I))) =
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + s + j) q) := by
    funext j
    exact momentWeakJointCoverFiniteGeodesic_imaginary_periodic
      K F htransport p
        (momentJointTailStart K F htransport p + s + j) r q
  rw [hfun]
theorem momentWeakJointCoverTailUpperEnvelope_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakJointCoverTailUpperEnvelope
        K F htransport p r)
      (imaginaryShift m, (0 : ℂ)) := by
  exact upperRegularization_sourceJointCover_periodic
    (momentWeakJointCoverTailSup_spatial_periodic
      K F htransport p r m)
theorem momentWeakJointCoverTailUpperEnvelope_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (s : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakJointCoverTailUpperEnvelope
        K F htransport p s)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  exact upperRegularization_sourceJointCover_periodic
    (momentWeakJointCoverTailSup_imaginary_periodic
      K F htransport p s r)
theorem momentWeakJointCoverUpperEnvelope_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakJointCoverUpperEnvelope K F htransport p)
      (imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold momentWeakJointCoverUpperEnvelope
  congr 1
  funext r
  exact momentWeakJointCoverTailUpperEnvelope_spatial_periodic
    K F htransport p r m q
theorem momentWeakJointCoverUpperEnvelope_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℝ) :
    Function.Periodic
      (momentWeakJointCoverUpperEnvelope K F htransport p)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  intro q
  unfold momentWeakJointCoverUpperEnvelope
  congr 1
  funext s
  exact momentWeakJointCoverTailUpperEnvelope_imaginary_periodic
    K F htransport p s r q
theorem momentWeakHolomorphicJointTrueRadialMollification_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      (imaginaryShift m, (0 : ℂ)) := by
  exact sourceJointTrueRadialSmoothed_periodic
    (momentWeakJointCoverUpperEnvelope_spatial_periodic
      K F htransport p m) k
theorem momentWeakHolomorphicJointTrueRadialMollification_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  exact sourceJointTrueRadialSmoothed_periodic
    (momentWeakJointCoverUpperEnvelope_imaginary_periodic
      K F htransport p r) k
theorem sourceJointSpatialComplexHessian_momentWeakHolomorphicJointTrueRadialMollification_posSemidef
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    (sourceJointSpatialComplexHessian
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k) τ z).PosSemidef := by
  apply sourceJointSpatialComplexHessian_posSemidef_of_local_circle_submean
    ((contDiff_infty.mp
      (contDiff_momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)) 2)
  intro q v
  refine ⟨1, by norm_num, ?_⟩
  intro r _
  exact
    momentWeakHolomorphicJointTrueRadialMollification_complex_line_submean_all_radius
      K F htransport p k q v r
def momentWeakHolomorphicStrictJointCoverWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  (1 - ε) * momentWeakHolomorphicJointTrueRadialMollification
    K F htransport p k q +
      ε * matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K) q.1
theorem contDiff_momentWeakHolomorphicStrictJointCoverWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) :
    ContDiff ℝ ∞
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) := by
  have hfst : ContDiff ℝ ∞
      (fun q : SourceJointComplexCover n => q.1) := by
    fun_prop
  unfold momentWeakHolomorphicStrictJointCoverWeight
  exact (contDiff_const.mul
    (contDiff_momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k)).add
    (contDiff_const.mul
      ((contDiff_matrixSourceCoverPotential
        (contDiff_momentBodyStrictRadialPotential K)).comp hfst))
theorem momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold momentWeakHolomorphicStrictJointCoverWeight
  rw [momentWeakHolomorphicJointTrueRadialMollification_spatial_periodic
    K F htransport p k m q]
  have hp := matrixSourceCoverPotential_periodic
    (momentBodyStrictRadialPotential K) m q.1
  simpa using congrArg (fun x : ℝ =>
    (1 - ε) * momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k q + ε * x) hp
theorem momentWeakHolomorphicStrictJointCoverWeight_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  intro q
  unfold momentWeakHolomorphicStrictJointCoverWeight
  rw [momentWeakHolomorphicJointTrueRadialMollification_imaginary_periodic
    K F htransport p k r q]
  simp
theorem sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_eq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    sourceJointSpatialComplexHessian
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) τ z =
      (1 - ε) • sourceJointSpatialComplexHessian
        (momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k) τ z +
      ε • sourceCoverComplexHessian
        (matrixSourceCoverPotential
          (momentBodyStrictRadialPotential K)) z := by
  change
    sourceCoverComplexHessian
      (fun ξ : LogSpace n =>
        (1 - ε) *
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (ξ, τ) +
        ε * matrixSourceCoverPotential
          (momentBodyStrictRadialPotential K) ξ) z =
      (1 - ε) • sourceCoverComplexHessian
        (fun ξ : LogSpace n =>
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (ξ, τ)) z +
      ε • sourceCoverComplexHessian
        (matrixSourceCoverPotential
          (momentBodyStrictRadialPotential K)) z
  exact sourceCoverComplexHessian_realAffine
    (contDiff_sourceJointSpatialSlice
      ((contDiff_infty.mp
        (contDiff_momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k)) 2) τ)
    ((contDiff_infty.mp
      (contDiff_matrixSourceCoverPotential
        (contDiff_momentBodyStrictRadialPotential K))) 2)
    (1 - ε) ε z
theorem sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_posDef
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    (sourceJointSpatialComplexHessian
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) τ z).PosDef := by
  rw [sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_eq
    K F htransport p ε k τ z]
  exact Matrix.PosDef.posSemidef_add
    ((sourceJointSpatialComplexHessian_momentWeakHolomorphicJointTrueRadialMollification_posSemidef
      K F htransport p k τ z).smul (sub_nonneg.mpr hε₁))
    ((sourceCoverComplexHessian_momentBodyStrictRadialPotential_posDef
      K z).smul hε₀)
def momentWeakHolomorphicStrictJointTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (t : ℝ) (q : LogTorus n) : ℝ :=
  jointSourceTorusWeight
    (momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k) t q
theorem angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight_eq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    angularCoverPotential
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t) =
      sourceJointSpatialSlice
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) (t / 2 : ℂ) := by
  exact angularCoverPotential_jointSourceTorusWeight_eq
    (momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k)
    (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
      K F htransport p ε k) t
theorem contDiff_angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    ContDiff ℝ ∞
      (angularCoverPotential
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) := by
  rw [angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight_eq
    K F htransport p ε k t]
  exact
    (contDiff_momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k).comp
      (contDiff_id.prodMk contDiff_const)
theorem angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_eq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    angularTorusComplexHessianMatrix
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t) q =
      sourceJointSpatialComplexHessian
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k)
        (t / 2 : ℂ) (sourceTorusCoverPoint q) := by
  ext i j
  change
    torusScalarRepresentative
      (fun z => complexHessian
        (angularCoverPotential
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) z i j) q =
      complexHessian
        (sourceJointSpatialSlice
          (momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k) (t / 2 : ℂ))
        (sourceTorusCoverPoint q) i j
  rw [angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight_eq
    K F htransport p ε k t]
  rfl
theorem angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    (angularTorusComplexHessianMatrix
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t) q).PosDef := by
  rw [angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_eq
    K F htransport p ε k t q]
  exact
    sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_posDef
      K F htransport p ε hε₀ hε₁ k
        (t / 2 : ℂ) (sourceTorusCoverPoint q)
theorem continuous_momentWeakHolomorphicStrictJointTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    Continuous (momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t) := by
  exact continuous_jointSourceTorusWeight
    (contDiff_momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k).continuous
    (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
      K F htransport p ε k) t
end BergmanJetJointHolomorphicStrictSchur
namespace BergmanJetJointHolomorphicFullLeviSchur
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open BergmanJetJointHolomorphicStrictSchur JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeGlobalPlurisubharmonicClosure JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian JetEnvelopeTrueRadialLocalHessian
open EnvelopeGeneralTorusDescent RadialSchurBlock RadialFullLeviSchur MatrixTorusBochnerBridge
open MatrixTorusBochnerCore
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder MatrixOrder
theorem convexOn_momentStrictRadialCoordinate :
    ConvexOn ℝ Set.univ momentStrictRadialCoordinate := by
  have hd : deriv momentStrictRadialCoordinate =
      momentStrictRadialCoordinateDerivative := by
    funext y
    exact (hasDerivAt_momentStrictRadialCoordinate y).deriv
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun y =>
      (hasDerivAt_momentStrictRadialCoordinate y).differentiableAt
  · rw [hd]
    exact fun y =>
      (hasDerivAt_momentStrictRadialCoordinateDerivative y)
        |>.differentiableAt
  · intro y
    change 0 ≤ deriv (deriv momentStrictRadialCoordinate) y
    rw [hd, (hasDerivAt_momentStrictRadialCoordinateDerivative y).deriv]
    exact (momentStrictRadialCoordinateSecond_pos y).le
theorem convexOn_momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n) :
    ConvexOn ℝ Set.univ (momentBodyStrictRadialPotential K) := by
  classical
  have hcoord (i : Fin n) :
      ConvexOn ℝ (Set.univ : Set (Space n))
        (fun x : Space n =>
          momentStrictRadialCoordinate
            (momentBodyStrictScale K * x i)) := by
    let L : Space n →ₗ[ℝ] ℝ :=
      momentBodyStrictScale K • (LinearMap.proj i)
    have h := convexOn_momentStrictRadialCoordinate.comp_linearMap L
    simpa [L, Function.comp_def] using h
  have hsum (s : Finset (Fin n)) :
      ConvexOn ℝ (Set.univ : Set (Space n))
        (fun x : Space n =>
          ∑ i ∈ s,
            momentStrictRadialCoordinate
              (momentBodyStrictScale K * x i)) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (convexOn_const (0 : ℝ)
            (convex_univ : Convex ℝ
              (Set.univ : Set (Space n))))
    | @insert i s hi ih =>
        have hadd := (hcoord i).add ih
        have hfun :
            (fun x : Space n =>
              momentStrictRadialCoordinate
                (momentBodyStrictScale K * x i)) +
              (fun x : Space n =>
                ∑ j ∈ s,
                  momentStrictRadialCoordinate
                    (momentBodyStrictScale K * x j)) =
              (fun x : Space n =>
                ∑ j ∈ insert i s,
                  momentStrictRadialCoordinate
                    (momentBodyStrictScale K * x j)) := by
          funext x
          simp [Finset.sum_insert hi]
        rw [hfun] at hadd
        exact hadd
  have hfun :
      (fun x : Space n =>
        ∑ i ∈ (Finset.univ : Finset (Fin n)),
          momentStrictRadialCoordinate
            (momentBodyStrictScale K * x i)) =
        momentBodyStrictRadialPotential K := by
    funext x
    simp [momentBodyStrictRadialPotential]
  rw [← hfun]
  exact hsum (Finset.univ : Finset (Fin n))
def momentBodyStrictJointCoverReference
    {n : ℕ} (K : CenteredBody n)
    (q : SourceJointComplexCover n) : ℝ :=
  matrixSourceCoverPotential (momentBodyStrictRadialPotential K) q.1
theorem continuous_momentBodyStrictJointCoverReference
    {n : ℕ} (K : CenteredBody n) :
    Continuous (momentBodyStrictJointCoverReference K) := by
  unfold momentBodyStrictJointCoverReference
  exact (continuous_matrixSourceCoverPotential
    (contDiff_momentBodyStrictRadialPotential K).continuous).comp
      continuous_fst
theorem momentBodyStrictJointCoverReference_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentBodyStrictJointCoverReference K q ≤
      Real.circleAverage
        (fun w : ℂ => momentBodyStrictJointCoverReference
          K (q + w • v)) 0 R := by
  let f : ℂ → Space n := fun w =>
    sourceCoverRadialLinear n ((q + w • v).1)
  have hf : Continuous f := by
    unfold f
    fun_prop
  have hangle : Continuous
      (fun θ : ℝ => f (circleMap 0 R θ)) :=
    hf.comp (continuous_circleMap 0 R)
  have hfi : IntegrableOn
      (fun θ : ℝ => f (circleMap 0 R θ))
      (Set.Ioc 0 (2 * Real.pi)) volume := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le).mp
    exact hangle.intervalIntegrable 0 (2 * Real.pi)
  have hgi : IntegrableOn
      (momentBodyStrictRadialPotential K ∘
        fun θ : ℝ => f (circleMap 0 R θ))
      (Set.Ioc 0 (2 * Real.pi)) volume := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le).mp
    exact ((contDiff_momentBodyStrictRadialPotential K).continuous.comp
      hangle).intervalIntegrable 0 (2 * Real.pi)
  have hzero :
      (volume : Measure ℝ) (Set.Ioc 0 (2 * Real.pi)) ≠ 0 := by
    rw [Real.volume_Ioc, sub_zero]
    exact (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne'
  have hfinite :
      (volume : Measure ℝ) (Set.Ioc 0 (2 * Real.pi)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hmean :=
    (convexOn_momentBodyStrictRadialPotential K).map_set_average_le
      (contDiff_momentBodyStrictRadialPotential K).continuous.continuousOn
      isClosed_univ hzero hfinite
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      hfi hgi
  have hline : CircleIntegrable
      (fun w : ℂ => (q + w • v).1) 0 R := by
    rw [circleIntegrable_def]
    exact (by fun_prop : Continuous
      (fun θ : ℝ =>
        (q + circleMap 0 R θ • v).1)).intervalIntegrable
          0 (2 * Real.pi)
  have hcenter :
      (⨍ θ in Set.Ioc 0 (2 * Real.pi),
        f (circleMap 0 R θ)) =
        sourceCoverRadialLinear n q.1 := by
    rw [sourceJointCircleAverage_eq_setAverage]
    calc
      Real.circleAverage f 0 R =
        sourceCoverRadialLinear n
          (Real.circleAverage
            (fun w : ℂ => (q + w • v).1) 0 R) := by
            simpa [f, Function.comp_def] using
              (sourceCoverRadialLinear n).circleAverage_comp_comm hline
      _ = sourceCoverRadialLinear n q.1 := by
            rw [sourceJointSpatialLine_circleAverage]
  have htarget :
      (⨍ θ in Set.Ioc 0 (2 * Real.pi),
        momentBodyStrictRadialPotential K
          (f (circleMap 0 R θ))) =
        Real.circleAverage
          (fun w : ℂ => momentBodyStrictRadialPotential K (f w))
          0 R :=
    sourceJointCircleAverage_eq_setAverage
      (fun w : ℂ => momentBodyStrictRadialPotential K (f w)) R
  rw [hcenter, htarget] at hmean
  simpa [f, momentBodyStrictJointCoverReference,
    matrixSourceCoverPotential, sourceCoverRadialLinear] using hmean
theorem momentWeakHolomorphicStrictJointCoverWeight_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k q ≤
      Real.circleAverage
        (fun w : ℂ =>
          momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k (q + w • v)) 0 R := by
  have hm : CircleIntegrable
      (fun w : ℂ =>
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k (q + w • v)) 0 R :=
    circleIntegrable_sourceJointCover_of_continuous
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      (contDiff_momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k).continuous q v R
  have hp : CircleIntegrable
      (fun w : ℂ =>
        momentBodyStrictJointCoverReference K (q + w • v)) 0 R :=
    circleIntegrable_sourceJointCover_of_continuous
      (momentBodyStrictJointCoverReference K)
      (continuous_momentBodyStrictJointCoverReference K)
      q v R
  have hm' : CircleIntegrable
      (fun w : ℂ =>
        (1 - ε) *
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (q + w • v)) 0 R := by
    simpa only [smul_eq_mul] using
      (hm.const_fun_smul (a := 1 - ε))
  have hp' : CircleIntegrable
      (fun w : ℂ =>
        ε * momentBodyStrictJointCoverReference
          K (q + w • v)) 0 R := by
    simpa only [smul_eq_mul] using
      (hp.const_fun_smul (a := ε))
  unfold momentWeakHolomorphicStrictJointCoverWeight
  change
    (1 - ε) *
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k q +
      ε * momentBodyStrictJointCoverReference K q ≤
      Real.circleAverage
        (fun w : ℂ =>
          (1 - ε) *
            momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k (q + w • v) +
          ε * momentBodyStrictJointCoverReference
            K (q + w • v)) 0 R
  rw [Real.circleAverage_fun_add hm' hp']
  change
    (1 - ε) *
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k q +
      ε * momentBodyStrictJointCoverReference K q ≤
      Real.circleAverage
        (fun w : ℂ => (1 - ε) •
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (q + w • v)) 0 R +
      Real.circleAverage
        (fun w : ℂ => ε •
          momentBodyStrictJointCoverReference
            K (q + w • v)) 0 R
  rw [Real.circleAverage_fun_smul,
    Real.circleAverage_fun_smul]
  change
    (1 - ε) *
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k q +
      ε * momentBodyStrictJointCoverReference K q ≤
      (1 - ε) *
          Real.circleAverage
            (fun w : ℂ =>
              momentWeakHolomorphicJointTrueRadialMollification
                K F htransport p k (q + w • v)) 0 R +
        ε *
          Real.circleAverage
            (fun w : ℂ =>
              momentBodyStrictJointCoverReference
                K (q + w • v)) 0 R
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (momentWeakHolomorphicJointTrueRadialMollification_complex_line_submean_all_radius
        K F htransport p k q v R)
      (sub_nonneg.mpr hε₁))
    (mul_le_mul_of_nonneg_left
      (momentBodyStrictJointCoverReference_complex_line_submean_all_radius
        K q v R) hε₀)
theorem sourceJointRealLeviQuadratic_momentWeakHolomorphicStrictJointCoverWeight_nonneg
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (q v : SourceJointComplexCover n) :
    0 ≤ sourceJointRealLeviQuadratic
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) q v := by
  apply sourceJointRealLeviQuadratic_nonnegative_of_local_circle_submean
    ((contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2)
  refine ⟨1, by norm_num, ?_⟩
  intro r _
  exact
    momentWeakHolomorphicStrictJointCoverWeight_complex_line_submean_all_radius
      K F htransport p ε hε₀ hε₁ k q v r
def momentWeakHolomorphicStrictJointCoverSchurBlock
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
  sourceComplexRowSchurBlock
    (sourceJointSpatialComplexHessian
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) τ z)
    (sourceJointCoverAntiholomorphicVelocityGradient
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) τ z)
    (jointSourceCoverAcceleration
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) (z, τ))
theorem momentWeakHolomorphicStrictJointCoverSchurBlock_isHermitian
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    (momentWeakHolomorphicStrictJointCoverSchurBlock
      K F htransport p ε k τ z).IsHermitian := by
  unfold momentWeakHolomorphicStrictJointCoverSchurBlock
  apply sourceComplexRowSchurBlock_isHermitian
  exact sourceJointSpatialComplexHessian_isHermitian
    ((contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2) τ z
theorem momentWeakHolomorphicStrictJointCoverSchurBlock_quadratic_eq_realLevi
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (τ : ℂ) (z : LogSpace n)
    (x : Fin n ⊕ Fin 1 → ℂ) :
    star x ⬝ᵥ
      (momentWeakHolomorphicStrictJointCoverSchurBlock
        K F htransport p ε k τ z *ᵥ x) =
      (sourceJointRealLeviQuadratic
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) (z, τ)
        (star (x ∘ Sum.inl), star (x (Sum.inr 0))) : ℂ) := by
  unfold momentWeakHolomorphicStrictJointCoverSchurBlock
  exact sourceJointCoverRowSchurBlock_quadratic_eq_realLevi
    ((contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2)
    (fun r => momentWeakHolomorphicStrictJointCoverWeight_imaginary_periodic
      K F htransport p ε k r)
    τ z x
theorem momentWeakHolomorphicStrictJointCoverSchurBlock_posSemidef
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (τ : ℂ) (z : LogSpace n) :
    (momentWeakHolomorphicStrictJointCoverSchurBlock
      K F htransport p ε k τ z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (momentWeakHolomorphicStrictJointCoverSchurBlock_isHermitian
      K F htransport p ε k τ z)
  intro x
  rw [momentWeakHolomorphicStrictJointCoverSchurBlock_quadratic_eq_realLevi
    K F htransport p ε k τ z x]
  apply (Complex.nonneg_iff).2
  constructor
  · exact
      sourceJointRealLeviQuadratic_momentWeakHolomorphicStrictJointCoverWeight_nonneg
        K F htransport p ε hε₀ hε₁ k (z, τ)
          (star (x ∘ Sum.inl), star (x (Sum.inr 0)))
  · simp
theorem momentWeakHolomorphicStrictJointCover_rowSchurEnergy_le_acceleration
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (τ : ℂ) (z : LogSpace n) :
    sourceComplexRowSchurEnergyDensity
      (sourceJointSpatialComplexHessian
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) τ z)
      (sourceJointCoverAntiholomorphicVelocityGradient
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) τ z) ≤
      jointSourceCoverAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) (z, τ) := by
  exact sourceComplexRowSchurEnergy_le
    (sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_posDef
      K F htransport p ε hε₀ hε₁ k τ z)
    _ _
    (momentWeakHolomorphicStrictJointCoverSchurBlock_posSemidef
      K F htransport p ε hε₀.le hε₁ k τ z)
end BergmanJetJointHolomorphicFullLeviSchur
namespace BergmanJetJointHolomorphicApproximation
open Set Function Filter MeasureTheory Metric
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicClosure BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialMollifier
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (LogSpace n)) (volume : Measure ℂ)
end BergmanJetJointHolomorphicApproximation
namespace RadialPartitionBounds
open Set Function Filter MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal NNReal Topology ContDiff
def sourceJointRealLogCoordinateCLM (n : ℕ) :
    SourceJointComplexCover n →L[ℝ] Space n :=
  (sourceRealLogCoordinateCLM n).comp
    (ContinuousLinearMap.fst ℝ
      (TorusCharacters.LogSpace n) ℂ)
def sourceJointRealTimeCLM (n : ℕ) :
    SourceJointComplexCover n →L[ℝ] ℝ :=
  (2 : ℝ) •
    (Complex.reCLM.comp
      (ContinuousLinearMap.snd ℝ
        (TorusCharacters.LogSpace n) ℂ))
theorem sourceJointRealTimeCLM_apply {n : ℕ}
    (q : SourceJointComplexCover n) :
    sourceJointRealTimeCLM n q = sourceJointCoverTime q := by
  simp [sourceJointRealTimeCLM, sourceJointCoverTime]
theorem abs_sourceJointCoverTime_sub_le {n : ℕ}
    (q y : SourceJointComplexCover n) :
    |sourceJointCoverTime (q - y)| ≤
      |sourceJointCoverTime q| +
        ‖sourceJointRealTimeCLM n‖ * ‖y‖ := by
  have hop := (sourceJointRealTimeCLM n).le_opNorm y
  rw [Real.norm_eq_abs] at hop
  calc
    |sourceJointCoverTime (q - y)| =
      |sourceJointCoverTime q -
        sourceJointRealTimeCLM n y| := by
          rw [← sourceJointRealTimeCLM_apply,
            map_sub, sourceJointRealTimeCLM_apply]
    _ ≤ |sourceJointCoverTime q| +
          |sourceJointRealTimeCLM n y| := by
      simpa [sub_eq_add_neg] using
        (abs_add_le (sourceJointCoverTime q)
          (-(sourceJointRealTimeCLM n y)))
    _ ≤ |sourceJointCoverTime q| +
          ‖sourceJointRealTimeCLM n‖ * ‖y‖ :=
      add_le_add (le_refl _) hop
end RadialPartitionBounds
namespace TorusFriedrichsCutoff
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters JetEnvelopeRightDerivative EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff
theorem angularSourceRadialCutoff_smul_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : LogTorus n → E}
    (hF : MemLp F 2 (angularWeightedTorusMeasure a))
    (m : ℕ) :
    MemLp
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) • F q)
      2 (angularWeightedTorusMeasure a) := by
  have hscalar : Continuous
      (fun q : LogTorus n => (sourceRadialCutoff m q : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_sourceRadialCutoff m)
  apply hF.of_le_mul (c := (1 : ℝ))
    (hscalar.aestronglyMeasurable.fun_smul hF.aestronglyMeasurable)
  filter_upwards [] with q
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
  exact mul_le_mul_of_nonneg_right
    (sourceRadialCutoff_le_one m q) (norm_nonneg (F q))
def angularSourceCutoffAdjointCommutator
    {n : ℕ} (m : ℕ)
    (W : LogSpace n → LogSpace n)
    (q : LogTorus n) : ℂ :=
  @inner ℂ (EuclideanSpace ℂ (Fin n)) _
    (sourceCutoffBarGradient m q)
    (torusFormRepresentative W q)
theorem continuous_angularSourceCutoffAdjointCommutator
    {n : ℕ} (m : ℕ)
    {W : LogSpace n → LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (hWp : ∀ q : Fin n → ℤ,
      Function.Periodic W (imaginaryShift q)) :
    Continuous (angularSourceCutoffAdjointCommutator m W) := by
  exact (continuous_sourceCutoffBarGradient m).inner
    (continuous_torusFormRepresentative_of_smooth_periodic hW hWp)
end TorusFriedrichsCutoff
namespace RadialAccelerationBounds
open Set Filter Function MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic EnvelopeTorusDescent EnvelopeGeneralTorusDescent
open JetEnvelopeTrueRadialMollifier
open scoped Topology ENNReal Convolution ContDiff
local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (TorusCharacters.LogSpace n))
    (volume : Measure ℂ)
def sourceJointTrueRadialTimeKernel (n k : ℕ)
    (y : SourceJointComplexCover n) : ℝ :=
  (fderiv ℝ (sourceJointTrueRadialMollifier n k) y)
    (sourceJointTimeDirection n)
def sourceJointTrueRadialTimeKernelMass (n k : ℕ) : ℝ :=
  ∫ y : SourceJointComplexCover n,
    |sourceJointTrueRadialTimeKernel n k y|
end RadialAccelerationBounds
namespace TorusWeakDolbeaultMollification
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths DolbeaultRegularity DolbeaultGraphDistributionBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
def normalizedCoverMollification {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ) (k : ℕ) :
    TorusCharacters.LogSpace n → ℂ :=
  (complexShrinkingBump (n := n) k).normed
    (volume : Measure (TorusCharacters.LogSpace n))
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g
theorem contDiff_normalizedCoverMollification
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (k r : ℕ) :
    ContDiff ℝ r (normalizedCoverMollification g k) := by
  let κ : TorusCharacters.LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (TorusCharacters.LogSpace n))
  have hκ : ContDiff ℝ r κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  change ContDiff ℝ r
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g)
  exact hκcompact.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hκ hg
theorem normalizedCoverMollification_periodic
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic g (TorusCharacters.imaginaryShift q))
    (k : ℕ) (q : Fin n → ℤ) :
    Function.Periodic (normalizedCoverMollification g k)
      (TorusCharacters.imaginaryShift q) := by
  exact normalizedShrinkingConvolution_periodic hperiod k q
end TorusWeakDolbeaultMollification
namespace TorusFriedrichsMollifierEstimates
open Set Function Filter MeasureTheory
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal Topology ContDiff Convolution
theorem normalizedCoverBump_convolution_sq_le_convolution_sq
    {n : ℕ} {h : LogSpace n → ℝ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) :
    (∫ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) y * h (x - y)
        ∂(volume : Measure (LogSpace n))) ^ 2 ≤
      ∫ y : LogSpace n,
        (complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) y * h (x - y) ^ 2
          ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.lsmul ℝ ℝ
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hκint : Integrable κ (volume : Measure (LogSpace n)) :=
    hκ.integrable_of_hasCompactSupport hκcompact
  have hfirst : Integrable
      (fun y : LogSpace n => κ y * h (x - y))
      (volume : Measure (LogSpace n)) := by
    have hexists := hκcompact.convolutionExists_right L
      (hh.locallyIntegrable (by norm_num)) hκ x
    simpa [L, mul_comm] using hexists.integrable_swap
  have hsecond : Integrable
      (fun y : LogSpace n => κ y * h (x - y) ^ 2)
      (volume : Measure (LogSpace n)) := by
    have hexists := hκcompact.convolutionExists_right L
      hh.integrable_sq.locallyIntegrable hκ x
    simpa [L, mul_comm] using hexists.integrable_swap
  let m : ℝ :=
    ∫ y : LogSpace n, κ y * h (x - y)
      ∂(volume : Measure (LogSpace n))
  have hnonneg :
      0 ≤ ∫ y : LogSpace n,
        κ y * (h (x - y) - m) ^ 2
          ∂(volume : Measure (LogSpace n)) :=
    integral_nonneg (fun y =>
      mul_nonneg
        ((complexShrinkingBump (n := n) k).nonneg_normed y)
        (sq_nonneg _))
  have hexpand :
      (∫ y : LogSpace n,
        κ y * (h (x - y) - m) ^ 2
          ∂(volume : Measure (LogSpace n))) =
      (∫ y : LogSpace n,
        κ y * h (x - y) ^ 2
          ∂(volume : Measure (LogSpace n))) - m ^ 2 := by
    calc
      (∫ y : LogSpace n,
        κ y * (h (x - y) - m) ^ 2
          ∂(volume : Measure (LogSpace n))) =
        ∫ y : LogSpace n,
          ((κ y * h (x - y) ^ 2 -
            (2 * m) * (κ y * h (x - y))) + m ^ 2 * κ y)
          ∂(volume : Measure (LogSpace n)) := by
          apply integral_congr_ae
          filter_upwards with y
          ring
      _ =
          ((∫ y : LogSpace n,
            κ y * h (x - y) ^ 2
              ∂(volume : Measure (LogSpace n))) -
            (2 * m) *
              (∫ y : LogSpace n,
                κ y * h (x - y)
                  ∂(volume : Measure (LogSpace n)))) +
            m ^ 2 *
              (∫ y : LogSpace n, κ y
                ∂(volume : Measure (LogSpace n))) := by
          calc
            (∫ y : LogSpace n,
              (κ y * h (x - y) ^ 2 -
                (2 * m) * (κ y * h (x - y))) + m ^ 2 * κ y
                ∂(volume : Measure (LogSpace n))) =
              (∫ y : LogSpace n,
                κ y * h (x - y) ^ 2 -
                  (2 * m) * (κ y * h (x - y))
                    ∂(volume : Measure (LogSpace n))) +
                ∫ y : LogSpace n, m ^ 2 * κ y
                  ∂(volume : Measure (LogSpace n)) :=
                MeasureTheory.integral_add
                  (hsecond.sub (hfirst.const_mul (2 * m)))
                  (hκint.const_mul (m ^ 2))
            _ = _ := by
              rw [MeasureTheory.integral_sub hsecond
                (hfirst.const_mul (2 * m)),
                MeasureTheory.integral_const_mul,
                MeasureTheory.integral_const_mul]
      _ = _ := by
          change
            ((∫ y : LogSpace n,
              κ y * h (x - y) ^ 2
                ∂(volume : Measure (LogSpace n))) -
              2 * m * m) +
                m ^ 2 *
                  (∫ y : LogSpace n, κ y
                    ∂(volume : Measure (LogSpace n))) = _
          rw [(complexShrinkingBump (n := n) k).integral_normed]
          ring
  change m ^ 2 ≤ _
  linarith [hnonneg, hexpand]
theorem norm_normalizedCoverMollification_le
    {n : ℕ} {h : LogSpace n → ℂ}
    (k : ℕ) (x : LogSpace n) :
    ‖normalizedCoverMollification h k x‖ ≤
      ∫ y : LogSpace n,
        (complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) y * ‖h (x - y)‖
          ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  change
    ‖(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))] h) x‖ ≤ _
  rw [MeasureTheory.convolution_def]
  calc
    ‖∫ y : LogSpace n,
      (ContinuousLinearMap.lsmul ℝ ℝ) (κ y) (h (x - y))
        ∂(volume : Measure (LogSpace n))‖ ≤
      ∫ y : LogSpace n,
        ‖(ContinuousLinearMap.lsmul ℝ ℝ) (κ y) (h (x - y))‖
          ∂(volume : Measure (LogSpace n)) :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      change ‖κ y • h (x - y)‖ = κ y * ‖h (x - y)‖
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg
          ((complexShrinkingBump (n := n) k).nonneg_normed y)]
theorem normalizedCoverMollification_norm_sq_le_convolution_norm_sq
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) :
    ‖normalizedCoverMollification h k x‖ ^ 2 ≤
      ∫ y : LogSpace n,
        (complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) y * ‖h (x - y)‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
  have hnorm := norm_normalizedCoverMollification_le (h := h) k x
  have hJ := normalizedCoverBump_convolution_sq_le_convolution_sq
    hh.norm k x
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hJ
theorem locallyIntegrable_cover_complex_mul_continuous
    {n : ℕ} {h b : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hb : Continuous b) :
    LocallyIntegrable (fun x => b x * h x)
      (volume : Measure (LogSpace n)) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hprod :=
    (hh.integrableOn_isCompact hK).mul_continuousOn
      hb.continuousOn hK
  simpa [mul_comm] using hprod
def normalizedCoverComplexDriftCommutator {n : ℕ}
    (b h : LogSpace n → ℂ) (k : ℕ) (x : LogSpace n) : ℂ :=
  normalizedCoverMollification (fun y => b y * h y) k x -
    b x * normalizedCoverMollification h k x
theorem continuous_normalizedCoverComplexDriftCommutator
    {n : ℕ} {b h : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hb : Continuous b) (k : ℕ) :
    Continuous (normalizedCoverComplexDriftCommutator b h k) := by
  unfold normalizedCoverComplexDriftCommutator
  exact (contDiff_normalizedCoverMollification
    (locallyIntegrable_cover_complex_mul_continuous hh hb) k 0).continuous.sub
      (hb.mul (contDiff_normalizedCoverMollification hh k 0).continuous)
end TorusFriedrichsMollifierEstimates
namespace TorusDeckPeriodization
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
def complexDeckPeriodization {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℂ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  ∑' q : Fin n → ℤ,
    ψ (z + TorusCharacters.imaginaryShift q)
end TorusDeckPeriodization
namespace TorusDeckCompactSupport
open Set Function Filter MeasureTheory Matrix
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open MatrixTorusBochnerIdentity TorusDeckPeriodization
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
end TorusDeckCompactSupport
namespace TorusDeckGraphAdjoint
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault WeightedTorusBrascampLieb TorusDeckPeriodization TorusDeckCompactSupport
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
theorem continuous_torusFunctionBarPartialRepresentative_of_periodic
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q)) :
    Continuous (torusFunctionBarPartialRepresentative F) := by
  change Continuous
    (fun p : LogTorus n =>
      WithLp.toLp 2
        (fun j : Fin n => sourceTorusBarPartial F j p))
  exact (PiLp.continuous_toLp 2
    (fun _ : Fin n => ℂ)).comp
      (continuous_pi (fun j =>
        continuous_sourceTorusBarPartial hF hperiod j))
theorem hasCompactSupport_torusFunctionBarPartialRepresentative_of_periodic
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F)) :
    HasCompactSupport (torusFunctionBarPartialRepresentative F) := by
  classical
  let K : Set (LogTorus n) :=
    ⋃ j : Fin n, tsupport (sourceTorusBarPartial F j)
  have hK : IsCompact K :=
    isCompact_iUnion (fun j : Fin n =>
      hasCompactSupport_sourceTorusBarPartial F hperiod hcompact j)
  apply HasCompactSupport.intro hK
  intro p hp
  ext j
  change sourceTorusBarPartial F j p = 0
  by_contra hnonzero
  apply hp
  exact Set.mem_iUnion.mpr
    ⟨j, subset_closure ((mem_support).mpr hnonzero)⟩
end TorusDeckGraphAdjoint
namespace TorusDeckFundamentalCell
open Set Function Filter MeasureTheory Matrix
open WeightedTorusDistributionBridge TorusDeckPeriodization
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
end TorusDeckFundamentalCell
namespace TorusWeightedBaseAE
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology ContDiff
end TorusWeightedBaseAE
namespace BergmanJetStrictMixedLocalCore
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusVectorClosedGraphWeakBridge WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology
theorem angularMemLp_locallyIntegrable_base
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {g : LogTorus n → ℂ}
    (hg : MemLp g 2 (angularWeightedTorusMeasure a)) :
    LocallyIntegrable g (sourceTorusBaseMeasure n) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  apply locallyIntegrable_iff.mpr
  intro S hS
  have hweighted : IntegrableOn g S (angularWeightedTorusMeasure a) :=
    (hg.locallyIntegrable (by norm_num)).integrableOn_isCompact hS
  unfold angularWeightedTorusMeasure at hweighted
  change Integrable g
    (((sourceTorusBaseMeasure n).withDensity
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a q))).restrict S)
    at hweighted
  rw [restrict_withDensity hS.measurableSet] at hweighted
  have hdmeas :
      Measurable
        (fun q : LogTorus n =>
          ENNReal.ofReal (angularWeightedTorusDensity a q)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  have hdfinite :
      ∀ᵐ q : LogTorus n
        ∂((sourceTorusBaseMeasure n).restrict S),
        ENNReal.ofReal (angularWeightedTorusDensity a q) < ⊤ :=
    Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top)
  have hscaled :=
    (integrable_withDensity_iff_integrable_smul'
      hdmeas hdfinite).mp hweighted
  have hexp :
      IntegrableOn
        (fun q : LogTorus n =>
          (Real.exp (-a q) : ℂ) * g q)
        S (sourceTorusBaseMeasure n) := by
    apply hscaled.congr
    filter_upwards [] with q
    simp [angularWeightedTorusDensity,
      (Real.exp_pos (-a q)).le, Complex.real_smul]
  have hreciprocal :
      Continuous
        (fun q : LogTorus n => (Real.exp (a q) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp ha)
  have hproduct :=
    hexp.mul_continuousOn hreciprocal.continuousOn hS
  refine hproduct.congr_fun ?_ hS.measurableSet
  intro q hq
  have hcancel :
      (Real.exp (-a q) : ℂ) *
        (Real.exp (a q) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  calc
    ((Real.exp (-a q) : ℂ) * g q) *
        (Real.exp (a q) : ℂ) =
      ((Real.exp (-a q) : ℂ) *
        (Real.exp (a q) : ℂ)) * g q := by
          ring
    _ = g q := by rw [hcancel, one_mul]
theorem angularWeightedScalarL2_locallyIntegrable_base
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (f : angularWeightedScalarL2 a) :
    LocallyIntegrable
      (fun q : LogTorus n => f q)
      (sourceTorusBaseMeasure n) :=
  angularMemLp_locallyIntegrable_base ha
    (MeasureTheory.Lp.memLp f)
theorem angularWeightedFormCoordinate_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (i : Fin n) :
    MemLp
      (fun q : LogTorus n =>
        (W q : EuclideanSpace ℂ (Fin n)) i)
      2 (angularWeightedTorusMeasure a) := by
  simpa [Function.comp_def, formCoordinateCLM] using
    (formCoordinateCLM i).comp_memLp'
      (MeasureTheory.Lp.memLp W)
theorem angularWeightedFormCoordinate_locallyIntegrable_base
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (W : angularWeightedFormL2 a) (i : Fin n) :
    LocallyIntegrable
      (fun q : LogTorus n =>
        (W q : EuclideanSpace ℂ (Fin n)) i)
      (sourceTorusBaseMeasure n) :=
  angularMemLp_locallyIntegrable_base ha
    (angularWeightedFormCoordinate_memLp W i)
theorem angularWeightedScalarCoverLift_locallyIntegrable
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (f : angularWeightedScalarL2 a) :
    LocallyIntegrable
      (complexTorusCoverLift
        (fun q : LogTorus n => f q))
      (volume : Measure (LogSpace n)) := by
  apply complexTorusCoverLift_locallyIntegrable
  simpa [unweightedTorusMeasure, sourceTorusBaseMeasure] using
    angularWeightedScalarL2_locallyIntegrable_base ha f
theorem angularWeightedFormCoordinateCoverLift_locallyIntegrable
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (W : angularWeightedFormL2 a) (i : Fin n) :
    LocallyIntegrable
      (complexTorusCoverLift
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) i))
      (volume : Measure (LogSpace n)) := by
  apply complexTorusCoverLift_locallyIntegrable
  simpa [unweightedTorusMeasure, sourceTorusBaseMeasure] using
    angularWeightedFormCoordinate_locallyIntegrable_base
      ha W i
end BergmanJetStrictMixedLocalCore
namespace MatrixTorusDolbeaultGraph
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusMatrixSquareRootContinuity
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate
  Matrix.Norms.L2Operator ContDiff
def angularMatrixSquareRoot {n : ℕ}
    (H : LogTorus n → Matrix (Fin n) (Fin n) ℂ)
    (q : LogTorus n) : Matrix (Fin n) (Fin n) ℂ :=
  CFC.sqrt (H q)
theorem continuous_angularMatrixSquareRoot {n : ℕ}
    {H : LogTorus n → Matrix (Fin n) (Fin n) ℂ}
    (hcont : Continuous H)
    (hH : ∀ q, (H q).PosDef) :
    Continuous (angularMatrixSquareRoot H) := by
  exact continuous_complexMatrixSquareRoot hcont
    (fun q => (hH q).posSemidef)
theorem continuous_angularMatrixSquareRoot_inverse {n : ℕ}
    {H : LogTorus n → Matrix (Fin n) (Fin n) ℂ}
    (hcont : Continuous H)
    (hH : ∀ q, (H q).PosDef) :
    Continuous (fun q => (angularMatrixSquareRoot H q)⁻¹) := by
  exact continuous_complexMatrixSquareRoot_inverse hcont hH
end MatrixTorusDolbeaultGraph
namespace TorusDeckWeightedUnfolding
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open WeightedTorusBochner TorusWeightedBaseAE
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
end TorusDeckWeightedUnfolding
namespace TorusDeckFullCellDerivative
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge TorusDeckPeriodization TorusDeckFundamentalCell
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff
end TorusDeckFullCellDerivative
namespace MatrixTorusCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge
open WeightedTorusDolbeault TorusWeightedBaseAE
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate ContDiff
def realAngularWeightedFundamentalCellMeasure {n : ℕ}
    (a : LogTorus n → ℝ) (b : Space n) :
    Measure (Space n × Space n) :=
  (realFundamentalCellMeasure b).withDensity
    (fun p => ENNReal.ofReal
      (angularWeightedTorusDensity a (realTorusCoverProjection n p)))
theorem continuous_realTorusCoverProjection (n : ℕ) :
    Continuous (realTorusCoverProjection n) := by
  change Continuous (fun p : Space n × Space n =>
    (p.1, angularCoverProjection n p.2))
  exact (continuous_fst : Continuous
    (fun p : Space n × Space n => p.1)).prodMk
      ((continuous_angularCoverProjection n).comp
        (continuous_snd : Continuous
          (fun p : Space n × Space n => p.2)))
theorem realAngularWeightedFundamentalCell_measurePreserving
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (b : Space n) :
    MeasurePreserving (realTorusCoverProjection n)
      (realAngularWeightedFundamentalCellMeasure a b)
      (angularWeightedTorusMeasure a) := by
  have hp : MeasurePreserving (realTorusCoverProjection n)
      (realFundamentalCellMeasure b) (sourceTorusBaseMeasure n) := by
    simpa [realFundamentalCellMeasure, sourceTorusBaseMeasure] using
      realTorusCoverProjection_measurePreserving
        (volume : Measure (Space n)) b
  refine ⟨hp.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hp.measurable hs]
  change
    (realFundamentalCellMeasure b).withDensity
      (fun p => ENNReal.ofReal
        (angularWeightedTorusDensity a
          (realTorusCoverProjection n p)))
        (realTorusCoverProjection n ⁻¹' s) =
      (sourceTorusBaseMeasure n).withDensity
        (fun q => ENNReal.ofReal
          (angularWeightedTorusDensity a q)) s
  rw [MeasureTheory.withDensity_apply _ (hp.measurable hs),
    MeasureTheory.withDensity_apply _ hs]
  exact hp.setLIntegral_comp_preimage hs
    (ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable)
abbrev angularWeightedCellScalarL2 {n : ℕ}
    (a : LogTorus n → ℝ) (b : Space n) :=
  MeasureTheory.Lp ℂ 2 (realAngularWeightedFundamentalCellMeasure a b)
abbrev angularWeightedCellFormL2 {n : ℕ}
    (a : LogTorus n → ℝ) (b : Space n) :=
  MeasureTheory.Lp (EuclideanSpace ℂ (Fin n)) 2
    (realAngularWeightedFundamentalCellMeasure a b)
def angularScalarFundamentalLiftLI {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) :
    angularWeightedScalarL2 a →ₗᵢ[ℂ]
      angularWeightedCellScalarL2 a b :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (realTorusCoverProjection n)
    (realAngularWeightedFundamentalCell_measurePreserving ha b)
def angularFormFundamentalLiftLI {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) :
    angularWeightedFormL2 a →ₗᵢ[ℂ]
      angularWeightedCellFormL2 a b :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (realTorusCoverProjection n)
    (realAngularWeightedFundamentalCell_measurePreserving ha b)
theorem realAngularWeightedFundamentalCellMeasure_isLocallyFinite
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (b : Space n) :
    IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) := by
  let : IsLocallyFiniteMeasure (realFundamentalCellMeasure b) :=
    realFundamentalCellMeasure_isLocallyFinite b
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    ((continuous_angularWeightedTorusDensity ha).comp
      (continuous_realTorusCoverProjection n))
def inverseAngularCoverWeight {n : ℕ}
    (a : LogTorus n → ℝ)
    (p : Space n × Space n) : ℂ :=
  (Real.exp (a (realTorusCoverProjection n p)) : ℂ)
theorem continuous_inverseAngularCoverWeight {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a) :
    Continuous (inverseAngularCoverWeight a) := by
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (ha.comp (continuous_realTorusCoverProjection n)))
def angularWeightedCellAdjointScalarTest {n : ℕ}
    (a : LogTorus n → ℝ) (ψ : LogSpace n → ℝ)
    (j : Fin n) (p : Space n × Space n) : ℂ :=
  inverseAngularCoverWeight a p *
    coverAdjointScalarTest ψ j (logarithmicCoordinatesEquiv n p)
def angularWeightedCellAdjointVectorTest {n : ℕ}
    (a : LogTorus n → ℝ) (ψ : LogSpace n → ℝ)
    (j : Fin n) (p : Space n × Space n) :
    EuclideanSpace ℂ (Fin n) :=
  inverseAngularCoverWeight a p •
    coverAdjointVectorTest ψ j (logarithmicCoordinatesEquiv n p)
theorem continuous_angularWeightedCellAdjointScalarTest {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (j : Fin n) :
    Continuous (angularWeightedCellAdjointScalarTest a ψ j) := by
  exact (continuous_inverseAngularCoverWeight ha).mul
    ((continuous_coverAdjointScalarTest hψ j).comp
      (logarithmicCoordinatesEquiv n).continuous)
theorem continuous_angularWeightedCellAdjointVectorTest {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (j : Fin n) :
    Continuous (angularWeightedCellAdjointVectorTest a ψ j) := by
  exact (continuous_inverseAngularCoverWeight ha).smul
    ((continuous_coverAdjointVectorTest hψ.continuous j).comp
      (logarithmicCoordinatesEquiv n).continuous)
theorem compactSupport_angularWeightedCellAdjointScalarTest {n : ℕ}
    (a : LogTorus n → ℝ) {ψ : LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (angularWeightedCellAdjointScalarTest a ψ j) := by
  have hcomp : HasCompactSupport
      (fun p : Space n × Space n =>
        coverAdjointScalarTest ψ j
          (logarithmicCoordinatesEquiv n p)) := by
    simpa [Function.comp_def] using
      (compactSupport_coverAdjointScalarTest hψcompact j).comp_homeomorph
        (logarithmicCoordinatesEquiv n).toHomeomorph
  exact hcomp.mul_left
theorem compactSupport_angularWeightedCellAdjointVectorTest {n : ℕ}
    (a : LogTorus n → ℝ) {ψ : LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (angularWeightedCellAdjointVectorTest a ψ j) := by
  have hcomp : HasCompactSupport
      (fun p : Space n × Space n =>
        ψ (logarithmicCoordinatesEquiv n p)) := by
    simpa [Function.comp_def] using
      hψcompact.comp_homeomorph
        (logarithmicCoordinatesEquiv n).toHomeomorph
  refine hcomp.mono ?_
  intro p hp
  exact mt (fun h => by
    simp [angularWeightedCellAdjointVectorTest,
      coverAdjointVectorTest, h]) hp
def angularWeightedCellAdjointVectorL2 {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    angularWeightedCellFormL2 a b := by
  letI : IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) :=
    realAngularWeightedFundamentalCellMeasure_isLocallyFinite ha b
  exact ((continuous_angularWeightedCellAdjointVectorTest
      ha hψ j).memLp_of_hasCompactSupport
      (μ := realAngularWeightedFundamentalCellMeasure a b)
      (compactSupport_angularWeightedCellAdjointVectorTest
        a hψcompact j)).toLp
      (angularWeightedCellAdjointVectorTest a ψ j)
end MatrixTorusCompactGreen
namespace TorusNoncompactBochner
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
end TorusNoncompactBochner
namespace TorusMollifiedBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusDistributionBridge TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff
def angularGraphMollifiedPhysicalField
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a) (k : ℕ) :
    LogSpace n → LogSpace n :=
  fun z i => normalizedCoverMollification
    (complexTorusCoverLift
      (fun q : LogTorus n =>
        (W q : EuclideanSpace ℂ (Fin n)) i)) k z
theorem angularGraphMollifiedPhysicalField_periodic
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (k : ℕ) (q : Fin n → ℤ) :
    Function.Periodic (angularGraphMollifiedPhysicalField W k)
      (imaginaryShift q) := by
  intro z
  funext i
  exact normalizedCoverMollification_periodic
    (fun d => complexTorusCoverLift_periodic
      (fun p : LogTorus n =>
        (W p : EuclideanSpace ℂ (Fin n)) i) d)
    k q z
end TorusMollifiedBochner
namespace WeightedTorusScalarCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open TorusWeakDolbeaultMollification TorusMollifiedBochner BergmanJetStrictMixedLocalCore
open MatrixTorusCompactGreen
open scoped BigOperators ENNReal InnerProductSpace Topology
  ComplexConjugate ContDiff Convolution Manifold
def angularWeightedCellAdjointScalarL2 {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    angularWeightedCellScalarL2 a b := by
  letI : IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) :=
    realAngularWeightedFundamentalCellMeasure_isLocallyFinite ha b
  exact ((continuous_angularWeightedCellAdjointScalarTest
      ha hψ j).memLp_of_hasCompactSupport
      (μ := realAngularWeightedFundamentalCellMeasure a b)
      (compactSupport_angularWeightedCellAdjointScalarTest
        a hψcompact j)).toLp
      (angularWeightedCellAdjointScalarTest a ψ j)
def angularCellScalarAdjointFunctional {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) (u : angularWeightedCellScalarL2 a b) :
    angularDolbeaultGraphAmbient a →L[ℂ] ℂ :=
  ((innerSL ℂ u).comp
    (angularScalarFundamentalLiftLI ha b).toContinuousLinearMap).comp
      (WithLp.fstL 2 ℂ
        (angularWeightedScalarL2 a) (angularWeightedFormL2 a))
def angularCellFormAdjointFunctional {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) (u : angularWeightedCellFormL2 a b) :
    angularDolbeaultGraphAmbient a →L[ℂ] ℂ :=
  ((innerSL ℂ u).comp
    (angularFormFundamentalLiftLI ha b).toContinuousLinearMap).comp
      (WithLp.sndL 2 ℂ
        (angularWeightedScalarL2 a) (angularWeightedFormL2 a))
def angularCellWeakAdjointFunctional {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    angularDolbeaultGraphAmbient a →L[ℂ] ℂ :=
  angularCellScalarAdjointFunctional ha b
    (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j) +
  angularCellFormAdjointFunctional ha b
    (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
theorem contDiff_angularGraphMollifiedPhysicalField
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (W : angularWeightedFormL2 a)
    (k r : ℕ) :
    ContDiff ℝ r (angularGraphMollifiedPhysicalField W k) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_normalizedCoverMollification
    (angularWeightedFormCoordinateCoverLift_locallyIntegrable
      ha W i) k r
end WeightedTorusScalarCompactGreen
namespace TorusMollificationLocalL2Bounds
open Set Function Filter MeasureTheory
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open TorusFriedrichsMollifierEstimates
open scoped BigOperators ENNReal Topology ContDiff Convolution
theorem normalizedCoverMollification_memLp
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) :
    MemLp (normalizedCoverMollification h k) 2
      (volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.mul ℝ ℝ
  let q : LogSpace n → ℝ :=
    κ ⋆[L, (volume : Measure (LogSpace n))]
      (fun x : LogSpace n => ‖h x‖ ^ 2)
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hκint : Integrable κ (volume : Measure (LogSpace n)) :=
    hκ.integrable_of_hasCompactSupport hκcompact
  have hq : Integrable q (volume : Measure (LogSpace n)) :=
    hκint.integrable_convolution L hh.norm.integrable_sq
  have hc : Continuous (normalizedCoverMollification h k) :=
    (contDiff_normalizedCoverMollification
      (hh.locallyIntegrable (by norm_num)) k 0).continuous
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
    hc.aestronglyMeasurable).mpr
  apply hq.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa [q, κ, L, MeasureTheory.convolution_def] using
    normalizedCoverMollification_norm_sq_le_convolution_norm_sq hh k x
end TorusMollificationLocalL2Bounds
namespace TorusWeightedCoverAdjointGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault WeightedTorusBochner WeightedTorusBrascampLieb TorusDeckPeriodization
open TorusDeckGraphAdjoint TorusDeckFundamentalCell TorusDeckFullCellDerivative
open TorusDeckWeightedUnfolding
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
end TorusWeightedCoverAdjointGreen
namespace TorusWeightedCoverGlobalGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
end TorusWeightedCoverGlobalGreen
namespace TorusWeightedAdjointMollification
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault TorusWeakDolbeaultMollification
open TorusFriedrichsMollifierEstimates TorusMollifiedBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
def angularMollifiedPhysicalAdjointDriftCommutator
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a) (k : ℕ)
    (x : LogSpace n) : ℂ :=
  ∑ j : Fin n,
    normalizedCoverComplexDriftCommutator
      (fun z : LogSpace n =>
        holomorphicCoordinate
          (fun y => (angularCoverPotential a y : ℂ)) z j)
      (complexTorusCoverLift
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) j)) k x
end TorusWeightedAdjointMollification
namespace TorusWeightedDensityConvolutionDivergence
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters DolbeaultRegularity
open DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity
open TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
end TorusWeightedDensityConvolutionDivergence
namespace TorusDensityAdaptedWeightedAdjoint
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
end TorusDensityAdaptedWeightedAdjoint
namespace TorusCompactTestGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open TorusMollificationLocalL2Bounds
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
end TorusCompactTestGreen
namespace TorusStrongCoverMollification
open Set Function Filter MeasureTheory
open TorusCharacters MatrixTorusBochnerCoreApproximation TorusWeakDolbeaultMollification
open TorusMollificationLocalL2Bounds TorusCompactTestGreen
open scoped ENNReal Topology ContDiff Convolution
end TorusStrongCoverMollification
namespace TorusClosedMollifierAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open TorusDensityAdaptedWeightedAdjoint
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
def translatedDensityCancelledCoverKernel
    {n : ℕ} (a : LogTorus n → ℝ)
    (k : ℕ) (x : LogSpace n) (y : LogSpace n) : ℝ :=
  (complexShrinkingBump (n := n) k).normed
    (volume : Measure (LogSpace n)) (x - y) /
    coverWeight (angularCoverPotential a) y
end TorusClosedMollifierAdjoint
namespace TorusStrongCoverMollificationDensity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity MatrixTorusBochnerCoreApproximation
open TorusWeakDolbeaultMollification TorusMollificationLocalL2Bounds TorusStrongCoverMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
def normalizedCoverMollificationL2
    {n : ℕ} (k : ℕ)
    (u : MeasureTheory.Lp ℂ 2 (volume : Measure (LogSpace n))) :
    MeasureTheory.Lp ℂ 2 (volume : Measure (LogSpace n)) :=
  (normalizedCoverMollification_memLp (MeasureTheory.Lp.memLp u) k).toLp
    (normalizedCoverMollification (fun x : LogSpace n => u x) k)
end TorusStrongCoverMollificationDensity
namespace TorusStrongWeightedTorusDescent
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeightedCoverAdjointGreen
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
def sourceCompactAngularCoverBox
    {n : ℕ} (S : Set (LogTorus n)) : Set (LogSpace n) :=
  (logarithmicCoordinatesEquiv n) ''
    ((Prod.fst '' S) ×ˢ
      Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
end TorusStrongWeightedTorusDescent
namespace TorusHomogeneousFriedrichs
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge WeightedTorusDolbeault
open TorusWeightedBaseAE TorusWeakDolbeaultMollification TorusStrongCoverMollificationDensity
open TorusStrongWeightedTorusDescent TorusFriedrichsMollifierEstimates
open TorusWeightedAdjointMollification BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
end TorusHomogeneousFriedrichs
namespace RadialPhysicalInverseSquareRootEnergy
open Set Function Filter MeasureTheory Matrix
open RadialSchurBlock
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology ContDiff
theorem complexEuclideanMatrixAction_mul
    {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) =
      Matrix.toEuclideanLin (A * B) v := by
  ext i
  change
    (A *ᵥ (B *ᵥ (fun j : Fin n => v j))) i =
      ((A * B) *ᵥ (fun j : Fin n => v j)) i
  rw [Matrix.mulVec_mulVec]
theorem complexHermitianMatrixAction_norm_sq
    {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin A v‖ ^ 2 =
      RCLike.re
        (@inner ℂ (EuclideanSpace ℂ (Fin n)) _ v
          (Matrix.toEuclideanLin (A * A) v)) := by
  calc
    ‖Matrix.toEuclideanLin A v‖ ^ 2 =
        RCLike.re
          (@inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (Matrix.toEuclideanLin A v)
            (Matrix.toEuclideanLin A v)) :=
      norm_sq_eq_re_inner (Matrix.toEuclideanLin A v)
    _ = RCLike.re
          (@inner ℂ (EuclideanSpace ℂ (Fin n)) _ v
            (Matrix.toEuclideanLin A
              (Matrix.toEuclideanLin A v))) := by
      apply congrArg RCLike.re
      exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
        v (Matrix.toEuclideanLin A v)
    _ = _ := by
      rw [complexEuclideanMatrixAction_mul]
theorem complexPositiveInverseSquareRootAction_norm_sq
    {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹) v‖ ^ 2 =
      RCLike.re
        (@inner ℂ (EuclideanSpace ℂ (Fin n)) _ v
          (Matrix.toEuclideanLin (A⁻¹) v)) := by
  rw [complexHermitianMatrixAction_norm_sq
    hA.isStrictlyPositive.sqrt.posDef.inv.isHermitian]
  rw [← Matrix.mul_inv_rev,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
theorem sourceComplexRowSchurEnergyDensity_eq_inverseSquareRoot_norm_sq
    {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ) :
    sourceComplexRowSchurEnergyDensity A b =
      ‖Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹)
        (WithLp.toLp 2 (star b))‖ ^ 2 := by
  rw [complexPositiveInverseSquareRootAction_norm_sq hA]
  rw [sourceComplexRowSchurEnergyDensity_eq,
    EuclideanSpace.inner_eq_star_dotProduct]
  change
    (b ⬝ᵥ (A⁻¹ *ᵥ star b)).re =
      ((A⁻¹ *ᵥ star b) ⬝ᵥ star (star b)).re
  rw [star_star, dotProduct_comm]
end RadialPhysicalInverseSquareRootEnergy
namespace RadialPhysicalResolventDefectReduction
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
end RadialPhysicalResolventDefectReduction
namespace RadialPhysicalVelocityCompactGraph
open Set Function Filter MeasureTheory Matrix
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
theorem contDiff_complexSourceCoverRadialCutoff_all
    {n : ℕ} (m r : ℕ) :
    ContDiff ℝ r (complexSourceCoverRadialCutoff (n := n) m) := by
  unfold complexSourceCoverRadialCutoff sourceCoverRadialCutoff
  exact Complex.ofRealCLM.contDiff.comp
    ((WeightedResolventConstantCore.growingBump
      (n := n) m).contDiff.comp
        (sourceCoverRadialLinear n).contDiff)
end RadialPhysicalVelocityCompactGraph
namespace TorusRootCurvatureCoercivity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert ComplexKillingSaturationBridge WeightedTorusBochner
open WeightedTorusBrascampLieb
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology ContDiff
def angularTorusConjugatePhysicalFormVector {n : ℕ}
    (W : LogSpace n → Fin n → ℂ) (q : LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2
    (star (fun i : Fin n =>
      torusScalarRepresentative (fun z => W z i) q))
end TorusRootCurvatureCoercivity
namespace RadialPhysicalResolventRootCutoffPairing
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology
def angularEuclideanConjugation {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (star (fun j : Fin n => v j))
theorem norm_angularEuclideanConjugation {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖angularEuclideanConjugation v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp [angularEuclideanConjugation, Pi.star_apply]
theorem continuous_complexEuclideanConjugatedMatrixAction {n : ℕ} :
    Continuous
      (fun Av : Matrix (Fin n) (Fin n) ℂ ×
          EuclideanSpace ℂ (Fin n) =>
        Matrix.toEuclideanLin Av.1
          (angularEuclideanConjugation Av.2)) := by
  change Continuous
    (fun Av : Matrix (Fin n) (Fin n) ℂ ×
        EuclideanSpace ℂ (Fin n) =>
      WithLp.toLp 2 (fun i : Fin n =>
        ∑ j : Fin n, Av.1 i j * conj (Av.2 j)))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact (continuous_fst.matrix_elem i j).mul
    (Complex.continuous_conj.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
        continuous_snd))
theorem aestronglyMeasurable_complexEuclideanConjugatedMatrixAction
    {n : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {A : X → Matrix (Fin n) (Fin n) ℂ}
    {V : X → EuclideanSpace ℂ (Fin n)}
    (hA : AEStronglyMeasurable A μ)
    (hV : AEStronglyMeasurable V μ) :
    AEStronglyMeasurable
      (fun x : X =>
        Matrix.toEuclideanLin (A x)
          (angularEuclideanConjugation (V x))) μ := by
  change AEStronglyMeasurable
    ((fun Av : Matrix (Fin n) (Fin n) ℂ ×
        EuclideanSpace ℂ (Fin n) =>
      Matrix.toEuclideanLin Av.1
        (angularEuclideanConjugation Av.2)) ∘
      (fun x : X => (A x, V x))) μ
  exact (continuous_complexEuclideanConjugatedMatrixAction
    (n := n)).comp_aestronglyMeasurable (hA.prodMk hV)
end RadialPhysicalResolventRootCutoffPairing
namespace TorusWeakRadialCutoffCommutator
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore WeightedTorusDolbeault
open MatrixTorusBochnerCoreConvergence
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
theorem continuous_complexEuclideanOuterProduct_uncurry
    {n : ℕ} :
    Continuous
      (fun vw : EuclideanSpace ℂ (Fin n) ×
          EuclideanSpace ℂ (Fin n) =>
        complexEuclideanOuterProduct vw.1 vw.2) := by
  change Continuous
    (fun vw : EuclideanSpace ℂ (Fin n) ×
        EuclideanSpace ℂ (Fin n) =>
      WithLp.toLp 2 (fun ij : Fin n × Fin n =>
        vw.1 ij.1 * vw.2 ij.2))
  apply (PiLp.continuous_toLp 2
    (fun _ : Fin n × Fin n => ℂ)).comp
  apply continuous_pi
  intro ij
  exact
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) ij.1).comp
      continuous_fst).mul
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) ij.2).comp
      continuous_snd)
def angularWeakSourceCutoffDerivativeCommutator
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) (q : LogTorus n) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  complexEuclideanOuterProduct (W q)
    (sourceCutoffBarGradient m q)
theorem angularWeakSourceCutoffDerivativeCommutator_aestronglyMeasurable
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) :
    AEStronglyMeasurable
      (angularWeakSourceCutoffDerivativeCommutator W m)
      (angularWeightedTorusMeasure a) := by
  change AEStronglyMeasurable
    ((fun vw : EuclideanSpace ℂ (Fin n) ×
        EuclideanSpace ℂ (Fin n) =>
      complexEuclideanOuterProduct vw.1 vw.2) ∘
      (fun q : LogTorus n =>
        (W q, sourceCutoffBarGradient m q)))
    (angularWeightedTorusMeasure a)
  exact (continuous_complexEuclideanOuterProduct_uncurry
    (n := n)).comp_aestronglyMeasurable
      ((MeasureTheory.Lp.memLp W).aestronglyMeasurable.prodMk
        (continuous_sourceCutoffBarGradient m).aestronglyMeasurable)
theorem angularWeakSourceCutoffDerivativeCommutator_norm
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) (q : LogTorus n) :
    ‖angularWeakSourceCutoffDerivativeCommutator W m q‖ =
      ‖W q‖ * ‖sourceCutoffBarGradient m q‖ := by
  exact complexEuclideanOuterProduct_norm
    (W q) (sourceCutoffBarGradient m q)
theorem angularWeakSourceCutoffDerivativeCommutator_norm_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) (q : LogTorus n) :
    ‖angularWeakSourceCutoffDerivativeCommutator W m q‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) * ‖W q‖ := by
  rw [angularWeakSourceCutoffDerivativeCommutator_norm]
  calc
    ‖W q‖ * ‖sourceCutoffBarGradient m q‖ ≤
      ‖W q‖ * (((m : ℝ) + 1)⁻¹ * C) :=
        mul_le_mul_of_nonneg_left
          (sourceCutoffBarGradient_norm_le hC m q)
          (norm_nonneg _)
    _ = _ := by ring
theorem angularWeakSourceCutoffDerivativeCommutator_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    MemLp
      (angularWeakSourceCutoffDerivativeCommutator W m)
      2 (angularWeightedTorusMeasure a) := by
  apply (MeasureTheory.Lp.memLp W).of_le_mul
    (c := ((m : ℝ) + 1)⁻¹ * C)
    (angularWeakSourceCutoffDerivativeCommutator_aestronglyMeasurable
      W m)
  filter_upwards [] with q
  exact angularWeakSourceCutoffDerivativeCommutator_norm_le
    W hC m q
def angularWeakSourceCutoffAdjointCommutator
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) (q : LogTorus n) : ℂ :=
  @inner ℂ (EuclideanSpace ℂ (Fin n)) _
    (sourceCutoffBarGradient m q) (W q)
theorem angularWeakSourceCutoffAdjointCommutator_aestronglyMeasurable
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) :
    AEStronglyMeasurable
      (angularWeakSourceCutoffAdjointCommutator W m)
      (angularWeightedTorusMeasure a) := by
  exact
    ((continuous_sourceCutoffBarGradient m).aestronglyMeasurable).inner
      (MeasureTheory.Lp.memLp W).aestronglyMeasurable
theorem angularWeakSourceCutoffAdjointCommutator_norm_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) (q : LogTorus n) :
    ‖angularWeakSourceCutoffAdjointCommutator W m q‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) * ‖W q‖ := by
  unfold angularWeakSourceCutoffAdjointCommutator
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      (sourceCutoffBarGradient_norm_le hC m q)
      (norm_nonneg _))
theorem angularWeakSourceCutoffAdjointCommutator_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    MemLp
      (angularWeakSourceCutoffAdjointCommutator W m)
      2 (angularWeightedTorusMeasure a) := by
  apply (MeasureTheory.Lp.memLp W).of_le_mul
    (c := ((m : ℝ) + 1)⁻¹ * C)
    (angularWeakSourceCutoffAdjointCommutator_aestronglyMeasurable
      W m)
  filter_upwards [] with q
  exact angularWeakSourceCutoffAdjointCommutator_norm_le W hC m q
end TorusWeakRadialCutoffCommutator
namespace TorusWeakRadialExteriorEnergy
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology
def complexEuclideanAntisymmetricEnergy
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) : ℂ :=
  (∑ i : Fin n, ∑ j : Fin n,
    (M (i, j) - M (j, i)) *
      conj (M (i, j) - M (j, i))) / 2
end TorusWeakRadialExteriorEnergy
namespace TorusWeakRadialBochnerUpperBound
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore WeightedTorusDolbeault
open MatrixTorusBochnerCoreDensity TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology
def angularWeakSourceCutoffAdjointDefectL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (d : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) : angularWeightedScalarL2 a :=
  -(angularSourceRadialCutoff_smul_memLp
      (MeasureTheory.Lp.memLp d) m).toLp
        (fun q : LogTorus n =>
          (sourceRadialCutoff m q : ℂ) • d q) +
    (angularWeakSourceCutoffAdjointCommutator_memLp W hC m).toLp
      (angularWeakSourceCutoffAdjointCommutator W m)
end TorusWeakRadialBochnerUpperBound
namespace TorusClosedMollifiedRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open WeightedTorusBrascampLieb TorusNoncompactBochner TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff
end TorusClosedMollifiedRootBochner
namespace TorusStrongWeightedRadialCutoff
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
end TorusStrongWeightedRadialCutoff
namespace RadialPhysicalResolventRootCutoffUniformExtraction
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedResolventConstantCore MatrixTorusBochnerCoreDensity
open scoped BigOperators ENNReal InnerProductSpace Topology
end RadialPhysicalResolventRootCutoffUniformExtraction
namespace TorusWeakResolventRootBochner
open Set Function Filter MeasureTheory Matrix
open RadialPhysicalResolventRootCutoffPairing
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff
end TorusWeakResolventRootBochner
namespace TorusWeakRadialExteriorMollification
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedPoincare WeightedBrascampLieb
open WeightedResolventConstantCore EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open TorusMollifiedBochner TorusNoncompactBochner TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff
theorem sourceCutoffBarGradient_hasCompactSupport
    {n : ℕ} (m : ℕ) :
    HasCompactSupport (sourceCutoffBarGradient (n := n) m) := by
  let S : Set (LogTorus n) :=
    tsupport (fun x : Space n => growingBump m x) ×ˢ
      (Set.univ : Set (AngularTorus n))
  have hS : IsCompact S :=
    (growingBump (n := n) m).hasCompactSupport.prod isCompact_univ
  apply HasCompactSupport.intro hS
  intro q hq
  have hrad :
      q.1 ∉ tsupport
        (fun x : Space n => growingBump m x) := by
    intro hbase
    exact hq ⟨hbase, Set.mem_univ q.2⟩
  have hder :
      fderiv ℝ
        (fun x : Space n => growingBump m x) q.1 = 0 :=
    fderiv_of_notMem_tsupport ℝ hrad
  have hgrad :
      euclideanGradient
        (fun x : Space n => growingBump m x) q.1 = 0 := by
    ext i
    simp [euclideanGradient, coordinateGradient, hder]
  apply norm_eq_zero.mp
  rw [sourceCutoffBarGradient_norm_eq, hgrad, norm_zero]
theorem sourceCutoffDerivativeCommutator_hasCompactSupport
    {n : ℕ} (m : ℕ)
    (V : LogSpace n → LogSpace n) :
    HasCompactSupport (sourceCutoffDerivativeCommutator m V) := by
  apply (sourceCutoffBarGradient_hasCompactSupport m).mono
  intro q hq
  change sourceCutoffBarGradient m q ≠ 0
  intro hz
  apply hq
  rw [sourceCutoffDerivativeCommutator_eq_outerProduct, hz]
  ext ij
  simp [complexEuclideanOuterProduct]
end TorusWeakRadialExteriorMollification
namespace TorusStrongWeightedCutoffAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerCoreConvergence MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBochner TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusWeightedAdjointMollification TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
theorem angularMollifiedPhysicalAdjointDriftCommutator_periodic
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (k : ℕ) (d : Fin n → ℤ) :
    Function.Periodic
      (angularMollifiedPhysicalAdjointDriftCommutator W k)
      (imaginaryShift d) := by
  intro z
  unfold angularMollifiedPhysicalAdjointDriftCommutator
  apply Finset.sum_congr rfl
  intro j _
  let b : LogSpace n → ℂ := fun x =>
    holomorphicCoordinate
      (fun y => (angularCoverPotential a y : ℂ)) x j
  let h : LogSpace n → ℂ :=
    complexTorusCoverLift
      (fun q => (W q : EuclideanSpace ℂ (Fin n)) j)
  have hb : ∀ e : Fin n → ℤ,
      Function.Periodic b (imaginaryShift e) := by
    intro e
    exact holomorphicCoordinate_periodic
      (fun y => (angularCoverPotential a y : ℂ))
      (complexAngularCoverPotential_periodic a) j e
  have hh : ∀ e : Fin n → ℤ,
      Function.Periodic h (imaginaryShift e) := by
    intro e
    exact complexTorusCoverLift_periodic
      (fun q => (W q : EuclideanSpace ℂ (Fin n)) j) e
  have hp : ∀ e : Fin n → ℤ,
      Function.Periodic (fun x => b x * h x)
        (imaginaryShift e) := by
    intro e x
    change b (x + imaginaryShift e) * h (x + imaginaryShift e) =
      b x * h x
    rw [hb e x, hh e x]
  change
    normalizedCoverMollification (fun x => b x * h x)
        k (z + imaginaryShift d) -
      b (z + imaginaryShift d) *
        normalizedCoverMollification h k (z + imaginaryShift d) =
      normalizedCoverMollification (fun x => b x * h x) k z -
        b z * normalizedCoverMollification h k z
  rw [normalizedCoverMollification_periodic hp k d z,
    hb d z, normalizedCoverMollification_periodic hh k d z]
end TorusStrongWeightedCutoffAdjoint
namespace TorusHomogeneousCutoffAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusFriedrichsMollifierEstimates TorusWeightedAdjointMollification
open TorusStrongWeightedTorusDescent TorusStrongWeightedRadialCutoff TorusFriedrichsCutoff
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
theorem continuous_angularMollifiedPhysicalAdjointDriftCommutator
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a) (k : ℕ) :
    Continuous (angularMollifiedPhysicalAdjointDriftCommutator W k) := by
  unfold angularMollifiedPhysicalAdjointDriftCommutator
  apply continuous_finsetSum
  intro j _
  apply continuous_normalizedCoverComplexDriftCommutator
    (angularWeightedFormCoordinateCoverLift_locallyIntegrable ha W j)
  exact (contDiff_holomorphicCoordinate
    (Complex.ofRealCLM.contDiff.comp ha2) j).continuous
theorem angularClosedMollifiedDrift_fixedRadialCutoff_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) :
    MemLp
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q)
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have hd : Continuous
      (torusScalarRepresentative
        (angularMollifiedPhysicalAdjointDriftCommutator W ℓ)) :=
    continuous_torusScalarRepresentative_of_periodic
      (continuous_angularMollifiedPhysicalAdjointDriftCommutator
        ha ha2 W ℓ)
      (TorusStrongWeightedCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_periodic W ℓ)
  have hc : Continuous
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q) :=
    (Complex.continuous_ofReal.comp
      (continuous_sourceRadialCutoff m)).smul hd
  have hs : HasCompactSupport
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q) := by
    apply (sourceRadialCutoff_hasCompactSupport m).mono
    intro q hq
    change sourceRadialCutoff m q ≠ 0
    intro hz
    apply hq
    simp [hz]
  exact hc.memLp_of_hasCompactSupport hs
theorem angularWeightedScalar_fixedRadialCutoff_mollification_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a)
    (m k : ℕ) :
    MemLp
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n => f r)) k) q)
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have hmoll : Continuous
      (torusScalarRepresentative
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n => f r)) k)) := by
    apply continuous_torusScalarRepresentative_of_periodic
    · exact (contDiff_normalizedCoverMollification
        (angularWeightedScalarCoverLift_locallyIntegrable
          ha f) k 0).continuous
    · intro d
      exact normalizedCoverMollification_periodic
        (fun d' => complexTorusCoverLift_periodic
          (fun q : LogTorus n => f q) d') k d
  have hcont : Continuous
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n => f r)) k) q) :=
    (Complex.continuous_ofReal.comp
      (continuous_sourceRadialCutoff m)).smul hmoll
  have hsupp : HasCompactSupport
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n => f r)) k) q) := by
    apply (sourceRadialCutoff_hasCompactSupport m).mono
    intro q hq
    change sourceRadialCutoff m q ≠ 0
    intro hzero
    apply hq
    simp [hzero]
  exact hcont.memLp_of_hasCompactSupport hsupp
end TorusHomogeneousCutoffAdjoint
namespace TorusHomogeneousRadialMatrix
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert WeightedBrascampLieb
open WeightedResolventConstantCore MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault TorusMollifiedBochner
open TorusWeakRadialCutoffCommutator TorusWeakRadialExteriorMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff
theorem angularClosedMollifiedRadialMatrixCommutator_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) :
    MemLp
      (sourceCutoffDerivativeCommutator m
        (angularGraphMollifiedPhysicalField W ℓ))
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  exact
    (continuous_sourceCutoffDerivativeCommutator m
      (WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
        ha W ℓ 2)
      (angularGraphMollifiedPhysicalField_periodic W ℓ)).memLp_of_hasCompactSupport
        (sourceCutoffDerivativeCommutator_hasCompactSupport m
          (angularGraphMollifiedPhysicalField W ℓ))
def angularClosedMollifiedRadialMatrixCommutatorL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) :
    MeasureTheory.Lp
      (EuclideanSpace ℂ (Fin n × Fin n)) 2
      (angularWeightedTorusMeasure a) :=
  (angularClosedMollifiedRadialMatrixCommutator_memLp
    ha W ℓ m).toLp
      (sourceCutoffDerivativeCommutator m
        (angularGraphMollifiedPhysicalField W ℓ))
end TorusHomogeneousRadialMatrix
namespace TorusHomogeneousResolventGreen
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open TorusDeckWeightedUnfolding TorusWeightedCoverAdjointGreen TorusWeightedCoverGlobalGreen
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold
end TorusHomogeneousResolventGreen
namespace TorusHomogeneousClosedResolventAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBrascampLieb TorusWeakDolbeaultMollification TorusFriedrichsMollifierEstimates
open TorusMollifiedBochner TorusWeightedAdjointMollification
open TorusWeightedDensityConvolutionDivergence TorusClosedMollifierAdjoint
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
end TorusHomogeneousClosedResolventAdjoint
namespace TorusHomogeneousSmoothRootBochner
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph
open RadialPhysicalInverseSquareRootEnergy TorusRootCurvatureCoercivity TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusMollifiedBochner TorusWeakRadialExteriorEnergy
open TorusClosedMollifiedRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff
def angularSmoothCompactHessianRootVector
    {n : ℕ} (a : LogTorus n → ℝ)
    (V : LogSpace n → LogSpace n)
    (m : ℕ) (q : LogTorus n) : EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanLin
    (angularMatrixSquareRoot (angularTorusComplexHessianMatrix a) q)
    (angularTorusConjugatePhysicalFormVector
      (cutoffPhysicalField m V) q)
theorem continuous_angularSmoothCompactHessianRootVector
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → LogSpace n)
    (hV : ContDiff ℝ 2 V)
    (hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d))
    (m : ℕ) :
    Continuous (angularSmoothCompactHessianRootVector a V m) := by
  have hroot := continuous_angularMatrixSquareRoot
    (continuous_angularTorusComplexHessianMatrix ha2) hH
  have hform :=
    continuous_torusFormRepresentative_of_smooth_periodic
      (contDiff_cutoffPhysicalField m hV)
      (cutoffPhysicalField_periodic m hVp)
  change Continuous
    (fun q : LogTorus n =>
      Matrix.toEuclideanLin
        (angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q)
        (angularEuclideanConjugation
          (torusFormRepresentative (cutoffPhysicalField m V) q)))
  change Continuous
    ((fun Av : Matrix (Fin n) (Fin n) ℂ ×
        EuclideanSpace ℂ (Fin n) =>
      Matrix.toEuclideanLin Av.1
        (angularEuclideanConjugation Av.2)) ∘
      (fun q : LogTorus n =>
        (angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q,
         torusFormRepresentative (cutoffPhysicalField m V) q)))
  exact (continuous_complexEuclideanConjugatedMatrixAction
    (n := n)).comp (hroot.prodMk hform)
theorem hasCompactSupport_angularSmoothCompactHessianRootVector
    {n : ℕ} (a : LogTorus n → ℝ)
    (V : LogSpace n → LogSpace n) (m : ℕ) :
    HasCompactSupport (angularSmoothCompactHessianRootVector a V m) := by
  apply (sourceRadialCutoff_hasCompactSupport m).mono
  intro q hq
  change angularSmoothCompactHessianRootVector a V m q ≠ 0 at hq
  change sourceRadialCutoff m q ≠ 0
  intro hzero
  apply hq
  change
    Matrix.toEuclideanLin
      (angularMatrixSquareRoot
        (angularTorusComplexHessianMatrix a) q)
      (angularEuclideanConjugation
        (torusFormRepresentative
          (cutoffPhysicalField m V) q)) = 0
  rw [torusFormRepresentative_cutoffPhysicalField m V q, hzero]
  ext i
  simp [angularEuclideanConjugation, Matrix.mulVec, dotProduct,
    Pi.star_apply]
theorem angularSmoothCompactHessianRootVector_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → LogSpace n)
    (hV : ContDiff ℝ 2 V)
    (hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d))
    (m : ℕ) :
    MemLp (angularSmoothCompactHessianRootVector a V m)
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  exact
    (continuous_angularSmoothCompactHessianRootVector
      ha2 hH V hV hVp m).memLp_of_hasCompactSupport
      (hasCompactSupport_angularSmoothCompactHessianRootVector a V m)
def angularClosedMollifiedRootVectorL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) : angularWeightedFormL2 a :=
  (angularSmoothCompactHessianRootVector_memLp
    ha ha2 hH (angularGraphMollifiedPhysicalField W ℓ)
    (WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2)
    (angularGraphMollifiedPhysicalField_periodic W ℓ)
    m).toLp
      (angularSmoothCompactHessianRootVector a
        (angularGraphMollifiedPhysicalField W ℓ) m)
end TorusHomogeneousSmoothRootBochner
namespace TorusHomogeneousRadialAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert WeightedBrascampLieb
open WeightedResolventConstantCore MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault TorusMollifiedBochner
open TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator TorusWeakRadialExteriorMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff
theorem angularClosedMollifiedRadialAdjointCommutator_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) :
    MemLp
      (angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ))
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have hc : Continuous
      (angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ)) :=
    continuous_angularSourceCutoffAdjointCommutator m
      (WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
        ha W ℓ 2)
      (angularGraphMollifiedPhysicalField_periodic W ℓ)
  have hs : HasCompactSupport
      (angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ)) := by
    apply (sourceCutoffBarGradient_hasCompactSupport m).mono
    intro q hq
    change sourceCutoffBarGradient m q ≠ 0
    intro hz
    apply hq
    simp [angularSourceCutoffAdjointCommutator, hz]
  exact hc.memLp_of_hasCompactSupport hs
def angularClosedMollifiedRadialAdjointCommutatorL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) : angularWeightedScalarL2 a :=
  (angularClosedMollifiedRadialAdjointCommutator_memLp
    ha W ℓ m).toLp
      (angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ))
end TorusHomogeneousRadialAdjoint
namespace TorusHomogeneousWeakResolventRootCoercivity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open JetEnvelopeRightDerivative EqualitySaturatingKillingPaths ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerCoreDensity
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusWeightedAdjointMollification TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy TorusWeakRadialBochnerUpperBound
open TorusWeakRadialExteriorMollification TorusClosedMollifiedRootBochner
open TorusStrongWeightedCutoffAdjoint TorusWeakResolventRootBochner
open RadialPhysicalResolventRootCutoffUniformExtraction TorusHomogeneousSmoothRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff
theorem exists_angularHessianSquareRoot_fiber_bound_on_compact
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {s : Set (LogTorus n)} (hs : IsCompact s) :
    ∃ B : ℝ, 0 < B ∧
      ∀ q ∈ s, ∀ v : EuclideanSpace ℂ (Fin n),
        ‖Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q) v‖ ≤ B * ‖v‖ := by
  have hbdd : BddAbove
      ((fun q : LogTorus n =>
        ‖angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q‖) '' s) :=
    hs.bddAbove_image
      (continuous_angularMatrixSquareRoot
        (continuous_angularTorusComplexHessianMatrix ha2)
        hH).norm.continuousOn
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨max 1 C,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q hq v
  have hroot :
      ‖angularMatrixSquareRoot
        (angularTorusComplexHessianMatrix a) q‖ ≤ max 1 C :=
    (hC ⟨q, hq, rfl⟩).trans (le_max_right _ _)
  change
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
      (angularMatrixSquareRoot
        (angularTorusComplexHessianMatrix a) q) v‖ ≤
      max 1 C * ‖v‖
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)‖ * ‖v‖ :=
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
        (angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q)).le_opNorm v
    _ = ‖angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q‖ * ‖v‖ := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
    _ ≤ _ := mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
def angularPhysicalResolventRootCutoffField
    {n : ℕ} (a : LogTorus n → ℝ)
    (W : angularWeightedFormL2 a)
    (m : ℕ) (q : LogTorus n) : EuclideanSpace ℂ (Fin n) :=
  (sourceRadialCutoff m q : ℂ) •
    Matrix.toEuclideanLin
      (angularMatrixSquareRoot
        (angularTorusComplexHessianMatrix a) q)
      (angularEuclideanConjugation (W q))
theorem angularPhysicalResolventRootCutoffField_aestronglyMeasurable
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a) (m : ℕ) :
    AEStronglyMeasurable
      (angularPhysicalResolventRootCutoffField a W m)
      (angularWeightedTorusMeasure a) := by
  change AEStronglyMeasurable
    (fun q : LogTorus n =>
      (sourceRadialCutoff m q : ℂ) •
        Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation (W q)))
    (angularWeightedTorusMeasure a)
  apply (Complex.continuous_ofReal.comp
    (continuous_sourceRadialCutoff m)).aestronglyMeasurable.smul
  apply aestronglyMeasurable_complexEuclideanConjugatedMatrixAction
  · exact
      (continuous_angularMatrixSquareRoot
        (continuous_angularTorusComplexHessianMatrix ha2)
        hH).aestronglyMeasurable
  · exact (MeasureTheory.Lp.memLp W).aestronglyMeasurable
theorem angularPhysicalResolventRootCutoffField_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a) (m : ℕ) :
    MemLp
      (angularPhysicalResolventRootCutoffField a W m)
      2 (angularWeightedTorusMeasure a) := by
  obtain ⟨B, hB, hb⟩ :=
    exists_angularHessianSquareRoot_fiber_bound_on_compact
      ha2 hH (sourceRadialCutoff_hasCompactSupport m).isCompact
  apply (MeasureTheory.Lp.memLp W).of_le_mul
    (c := B)
    (angularPhysicalResolventRootCutoffField_aestronglyMeasurable
      ha2 hH W m)
  filter_upwards [] with q
  by_cases hq : q ∈ tsupport (sourceRadialCutoff (n := n) m)
  · rw [angularPhysicalResolventRootCutoffField,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
    calc
      sourceRadialCutoff m q *
        ‖Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation (W q))‖ ≤
        ‖Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation (W q))‖ :=
        mul_le_of_le_one_left (norm_nonneg _)
          (sourceRadialCutoff_le_one m q)
      _ ≤ B * ‖angularEuclideanConjugation (W q)‖ :=
        hb q hq _
      _ = B * ‖W q‖ := by
        rw [norm_angularEuclideanConjugation]
  · have hz : sourceRadialCutoff m q = 0 :=
      image_eq_zero_of_notMem_tsupport hq
    simp [angularPhysicalResolventRootCutoffField, hz,
      mul_nonneg hB.le (norm_nonneg _)]
def angularPhysicalResolventRootCutoffL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a) (m : ℕ) :
    angularWeightedFormL2 a :=
  (angularPhysicalResolventRootCutoffField_memLp
    ha2 hH W m).toLp
      (angularPhysicalResolventRootCutoffField a W m)
theorem angularClosedMollifiedRadialAdjoint_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a) (ℓ m : ℕ) :
    MemLp
      (angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)))
      2 (angularWeightedTorusMeasure a) := by
  let V : LogSpace n → LogSpace n :=
    angularGraphMollifiedPhysicalField W ℓ
  have hV : ContDiff ℝ 2 V :=
    WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2
  have hp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d) :=
    angularGraphMollifiedPhysicalField_periodic W ℓ
  have hc : Continuous
      (angularTorusFormAdjoint a (cutoffPhysicalField m V)) := by
    unfold angularTorusFormAdjoint
    apply continuous_finsetSum
    intro i _
    exact continuous_angularTorusWeightedHolomorphicDerivative ha2
      (contDiff_pi.mp (contDiff_cutoffPhysicalField m hV) i)
      (fun d z => congrFun
        (cutoffPhysicalField_periodic m hp d z) i) i
  have hprod := integrable_angularTorusFormAdjoint_mul_conj
    (cutoffPhysicalField m V) ha ha2
    (fun i => contDiff_pi.mp (contDiff_cutoffPhysicalField m hV) i)
    (fun i d z => congrFun
      (cutoffPhysicalField_periodic m hp d z) i)
    (cutoffPhysicalField_coordinate_hasCompactSupport m V)
  have hsquare : Integrable
      (fun q : LogTorus n =>
        ‖angularTorusFormAdjoint a
          (cutoffPhysicalField m V) q‖ ^ 2)
      (angularWeightedTorusMeasure a) := by
    refine hprod.re.congr ?_
    filter_upwards [] with q
    change
      (angularTorusFormAdjoint a
          (cutoffPhysicalField m V) q *
        conj (angularTorusFormAdjoint a
          (cutoffPhysicalField m V) q)).re =
        ‖angularTorusFormAdjoint a
          (cutoffPhysicalField m V) q‖ ^ 2
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq, pow_two, Complex.mul_re]
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
    hc.aestronglyMeasurable).mpr hsquare
def angularClosedMollifiedRadialAdjointL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) : angularWeightedScalarL2 a :=
  (angularClosedMollifiedRadialAdjoint_memLp
    ha ha2 W ℓ m).toLp
      (angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)))
end TorusHomogeneousWeakResolventRootCoercivity
namespace BergmanJetHolomorphicPhysicalMeasure
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence MatrixTorusBochnerBridge
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentMoserTrudinger
open BergmanJetEnvelopePlurisubharmonic BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetStrictRadialRegularizer
open BergmanJetJointHolomorphicStrictSchur JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier EnvelopeSmoothing
open EnvelopeGeneralTorusDescent RadialPartitionBounds LogPartitionConvexity WeightedTorusDolbeault
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution
def momentWeakHolomorphicJointMollifierLowerBound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  momentJointGlobalLowerBound K F -
    BodyScale.canonicalScale K *
      (|sourceJointCoverTime q| + ‖sourceJointRealTimeCLM n‖)
theorem momentWeakHolomorphicJointMollifierLowerBound_le_mollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakHolomorphicJointMollifierLowerBound K F q ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k q := by
  let C : ℝ :=
    momentWeakHolomorphicJointMollifierLowerBound K F q
  have hleft : Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y * C)
      (volume : Measure (SourceJointComplexCover n)) :=
    (integrable_sourceJointTrueRadialMollifier n k).mul_const C
  have hright : Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope
            K F htransport p (q - y))
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p) k q
  change C ≤ _
  unfold momentWeakHolomorphicJointTrueRadialMollification
    sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  calc
    C = ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y * C := by
          rw [MeasureTheory.integral_mul_const,
            integral_sourceJointTrueRadialMollifier, one_mul]
    _ ≤ ∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p (q - y) := by
      apply MeasureTheory.integral_mono hleft hright
      intro y
      by_cases hy : sourceJointTrueRadialMollifier n k y = 0
      · simp [hy]
      · apply mul_le_mul_of_nonneg_left _
          (sourceJointTrueRadialMollifier_nonneg n k y)
        have hball :=
          support_sourceJointTrueRadialMollifier_subset_closedBall k hy
        have hynorm : ‖y‖ ≤ (1 : ℝ) := by
          have hsmall :
              ‖y‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hball
          have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.zero_lt_succ k
          have hradius : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
            apply (div_le_iff₀ hk).mpr
            norm_num
          exact hsmall.trans hradius
        have htime :
            |sourceJointCoverTime (q - y)| ≤
              |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
          calc
            |sourceJointCoverTime (q - y)| ≤
                |sourceJointCoverTime q| +
                  ‖sourceJointRealTimeCLM n‖ * ‖y‖ :=
              abs_sourceJointCoverTime_sub_le q y
            _ ≤ |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
              exact add_le_add (le_refl _)
                (mul_le_of_le_one_right
                  (norm_nonneg (sourceJointRealTimeCLM n)) hynorm)
        have hmin :
            -(|sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖) ≤
              min (sourceJointCoverTime (q - y)) 0 := by
          apply le_min
          · linarith [neg_abs_le (sourceJointCoverTime (q - y))]
          · have hn :
                0 ≤ |sourceJointCoverTime q| +
                  ‖sourceJointRealTimeCLM n‖ :=
                add_nonneg (abs_nonneg _) (norm_nonneg _)
            linarith
        calc
          C ≤ momentWeakJointCoverFiniteMinorant
              K F (q - y) := by
                dsimp [C,
                  momentWeakHolomorphicJointMollifierLowerBound,
                  momentWeakJointCoverFiniteMinorant]
                nlinarith [BodyScale.canonicalScale_pos K]
          _ ≤ momentWeakJointCoverUpperEnvelope
              K F htransport p (q - y) :=
            momentWeakJointCoverFiniteMinorant_le_upperEnvelope
              K F htransport p (q - y)
def momentWeakHolomorphicJointTimeLowerBound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) (t : ℝ) : ℝ :=
  momentJointGlobalLowerBound K F -
    BodyScale.canonicalScale K *
      (|t| + ‖sourceJointRealTimeCLM n‖)
theorem momentWeakHolomorphicJointTimeLowerBound_le_mollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) (t : ℝ) :
    momentWeakHolomorphicJointTimeLowerBound K F t ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k (sourceJointTimeEmbedding z t) := by
  simpa [momentWeakHolomorphicJointTimeLowerBound,
    momentWeakHolomorphicJointMollifierLowerBound,
    sourceJointCoverTime_timeEmbedding] using
      momentWeakHolomorphicJointMollifierLowerBound_le_mollification
        K F htransport p k (sourceJointTimeEmbedding z t)
theorem momentWeakHolomorphicStrictRadialPotential_norm_lower
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    momentBodyStrictScale K * ‖x‖ ≤
      momentBodyStrictRadialPotential K x := by
  calc
    momentBodyStrictScale K * ‖x‖ ≤
        momentBodyStrictScale K *
          (∑ i : Fin n, |x i|) := by
      exact mul_le_mul_of_nonneg_left
        (SupportFunction.norm_le_sum_abs x)
        (momentBodyStrictScale_pos K).le
    _ ≤ momentBodyStrictRadialPotential K x :=
      momentBodyStrictRadialPotential_sum_abs_lower K x
theorem momentWeakHolomorphicStrictJointTorusWeight_norm_coercivity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (q : LogTorus n) :
    (ε * momentBodyStrictScale K) * ‖q.1‖ +
        (1 - ε) * momentWeakHolomorphicJointTimeLowerBound K F t ≤
      momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t q := by
  have hweak :=
    momentWeakHolomorphicJointTimeLowerBound_le_mollification
      K F htransport p (sourceTorusCoverPoint q) k t
  have hrad :=
    momentWeakHolomorphicStrictRadialPotential_norm_lower K q.1
  have hweak' := mul_le_mul_of_nonneg_left hweak
    (sub_nonneg.mpr hε₁)
  have hrad' := mul_le_mul_of_nonneg_left hrad hε₀
  rw [momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover]
  unfold momentWeakHolomorphicStrictJointCoverWeight
  have href :
      matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t).1 =
        momentBodyStrictRadialPotential K q.1 := by
    simp [sourceJointTimeEmbedding, sourceTorusCoverPoint,
      matrixSourceCoverPotential_logarithmicPoint]
  rw [href]
  nlinarith
theorem integrable_exp_neg_momentWeakHolomorphicStrictJointTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    Integrable
      (fun q : LogTorus n =>
        Real.exp
          (-momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t q))
      (sourceTorusBaseMeasure n) := by
  let δ : ℝ := ε * momentBodyStrictScale K
  let C : ℝ :=
    -(1 - ε) * momentWeakHolomorphicJointTimeLowerBound K F t
  have hδ : 0 < δ :=
    mul_pos hε₀ (momentBodyStrictScale_pos K)
  have hrad : Integrable
      (fun x : Space n => Real.exp (-δ * ‖x‖))
      (volume : Measure (Space n)) :=
    integrable_exp_neg_mul_norm_all hδ
  have hang : Integrable
      (fun _ : AngularTorus n => (1 : ℝ))
      (angularMeasure n) :=
    integrable_const 1
  have hprod : Integrable
      (fun q : LogTorus n =>
        Real.exp (-δ * ‖q.1‖) * (1 : ℝ))
      (sourceTorusBaseMeasure n) := by
    simpa [sourceTorusBaseMeasure] using hrad.mul_prod hang
  have hmajor := hprod.const_mul (Real.exp C)
  have hmeas : AEStronglyMeasurable
      (fun q : LogTorus n =>
        Real.exp
          (-momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t q))
      (sourceTorusBaseMeasure n) :=
    (Real.continuous_exp.comp
      (continuous_momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t).neg).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with q
  change
    ‖Real.exp
        (-momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t q)‖ ≤
      Real.exp C * (Real.exp (-δ * ‖q.1‖) * (1 : ℝ))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [mul_one]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc :=
    momentWeakHolomorphicStrictJointTorusWeight_norm_coercivity
      K F htransport p k t hε₀.le hε₁ q
  dsimp [δ, C]
  linarith
theorem momentWeakHolomorphicStrictJointWeightedMeasure_isFinite
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    IsFiniteMeasure
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) := by
  apply angularWeightedTorusMeasure_isFinite_of_integrable
  exact integrable_exp_neg_momentWeakHolomorphicStrictJointTorusWeight
    K F htransport p k t hε₀ hε₁
end BergmanJetHolomorphicPhysicalMeasure
namespace BergmanJetJointHolomorphicPhysicalApproximation
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentMoserTrudinger BergmanJetTorusEnvelope
open BergmanJetTorusCoercivity BergmanJetStrictRadialRegularizer
open BergmanJetJointEnvelopeRegularization BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open BergmanJetJointHolomorphicApproximation BergmanJetHolomorphicPhysicalMeasure
open JetEnvelopeRightDerivative JetEnvelopeSlopeConvergence JetEnvelopeGlobalPlurisubharmonic
open EnvelopeSmoothing EnvelopeGeneralTorusDescent LogPartitionConvexity
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
def momentWeakHolomorphicUniformRadialRate
    {n : ℕ} (K : CenteredBody n) : ℝ :=
  min (((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹)
    (momentBodyStrictScale K)
def momentWeakHolomorphicUniformCoercivityConstant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) : ℝ :=
  max (momentTorusEnvelopeCoercivityConstant K F htransport) 0
def momentWeakHolomorphicUniformDensityMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (q : LogTorus n) : ℝ :=
  Real.exp
      (momentWeakHolomorphicUniformCoercivityConstant
        K F htransport) *
    (Real.exp
      (-momentWeakHolomorphicUniformRadialRate K * ‖q.1‖) *
      (1 : ℝ))
end BergmanJetJointHolomorphicPhysicalApproximation
namespace BergmanJetTorusRightSlopeBridge
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert SupportFunction LaplaceAsymptotics BergmanMonomials
open BergmanGeodesicConvexity JetEnvelopeRightDerivative ActualJetUpperEnvelope MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakGlobalKernel
open BergmanJetGeodesic BergmanJetProfileBridge BergmanJetRealGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopeLimit BergmanJetTorusEnvelope BergmanJetTorusSlopeBridge
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal InnerProductSpace Topology
def momentTorusJetSlope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : LogTorus n) : ℝ :=
  if hk : 0 < k then
    momentPositiveTorusJetSlope
      K hk F htransport p
        (Nat.floor
          (BodyScale.canonicalScale K * (k : ℝ))) q
  else 0
end BergmanJetTorusRightSlopeBridge
namespace BergmanJetTorusRightSlopeGibbsBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity
open BergmanJetTorusEnvelope BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge
open scoped BigOperators ENNReal Topology
def momentBodyEnvelopePositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (q : LogTorus n) : ℝ :=
  (momentBodyTorusWeight K p t q -
    momentBodyTorusWeight K p 0 q) / t
end BergmanJetTorusRightSlopeGibbsBridge
namespace BergmanJetPortmanteauSlopeBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal NNReal Topology
end BergmanJetPortmanteauSlopeBridge
namespace BergmanJetPortmanteauUpperTailBridge
open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology
end BergmanJetPortmanteauUpperTailBridge
namespace BergmanJetPortmanteauMovingUpperTailBridge
open Set Function Filter MeasureTheory
open BergmanJetPortmanteauSlopeBridge BergmanJetPortmanteauUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology
def movingUpperLevelClosedTail
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (t : ℝ) (N : ℕ) : Set X :=
  closure (⋃ k : ℕ, ⋃ (_ : N ≤ k), {x : X | t ≤ f k x})
end BergmanJetPortmanteauMovingUpperTailBridge
namespace TorusHomogeneousBrascampLieb
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBrascampLieb
open MatrixTorusDolbeaultGraph TorusDeckGraphAdjoint TorusFriedrichsCutoff
open RadialPhysicalVelocityCompactGraph RadialPhysicalInverseSquareRootEnergy
open RadialPhysicalResolventRootCutoffPairing RadialPhysicalResolventDefectReduction
open TorusHomogeneousWeakResolventRootCoercivity
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff
def angularSourceFreeScalarRadialGraphTest
    {n : ℕ} (U : LogSpace n → ℂ) (m : ℕ) (z : LogSpace n) : ℂ :=
  complexSourceCoverRadialCutoff m z * U z
theorem contDiff_angularSourceFreeScalarRadialGraphTest
    {n : ℕ} {U : LogSpace n → ℂ}
    (hU : ContDiff ℝ 3 U) (m : ℕ) :
    ContDiff ℝ 3 (angularSourceFreeScalarRadialGraphTest U m) := by
  exact (contDiff_complexSourceCoverRadialCutoff_all m 3).mul hU
theorem angularSourceFreeScalarRadialGraphTest_periodic
    {n : ℕ} {U : LogSpace n → ℂ}
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (m : ℕ) (d : Fin n → ℤ) :
    Function.Periodic
      (angularSourceFreeScalarRadialGraphTest U m)
      (imaginaryShift d) := by
  intro z
  unfold angularSourceFreeScalarRadialGraphTest
  rw [complexSourceCoverRadialCutoff_periodic m d z, hperiod d z]
theorem torusScalarRepresentative_angularSourceFreeScalarRadialGraphTest
    {n : ℕ} (U : LogSpace n → ℂ) (m : ℕ) (q : LogTorus n) :
    torusScalarRepresentative
      (angularSourceFreeScalarRadialGraphTest U m) q =
      (sourceRadialCutoff m q : ℂ) * torusScalarRepresentative U q := by
  unfold angularSourceFreeScalarRadialGraphTest
  rw [torusScalarRepresentative_mul,
    torusScalarRepresentative_complexSourceCoverRadialCutoff]
theorem hasCompactSupport_angularSourceFreeScalarRadialGraphTest
    {n : ℕ} (U : LogSpace n → ℂ) (m : ℕ) :
    HasCompactSupport
      (torusScalarRepresentative
        (angularSourceFreeScalarRadialGraphTest U m)) := by
  have heq :
      torusScalarRepresentative
        (angularSourceFreeScalarRadialGraphTest U m) =
      fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) * torusScalarRepresentative U q := by
    funext q
    exact torusScalarRepresentative_angularSourceFreeScalarRadialGraphTest
      U m q
  rw [heq]
  exact (complexSourceRadialCutoff_hasCompactSupport m).mul_right
theorem angularSourceFreeScalarRadialGraphTest_scalar_memLp
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (m : ℕ) :
    MemLp
      (torusScalarRepresentative
        (angularSourceFreeScalarRadialGraphTest U m)) 2
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  apply (continuous_torusScalarRepresentative_of_periodic
    (contDiff_angularSourceFreeScalarRadialGraphTest hU m).continuous
    (angularSourceFreeScalarRadialGraphTest_periodic hperiod m)).memLp_of_hasCompactSupport
  exact hasCompactSupport_angularSourceFreeScalarRadialGraphTest U m
theorem angularSourceFreeScalarRadialGraphTest_barPartial_memLp
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (m : ℕ) :
    MemLp
      (torusFunctionBarPartialRepresentative
        (angularSourceFreeScalarRadialGraphTest U m)) 2
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  let V : LogSpace n → ℂ := angularSourceFreeScalarRadialGraphTest U m
  have hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d) :=
    angularSourceFreeScalarRadialGraphTest_periodic hperiod m
  apply (continuous_torusFunctionBarPartialRepresentative_of_periodic
    ((contDiff_angularSourceFreeScalarRadialGraphTest hU m).of_le
      (by norm_num)) hVp).memLp_of_hasCompactSupport
  exact hasCompactSupport_torusFunctionBarPartialRepresentative_of_periodic
    V hVp (hasCompactSupport_angularSourceFreeScalarRadialGraphTest U m)
def angularSourceFreeScalarCutoffGradient
    {n : ℕ} (U : LogSpace n → ℂ)
    (m : ℕ) (q : LogTorus n) : EuclideanSpace ℂ (Fin n) :=
  torusScalarRepresentative U q • sourceCutoffBarGradient m q
theorem continuous_angularSourceFreeScalarCutoffGradient
    {n : ℕ} {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (m : ℕ) :
    Continuous (angularSourceFreeScalarCutoffGradient U m) := by
  exact (continuous_torusScalarRepresentative_of_periodic
    hU.continuous hperiod).smul (continuous_sourceCutoffBarGradient m)
theorem angularSourceFreeScalarCutoffGradient_norm_le
    {n : ℕ} (U : LogSpace n → ℂ)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y : Space n => unitBump y) x‖ ≤ C)
    (m : ℕ) (q : LogTorus n) :
    ‖angularSourceFreeScalarCutoffGradient U m q‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) * ‖torusScalarRepresentative U q‖ := by
  unfold angularSourceFreeScalarCutoffGradient
  rw [norm_smul]
  calc
    ‖torusScalarRepresentative U q‖ * ‖sourceCutoffBarGradient m q‖ ≤
      ‖torusScalarRepresentative U q‖ * (((m : ℝ) + 1)⁻¹ * C) :=
      mul_le_mul_of_nonneg_left
        (sourceCutoffBarGradient_norm_le hC m q) (norm_nonneg _)
    _ = _ := by ring
theorem angularSourceFreeScalarCutoffGradient_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (m : ℕ) :
    MemLp (angularSourceFreeScalarCutoffGradient U m) 2
      (angularWeightedTorusMeasure a) := by
  obtain ⟨C, _, hC⟩ := unitBump_euclideanGradient_bound (n := n)
  apply hu.of_le_mul (c := ((m : ℝ) + 1)⁻¹ * C)
    (continuous_angularSourceFreeScalarCutoffGradient
      hU hperiod m).aestronglyMeasurable
  filter_upwards [] with q
  exact angularSourceFreeScalarCutoffGradient_norm_le U hC m q
def angularSourceFreeInverseRootGradientField
    {n : ℕ} (a : LogTorus n → ℝ)
    (U : LogSpace n → ℂ) (q : LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanLin
    ((angularMatrixSquareRoot
      (angularTorusComplexHessianMatrix a) q)⁻¹)
    (angularEuclideanConjugation
      (torusFunctionBarPartialRepresentative U q))
def angularSourceFreeInverseRootGradientL2
    {n : ℕ} {a : LogTorus n → ℝ}
    {U : LogSpace n → ℂ}
    (hr : MemLp (angularSourceFreeInverseRootGradientField a U)
      2 (angularWeightedTorusMeasure a)) :
    angularWeightedFormL2 a :=
  hr.toLp (angularSourceFreeInverseRootGradientField a U)
def angularSourceFreeTruncatedGradientL2
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (m : ℕ) : angularWeightedFormL2 a :=
  angularBarPartialL2OfRepresentative a
    (angularSourceFreeScalarRadialGraphTest U m)
    (angularSourceFreeScalarRadialGraphTest_barPartial_memLp
      ha hU hperiod m) -
  (angularSourceFreeScalarCutoffGradient_memLp hU hperiod hu m).toLp
    (angularSourceFreeScalarCutoffGradient U m)
end TorusHomogeneousBrascampLieb
namespace BergmanJetHolomorphicPhysicalSupport
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier
open EnvelopeSmoothing EnvelopeGeneralTorusDescent RadialPartitionBounds MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentWeakBergman BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetSpatialSmoothing
open BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicStrictSchur
open BergmanJetHolomorphicPhysicalMeasure WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution
def momentWeakHolomorphicJointMollifierSupportError
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier) +
    BodyScale.canonicalScale K + 1 +
    BodyScale.canonicalScale K *
      (|sourceJointCoverTime q| + ‖sourceJointRealTimeCLM n‖) +
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) * 2
def momentWeakHolomorphicJointTimeSupportError
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) (t : ℝ) : ℝ :=
  Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier) +
    BodyScale.canonicalScale K + 1 +
    BodyScale.canonicalScale K *
      (|t| + ‖sourceJointRealTimeCLM n‖) +
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) * 2
end BergmanJetHolomorphicPhysicalSupport
namespace BergmanJetJointHolomorphicTimeDerivativeBounds
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation BergmanJetEnvelopePlurisubharmonic
open BergmanJetUpperEnvelope BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative
open JetEnvelopeTrueRadialMollifier EnvelopeSmoothing EnvelopeGeneralTorusDescent
open RadialAccelerationBounds
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder
local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (LogSpace n)) (volume : Measure ℂ)
def momentWeakJointRealTimeShift (n : ℕ) (h : ℝ) :
    SourceJointComplexCover n :=
  ((0 : LogSpace n), (h / 2 : ℂ))
@[simp] theorem sourceJointCoverTime_add_momentWeakJointRealTimeShift
    {n : ℕ} (q : SourceJointComplexCover n) (h : ℝ) :
    sourceJointCoverTime
      (q + momentWeakJointRealTimeShift n h) =
        sourceJointCoverTime q + h := by
  simp [sourceJointCoverTime,
    momentWeakJointRealTimeShift, Complex.add_re]
  ring
end BergmanJetJointHolomorphicTimeDerivativeBounds
namespace BergmanJetHolomorphicPhysicalLogConvexity
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative LogPartitionConvexity
open JointHolomorphicLaurentFourierCompatibility EnvelopeSmoothing EnvelopeGeneralTorusDescent
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation WeightedTorusDolbeault
open WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph RadialSchurBlock TorusDeckGraphAdjoint
open RadialPhysicalInverseSquareRootEnergy MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicFullLeviSchur
open BergmanJetHolomorphicPhysicalMeasure BergmanJetHolomorphicPhysicalSupport
open BergmanJetJointHolomorphicPhysicalApproximation BergmanJetJointHolomorphicTimeDerivativeBounds
open TorusHomogeneousBrascampLieb
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff
def momentWeakHolomorphicStrictJointPhysicalMixedCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (z : LogSpace n) : ℂ :=
  (jointSourceCoverVelocity
    (momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k)
    (z, (t / 2 : ℂ)) : ℂ)
theorem contDiff_momentWeakHolomorphicStrictJointPhysicalMixedCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    ContDiff ℝ 3
      (momentWeakHolomorphicStrictJointPhysicalMixedCover
        K F htransport p ε k t) := by
  let G : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k
  have hG : ContDiff ℝ 4 G :=
    (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 4
  have hv : ContDiff ℝ 3 (jointSourceCoverVelocity G) := by
    unfold jointSourceCoverVelocity
    exact (hG.fderiv_right (m := 3) (by norm_num)).clm_apply
      contDiff_const
  exact Complex.ofRealCLM.contDiff.comp
    (hv.comp (contDiff_id.prodMk contDiff_const))
theorem momentWeakHolomorphicStrictJointPhysicalMixedCover_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (d : Fin n → ℤ) :
    Function.Periodic
      (momentWeakHolomorphicStrictJointPhysicalMixedCover
        K F htransport p ε k t)
      (imaginaryShift d) := by
  intro z
  change
    (jointSourceCoverVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (z + imaginaryShift d, (t / 2 : ℂ)) : ℂ) =
    (jointSourceCoverVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (z, (t / 2 : ℂ)) : ℂ)
  have h := jointSourceCoverVelocity_spatial_periodic
    (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
      K F htransport p ε k) d (z, (t / 2 : ℂ))
  simpa only [Prod.mk_add_mk, add_zero] using
    congrArg Complex.ofReal h
def momentWeakHolomorphicStrictJointPhysicalCenteredCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (z : LogSpace n) : ℂ :=
  momentWeakHolomorphicStrictJointPhysicalMixedCover
    K F htransport p ε k t z -
  (sourceProbabilityMean
    (momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k) t
    (jointSourceTorusVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t) : ℂ)
theorem contDiff_momentWeakHolomorphicStrictJointPhysicalCenteredCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    ContDiff ℝ 3
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t) := by
  exact
    (contDiff_momentWeakHolomorphicStrictJointPhysicalMixedCover
      K F htransport p ε k t).sub contDiff_const
theorem momentWeakHolomorphicStrictJointPhysicalCenteredCover_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (d : Fin n → ℤ) :
    Function.Periodic
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t)
      (imaginaryShift d) := by
  intro z
  unfold momentWeakHolomorphicStrictJointPhysicalCenteredCover
  rw [momentWeakHolomorphicStrictJointPhysicalMixedCover_periodic
    K F htransport p ε k t d z]
def momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) : ℂ :=
  ((jointSourceTorusVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t q -
    sourceProbabilityMean
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t) : ℝ) : ℂ)
def momentWeakHolomorphicStrictJointPhysicalMixedRow
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) : Fin n → ℂ :=
  fun i => sourceTorusBarPartial
    (momentWeakHolomorphicStrictJointPhysicalMixedCover
      K F htransport p ε k t) i q
theorem momentWeakHolomorphicStrictJointPhysicalMixedRow_eq_cover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    momentWeakHolomorphicStrictJointPhysicalMixedRow
      K F htransport p ε k t q =
    sourceJointCoverAntiholomorphicVelocityGradient
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (t / 2 : ℂ) (sourceTorusCoverPoint q) := by
  funext i
  rfl
theorem torusFunctionBarPartialRepresentative_momentWeakHolomorphicStrictJointPhysicalCenteredCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    torusFunctionBarPartialRepresentative
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t) q =
      WithLp.toLp 2
        (momentWeakHolomorphicStrictJointPhysicalMixedRow
          K F htransport p ε k t q) := by
  ext i
  change
    coverRepresentative
      (fun z => barPartialCoordinate
        (momentWeakHolomorphicStrictJointPhysicalCenteredCover
          K F htransport p ε k t) z i) q.1 q.2 =
    coverRepresentative
      (fun z => barPartialCoordinate
        (momentWeakHolomorphicStrictJointPhysicalMixedCover
          K F htransport p ε k t) z i) q.1 q.2
  congr 1
  funext z
  unfold momentWeakHolomorphicStrictJointPhysicalCenteredCover
  rw [barPartial_sub
    ((contDiff_momentWeakHolomorphicStrictJointPhysicalMixedCover
      K F htransport p ε k t).of_le (by norm_num))
    contDiff_const z i]
  simp [barPartialCoordinate]
def momentWeakHolomorphicStrictJointPhysicalRowEnergy
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) : ℝ :=
  sourceComplexRowSchurEnergyDensity
    (angularTorusComplexHessianMatrix
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t) q)
    (momentWeakHolomorphicStrictJointPhysicalMixedRow
      K F htransport p ε k t q)
theorem momentWeakHolomorphicStrictJointPhysicalRowEnergy_le_acceleration
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    momentWeakHolomorphicStrictJointPhysicalRowEnergy
      K F htransport p ε k t q ≤
    jointSourceTorusAcceleration
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t q := by
  unfold momentWeakHolomorphicStrictJointPhysicalRowEnergy
  rw [angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_eq,
    momentWeakHolomorphicStrictJointPhysicalMixedRow_eq_cover,
    jointSourceTorusAcceleration_eq_cover]
  exact momentWeakHolomorphicStrictJointCover_rowSchurEnergy_le_acceleration
    K F htransport p ε hε₀ hε₁ k (t / 2 : ℂ)
      (sourceTorusCoverPoint q)
theorem continuous_momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    Continuous
      (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
        K F htransport p ε k t) := by
  exact Complex.continuous_ofReal.comp
    ((continuous_jointSourceTorusVelocity
      ((contDiff_infty.mp
        (contDiff_momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k)) 2)
      (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
        K F htransport p ε k) t).sub continuous_const)
theorem momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ)
    {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    MemLp
      (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
        K F htransport p ε k t) 2
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) := by
  let : IsFiniteMeasure
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) :=
    momentWeakHolomorphicStrictJointWeightedMeasure_isFinite
      K F htransport p k t hε₀ hε₁
  apply MemLp.of_bound
    (continuous_momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
      K F htransport p ε k t).aestronglyMeasurable
    (B + |sourceProbabilityMean
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t)|)
  filter_upwards [] with q
  unfold momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_sub _ _).trans (add_le_add (hB q) (le_refl _))
theorem continuous_angularSourceFreeInverseRootGradientField
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {U : LogSpace n → ℂ}
    (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ,
      Function.Periodic U (imaginaryShift d)) :
    Continuous (angularSourceFreeInverseRootGradientField a U) := by
  have hroot := continuous_angularMatrixSquareRoot_inverse
    (continuous_angularTorusComplexHessianMatrix ha2) hH
  have hrow := continuous_torusFunctionBarPartialRepresentative_of_periodic
    (hU.of_le (by norm_num)) hperiod
  change Continuous
    (fun q : LogTorus n =>
      WithLp.toLp 2 (fun i : Fin n =>
        ∑ j : Fin n,
          ((angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)⁻¹) i j *
            conj (torusFunctionBarPartialRepresentative U q j)))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact (hroot.matrix_elem i j).mul
    (Complex.continuous_conj.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp hrow))
theorem momentWeakHolomorphicStrictJointPhysicalRowEnergy_eq_inverseRoot_norm_sq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    momentWeakHolomorphicStrictJointPhysicalRowEnergy
      K F htransport p ε k t q =
    ‖angularSourceFreeInverseRootGradientField
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t)
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t) q‖ ^ 2 := by
  unfold momentWeakHolomorphicStrictJointPhysicalRowEnergy
  rw [sourceComplexRowSchurEnergyDensity_eq_inverseSquareRoot_norm_sq
    (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
      K F htransport p ε hε₀ hε₁ k t q)]
  unfold angularSourceFreeInverseRootGradientField
  rw [torusFunctionBarPartialRepresentative_momentWeakHolomorphicStrictJointPhysicalCenteredCover
    K F htransport p ε k t q]
  rfl
theorem momentWeakHolomorphicStrictJointPhysicalInverseRoot_angular_memLp
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ)
    {J : ℝ}
    (hJ : ∀ q : LogTorus n,
      |jointSourceTorusAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ J) :
    MemLp
      (angularSourceFreeInverseRootGradientField
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)
        (momentWeakHolomorphicStrictJointPhysicalCenteredCover
          K F htransport p ε k t)) 2
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) := by
  let a : LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t
  let U : LogSpace n → ℂ :=
    momentWeakHolomorphicStrictJointPhysicalCenteredCover
      K F htransport p ε k t
  let : IsFiniteMeasure (angularWeightedTorusMeasure a) :=
    momentWeakHolomorphicStrictJointWeightedMeasure_isFinite
      K F htransport p k t hε₀ hε₁
  have hcontinuous :
      Continuous (angularSourceFreeInverseRootGradientField a U) :=
    continuous_angularSourceFreeInverseRootGradientField
      ((contDiff_infty.mp
        (contDiff_angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) 2)
      (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
        K F htransport p ε hε₀ hε₁ k t)
      (contDiff_momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t)
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover_periodic
        K F htransport p ε k t)
  apply MemLp.of_bound hcontinuous.aestronglyMeasurable (Real.sqrt |J|)
  filter_upwards [] with q
  apply (sq_le_sq₀ (norm_nonneg _)
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (abs_nonneg J)]
  rw [← momentWeakHolomorphicStrictJointPhysicalRowEnergy_eq_inverseRoot_norm_sq
    K F htransport p ε hε₀ hε₁ k t q]
  exact (momentWeakHolomorphicStrictJointPhysicalRowEnergy_le_acceleration
    K F htransport p ε hε₀ hε₁ k t q).trans
      ((le_abs_self _).trans ((hJ q).trans (le_abs_self J)))
end BergmanJetHolomorphicPhysicalLogConvexity
namespace BergmanJetJointHolomorphicConvexTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open MomentRegularity BergmanJetTorusEnvelope BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicPhysicalApproximation
open JetEnvelopeSlopeConvergence LogPartitionConvexity
open scoped BigOperators ENNReal Topology
end BergmanJetJointHolomorphicConvexTransfer
namespace BergmanJetJointHolomorphicUnconditionalBodyConvexity
open Set Function Filter
open TorusCharacters BergmanJetPartitionEndpoint BergmanJetHolomorphicPhysicalLogConvexity
open BergmanJetJointHolomorphicConvexTransfer
open scoped Topology
end BergmanJetJointHolomorphicUnconditionalBodyConvexity
namespace BergmanJetLocalGrowth
open Set Function Filter MeasureTheory Module Metric Asymptotics
open BergmanMonomials BergmanDiagonalBasisIndependence GlobalBergmanKernelBound AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetBasis MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge
open BergmanJetRealGeodesic JetEnvelopeLocalGrowth LaurentJetMultiplicityBridge
open scoped BigOperators Topology ENNReal InnerProductSpace
def momentLocalCoverPotential {n : ℕ}
    (K : CenteredBody n) (F : SourceFiniteEnergyPotential K)
    (z : TorusCharacters.LogSpace n) : ℝ :=
  momentNormalizedPotential F (realLogCoordinate z)
def momentLocalPotentialMaximum {n : ℕ}
    (K : CenteredBody n) (F : SourceFiniteEnergyPotential K)
    (p : TorusCharacters.LogSpace n) (R : ℝ) : ℝ :=
  sSup (momentLocalCoverPotential K F '' Metric.closedBall p R)
end BergmanJetLocalGrowth
namespace BergmanJetLocalEnvelopeGrowth
open Set Function Filter MeasureTheory Module Metric
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetLocalGrowth ActualJetUpperEnvelope
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative JetEnvelopeLocalGrowth
open LogPartitionConvexity
open scoped BigOperators ENNReal Topology
def momentBodyLocalPartitionGrowthConstant
    {n : ℕ} (K : CenteredBody n) (R : ℝ) : ℝ :=
  momentLocalPotentialMaximum K
      (momentBodyOptimizer K) (0 : LogSpace n) R -
    Real.log (sourceLocalBallVolumeConstant n R) +
    Real.log (normalizedVolume K.carrier)
end BergmanJetLocalEnvelopeGrowth
namespace BergmanJetBodyLogPartitionSharpGrowth
open Set Filter
open TorusCharacters BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicUnconditionalBodyConvexity BergmanJetLocalEnvelopeGrowth
open scoped Topology
end BergmanJetBodyLogPartitionSharpGrowth
namespace BergmanJetBodyExponentialSecantBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open BergmanJetPartitionEndpoint BergmanJetTorusRightSlopeGibbsBridge
open BergmanJetBodyLogPartitionSharpGrowth
open scoped BigOperators ENNReal Topology
def momentBodyEnvelopeRelativeDensity
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (q : LogTorus n) : ℝ :=
  Real.exp
    (-(momentBodyTorusWeight K p t q -
      momentBodyTorusWeight K p 0 q))
end BergmanJetBodyExponentialSecantBridge
namespace BergmanJetPortmanteauActualUpperTailBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge JetEnvelopeRightDerivative EnvelopeSpatialPeriodicity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation BergmanJetUpperEnvelope
open BergmanJetSpatialPeriodicity BergmanJetPortmanteauSlopeBridge
open scoped BigOperators ENNReal NNReal Topology
def momentTorusTailUpperEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  momentJointTailUpperEnvelope K F htransport p r
    (sourcePositiveJointTimePoint (sourceTorusCoverPoint q) t ht)
end BergmanJetPortmanteauActualUpperTailBridge
namespace BergmanJetGlobalLogKernelEquiLipschitz
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics BergmanMonomials LatticeAsymptotics LaurentJetSeparatedness
open GlobalBergmanKernelBound MomentMinimizer MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation MomentRegularity BergmanJetBasis MomentWeakGlobalKernel
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal NNReal Topology
end BergmanJetGlobalLogKernelEquiLipschitz
namespace BergmanJetTorusSlopeJointNeighborhoodUpper
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert BergmanMonomials JetEnvelopeRightDerivative
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge BergmanJetGlobalLogKernelEquiLipschitz
open BergmanJetPortmanteauActualUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology
def momentTorusTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  (momentTorusTailUpperEnvelopeTimeSlice
      K F htransport p r t ht q -
    momentNormalizedPotential F q.1) / t
def momentTorusClampedTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  max 0 (momentTorusTailPositiveSecant
    K F htransport p r t ht q)
end BergmanJetTorusSlopeJointNeighborhoodUpper
namespace BergmanJetPortmanteauActualVolumeBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative LogPartitionConvexity
open MomentRegularity BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge BergmanJetTorusRightSlopeBridge
open BergmanJetTorusRightSlopeGibbsBridge BergmanJetBodyExponentialSecantBridge
open BergmanJetPortmanteauMovingUpperTailBridge BergmanJetPortmanteauActualUpperTailBridge
open BergmanJetTorusSlopeJointNeighborhoodUpper
open scoped BigOperators ENNReal NNReal Topology
def momentBodyMovingBergmanProbability
    {n : ℕ} (K : CenteredBody n) (k : ℕ) :
    ProbabilityMeasure (LogTorus n) :=
  ⟨momentTorusBergmanProbability
      K (momentBodyOptimizer K) (k + 1),
    momentTorusBergmanProbability_isProbability
      K (Nat.zero_lt_succ k) (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)⟩
def momentBodyZeroGibbsProbability
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) : ProbabilityMeasure (LogTorus n) :=
  ⟨sourceProbability (momentBodyTorusWeight K p) 0,
    sourceProbability_momentBody_isProbability K p 0⟩
def momentBodyTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  (momentTorusTailUpperEnvelopeTimeSlice
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p r t ht q -
    momentNormalizedPotential (momentBodyOptimizer K) q.1) / t
def momentBodyClampedTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  max 0 (momentBodyTailPositiveSecant K p r t ht q)
end BergmanJetPortmanteauActualVolumeBridge
namespace MomentWeakBergmanProbabilityEndpoint
open Set Function Filter MeasureTheory
open BergmanMonomials BergmanNormalization LatticeAsymptotics MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman MomentWeakGlobalKernel
open scoped BigOperators ENNReal Topology
theorem normalizedMonomialDensity_momentNormalized_integrable
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    Integrable
      (normalizedMonomialDensity K k (momentNormalizedPotential F) u)
      (volume : Measure (Space n)) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  exact
    (integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport u.property.1 hkreal).div_const _
theorem integral_normalizedMonomialDensity_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    (∫ x : Space n,
      normalizedMonomialDensity
        K k (momentNormalizedPotential F) u x
        ∂(volume : Measure (Space n))) = 1 := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  unfold normalizedMonomialDensity
  rw [MeasureTheory.integral_div]
  change
    monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) /
      monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) = 1
  apply div_self
  exact
    (monomialIntegral_momentNormalized_pos
      F htransport u.property.1 hkreal).ne'
theorem weightedDiagonalKernel_momentNormalized_integrable
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Integrable
      (weightedDiagonalKernel K k (momentNormalizedPotential F))
      (volume : Measure (Space n)) := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel
  simp_rw [tsum_fintype]
  exact integrable_finsetSum Finset.univ
    (fun u _ => normalizedMonomialDensity_momentNormalized_integrable
      K hk F htransport u)
theorem integral_weightedDiagonalKernel_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    (∫ x : Space n,
      weightedDiagonalKernel K k (momentNormalizedPotential F) x
        ∂(volume : Measure (Space n))) =
      (bergmanDimension K k : ℝ) := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel
  simp_rw [tsum_fintype]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [integral_normalizedMonomialDensity_momentNormalized
      K hk F htransport]
    simp [bergmanDimension, Nat.card_eq_fintype_card]
  · intro u _
    exact normalizedMonomialDensity_momentNormalized_integrable
      K hk F htransport u
theorem normalizedDiagonalDensity_momentNormalized_integrable
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Integrable
      (normalizedDiagonalDensity K k (momentNormalizedPotential F))
      (volume : Measure (Space n)) := by
  exact
    (weightedDiagonalKernel_momentNormalized_integrable
      K hk F htransport).div_const _
theorem normalizedDiagonalDensity_momentNormalized_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    0 < normalizedDiagonalDensity
      K k (momentNormalizedPotential F) x := by
  unfold normalizedDiagonalDensity
  exact div_pos
    (weightedDiagonalKernel_momentNormalized_pos
      K hk F htransport x)
    (by exact_mod_cast bergmanDimension_pos K hk)
theorem integral_normalizedDiagonalDensity_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    (∫ x : Space n,
      normalizedDiagonalDensity K k
        (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) = 1 := by
  unfold normalizedDiagonalDensity
  rw [MeasureTheory.integral_div,
    integral_weightedDiagonalKernel_momentNormalized
      K hk F htransport]
  apply div_self
  exact_mod_cast (bergmanDimension_pos K hk).ne'
theorem normalizedBergmanMeasure_momentNormalized_univ
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    normalizedBergmanMeasure
      K k (momentNormalizedPotential F) Set.univ = 1 := by
  unfold normalizedBergmanMeasure
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (normalizedDiagonalDensity_momentNormalized_integrable
      K hk F htransport)
    (Filter.Eventually.of_forall fun x =>
      (normalizedDiagonalDensity_momentNormalized_pos
        K hk F htransport x).le),
    integral_normalizedDiagonalDensity_momentNormalized
      K hk F htransport]
  exact ENNReal.ofReal_one
theorem normalizedBergmanMeasure_momentNormalized_isProbability
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    IsProbabilityMeasure
      (normalizedBergmanMeasure
        K k (momentNormalizedPotential F)) :=
  ⟨normalizedBergmanMeasure_momentNormalized_univ
    K hk F htransport⟩
end MomentWeakBergmanProbabilityEndpoint
namespace BergmanJetBergmanProbabilityTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanMonomials BergmanNormalization
open JetEnvelopeSlopeConvergence LogPartitionConvexity MomentOptimizer MomentWeakFirstVariation
open MomentRegularity MomentWeakBergman MomentWeakBergmanProbabilityEndpoint
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open scoped BigOperators ENNReal Topology
def momentWeakTorusBergmanDensity {n : ℕ}
    (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (k : ℕ) (q : LogTorus n) : ℝ :=
  normalizedDiagonalDensity K k (momentNormalizedPotential F) q.1
def momentWeakTorusGibbsDensity {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (q : LogTorus n) : ℝ :=
  WeightedPoincare.normalizedDensity F.potential q.1
def momentWeakTorusGibbsProbability {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : Measure (LogTorus n) :=
  (finiteEnergySourceGibbsProbability F).prod (angularMeasure n)
end BergmanJetBergmanProbabilityTransfer
namespace BergmanJetRadialHaarWeakProbabilityLift
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanNormalization LogPartitionConvexity MomentOptimizer
open MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakBergman MomentWeakBergmanProbabilityEndpoint BergmanJetPartitionEndpoint
open BergmanJetTorusSlopeBridge BergmanJetBergmanProbabilityTransfer
open BergmanJetPortmanteauActualVolumeBridge
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
def momentMovingRadialBergmanProbability
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (k : ℕ) : ProbabilityMeasure (Space n) :=
  ⟨normalizedBergmanMeasure
      K (k + 1) (momentNormalizedPotential F),
    normalizedBergmanMeasure_momentNormalized_isProbability
      K (Nat.zero_lt_succ k) F htransport⟩
def momentRadialGibbsProbability
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    ProbabilityMeasure (Space n) :=
  ⟨finiteEnergySourceGibbsProbability F,
    finiteEnergySourceGibbsProbability_isProbability F⟩
def momentNormalizedAngularHaarProbability (n : ℕ) :
    ProbabilityMeasure (AngularTorus n) :=
  ⟨angularMeasure n, angularMeasure_isProbability n⟩
end BergmanJetRadialHaarWeakProbabilityLift
namespace BergmanJetDualGradientConcentration
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentInteriorLegendre
open scoped ENNReal NNReal Topology
end BergmanJetDualGradientConcentration
namespace BergmanJetDualPhaseConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentInteriorLegendre
open scoped BigOperators ENNReal NNReal Topology
end BergmanJetDualPhaseConcentration
namespace BergmanJetMovingPhaseConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetPhaseLaplace
open BergmanJetDualPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology
end BergmanJetMovingPhaseConcentration
namespace BergmanJetMovingMonomialConcentration
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open MomentRegularity MomentWeakBergman BergmanJetMovingPhaseConcentration
open scoped BigOperators ENNReal NNReal Topology
end BergmanJetMovingMonomialConcentration
namespace BergmanJetMovingMonomialProbability
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ENNReal NNReal Topology
end BergmanJetMovingMonomialProbability
namespace BergmanJetMovingMonomialTailConvergence
open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetPointwiseLogKernel
open BergmanJetMovingPhaseConcentration BergmanJetMovingMonomialConcentration
open BergmanJetMovingMonomialProbability
open scoped BigOperators ENNReal NNReal Topology
end BergmanJetMovingMonomialTailConvergence
namespace BergmanJetMovingMonomialObservableConvergence
open Set Function Filter MeasureTheory Metric
open LaplaceAsymptotics MonomialIntegrability MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetMovingMonomialTailConvergence
open scoped BigOperators ENNReal NNReal Topology
end BergmanJetMovingMonomialObservableConvergence
namespace BergmanJetTriangularLatticeConvergence
open Set Filter MeasureTheory Metric
open LatticeAsymptotics
open scoped BigOperators ENNReal NNReal Topology
def triangularUnitLatticeStep {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) (x : Space n) : ℝ :=
  ∑ J ∈ (BoxIntegral.unitPartition.prepartition (k + 1) B).boxes,
    (J : Set (Space n)).indicator
      (fun _ : Space n =>
        s.indicator (G (k + 1))
          ((BoxIntegral.unitPartition.prepartition (k + 1) B).tag J)) x
end BergmanJetTriangularLatticeConvergence
namespace BergmanJetDualGradientInverseTransport
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentWeakFirstVariation MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetDualGradientConcentration
open BergmanJetDualPhaseConcentration
open scoped ENNReal NNReal Topology
end BergmanJetDualGradientInverseTransport
namespace BergmanJetRoundedMonomialObservableConvergence
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open BergmanJetPhaseLaplace BergmanJetDualPhaseConcentration
open scoped ENNReal NNReal Topology
end BergmanJetRoundedMonomialObservableConvergence
namespace BergmanJetDiagonalObservableLatticeIdentity
open Set Function Filter MeasureTheory
open BergmanMonomials BergmanNormalization LatticeAsymptotics MonomialIntegrability MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergmanProbabilityEndpoint
open scoped BigOperators ENNReal NNReal Topology
def momentNormalizedLaurentObservable
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (k : ℕ)
    (f : Space n → ℝ)
    (u : Space n) : ℝ :=
  (∫ x : Space n,
    f x * monomialWeight (k : ℝ) u
      (momentNormalizedPotential F) x
    ∂(volume : Measure (Space n))) /
    monomialIntegral (k : ℝ) u
      (momentNormalizedPotential F)
end BergmanJetDiagonalObservableLatticeIdentity
namespace BergmanJetUpperTaggedMonomialObservableConvergence
open Set Function Filter MeasureTheory
open LaplaceAsymptotics LatticeAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetDualGradientConcentration BergmanJetMovingMonomialObservableConvergence
open BergmanJetRoundedMonomialObservableConvergence BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity
open scoped BigOperators ENNReal NNReal Topology
def upperTaggedLatticeExponent {n : ℕ}
    (k : ℕ) (u : Space n) : Space n :=
  fun i => (⌈(k : ℝ) * u i⌉ : ℝ) / (k : ℝ)
def momentTaggedLaurentObservable
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (k : ℕ)
    (f : Space n → ℝ)
    (u : Space n) : ℝ := by
  classical
  exact
    if hk : 0 < k then
      if hu : u ∈ scaledIntegerLattice n k then
        momentNormalizedLaurentObservable F k f u
      else 0
    else 0
end BergmanJetUpperTaggedMonomialObservableConvergence
namespace Volume
open Set Function Filter MeasureTheory
open TorusCharacters LatticeAsymptotics BergmanMonomials BergmanNormalization LaplaceAsymptotics
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentRegularity BergmanJetPartitionEndpoint BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity BergmanJetDualGradientInverseTransport
open BergmanJetUpperTaggedMonomialObservableConvergence BergmanJetPortmanteauActualVolumeBridge
open BergmanJetRadialHaarWeakProbabilityLift
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
end Volume
end Ehrhart
end


