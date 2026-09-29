-- Prove2me | solution 1 for AutomorphicForm.StandardKernel.exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0be80243-d4ed-5ea0-b6b2-174d7ada0fec

import Definitions.Def_AutomorphicForm_SmoothingKernel
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv.AutomorphicForm"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "StandardKernel.realCoord"
namespace StandardKernel
p2m_export "AutomorphicForm.StandardKernel" "realCoord realCoord_apply ofReal continuous_ofReal ofReal_realCoord"
namespace HaarRealCoord
p2m_open "AutomorphicForm.StandardKernel AutomorphicForm"

p2m_open "MeasureTheory Set Topology AutomorphicForm.StandardKernel P2MW.S_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv.AutomorphicForm.StandardKernel"

theorem ofReal_mul (r s : ℝ) : ofReal (r * s) = ofReal r * ofReal s := by
  funext v
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm (r * s) =
    ofReal r v * ofReal s v
  rw [map_mul]
  rfl

theorem ofReal_one : ofReal 1 = 1 := by
  funext v
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm 1 = 1
  rw [map_one]

theorem realCoord_ofReal (r : ℝ) : realCoord (ofReal r) = r := by
  rw [realCoord_apply]
  show InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).symm r) = r
  exact (InfinitePlace.Completion.ringEquivRealOfIsReal _).apply_symm_apply r

def unitOfReal (y : ℝ) (hy : y ≠ 0) : (InfiniteAdeleRing ℚ)ˣ where
  val := ofReal y
  inv := ofReal y⁻¹
  val_inv := by rw [← ofReal_mul, mul_inv_cancel₀ hy, ofReal_one]
  inv_val := by rw [← ofReal_mul, inv_mul_cancel₀ hy, ofReal_one]

theorem unitOfReal_realCoord (z : (InfiniteAdeleRing ℚ)ˣ) :
    unitOfReal (realCoord (z : InfiniteAdeleRing ℚ)) ((z.isUnit.map realCoord).ne_zero) = z :=
  Units.ext (ofReal_realCoord _)

def unitOfReal' (y : ℝ) : (InfiniteAdeleRing ℚ)ˣ :=
  if hy : y = 0 then 1 else unitOfReal y hy

theorem unitOfReal'_of_ne {y : ℝ} (hy : y ≠ 0) : unitOfReal' y = unitOfReal y hy := by
  simp [unitOfReal', hy]

theorem coe_unitOfReal'_of_ne {y : ℝ} (hy : y ≠ 0) :
    ((unitOfReal' y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = ofReal y := by
  rw [unitOfReal'_of_ne hy]; rfl

theorem unitOfReal'_realCoord (z : (InfiniteAdeleRing ℚ)ˣ) :
    unitOfReal' (realCoord (z : InfiniteAdeleRing ℚ)) = z := by
  rw [unitOfReal'_of_ne ((z.isUnit.map realCoord).ne_zero)]
  exact Units.ext (ofReal_realCoord _)

theorem unitOfReal'_one : unitOfReal' 1 = 1 := by
  rw [unitOfReal'_of_ne one_ne_zero]
  exact Units.ext ofReal_one

theorem ofReal_neg (r : ℝ) : ofReal (-r) = -ofReal r := by
  funext v
  show (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm (-r) = -ofReal r v
  rw [map_neg]
  rfl

theorem coe_unitOfReal'_neg_one : ((unitOfReal' (-1) : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = -1 := by
  rw [coe_unitOfReal'_of_ne (by norm_num), ofReal_neg, ofReal_one]

theorem continuousOn_unitOfReal' : ContinuousOn unitOfReal' ({0}ᶜ : Set ℝ) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (({0}ᶜ : Set ℝ).domRestrict unitOfReal') = fun y : ({0}ᶜ : Set ℝ) => unitOfReal (y : ℝ) y.2 := by
    funext y
    exact unitOfReal'_of_ne y.2
  rw [heq, Units.continuous_iff]
  constructor
  · show Continuous fun y : ({0}ᶜ : Set ℝ) => ofReal (y : ℝ)
    exact continuous_ofReal.comp continuous_subtype_val
  · show Continuous fun y : ({0}ᶜ : Set ℝ) => ofReal ((y : ℝ)⁻¹)
    exact continuous_ofReal.comp (continuous_subtype_val.inv₀ fun y => y.2)

theorem continuous_realCoord : Continuous (realCoord : InfiniteAdeleRing ℚ → ℝ) :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

abbrev T (z : (InfiniteAdeleRing ℚ)ˣ) : ℝ := realCoord (z : InfiniteAdeleRing ℚ)

theorem continuous_T : Continuous T := continuous_realCoord.comp Units.continuous_val

theorem T_ne_zero (z : (InfiniteAdeleRing ℚ)ˣ) : T z ≠ 0 := (z.isUnit.map realCoord).ne_zero

theorem T_mul (u z : (InfiniteAdeleRing ℚ)ˣ) : T (u * z) = T u * T z := by
  show realCoord ((u : InfiniteAdeleRing ℚ) * z) = _
  rw [map_mul]

theorem T_unitOfReal' {y : ℝ} (hy : y ≠ 0) : T (unitOfReal' y) = y := by
  show realCoord ((unitOfReal' y : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = y
  rw [coe_unitOfReal'_of_ne hy, realCoord_ofReal]

theorem preimage_T_eq_image {K : Set ℝ} (hK : K ⊆ ({0}ᶜ : Set ℝ)) : T ⁻¹' K = unitOfReal' '' K := by
  ext z
  constructor
  · intro hz
    exact ⟨T z, hz, unitOfReal'_realCoord z⟩
  · rintro ⟨y, hy, rfl⟩
    show T (unitOfReal' y) ∈ K
    rw [T_unitOfReal' (fun h => hK hy h)]
    exact hy

section Measure

variable [MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
  (ν : Measure (InfiniteAdeleRing ℚ)ˣ) [ν.IsHaarMeasure]

theorem measurable_T : Measurable T := continuous_T.measurable

abbrev m : Measure ℝ := Measure.map T ν

theorem m_apply {A : Set ℝ} (hA : MeasurableSet A) : m ν A = ν (T ⁻¹' A) := Measure.map_apply (measurable_T) hA

theorem m_lt_top_of_isCompact {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ ({0}ᶜ : Set ℝ)) : m ν K < ⊤ := by
  rw [m_apply ν hK.isClosed.measurableSet, preimage_T_eq_image hK0]
  exact (hK.image_of_continuousOn (continuousOn_unitOfReal'.mono hK0)).measure_lt_top

theorem map_mul_left_m {c : ℝ} (hc : c ≠ 0) : Measure.map (fun y => c * y) (m ν) = m ν := by
  rw [Measure.map_map (measurable_const_mul c) (measurable_T)]
  have h : ((fun y => c * y) ∘ T) = T ∘ fun z => unitOfReal' c * z := by
    funext z
    show c * T z = T (unitOfReal' c * z)
    rw [T_mul, T_unitOfReal' hc]
  rw [h, ← Measure.map_map (measurable_T) (measurable_const_mul _),
    Measure.IsMulLeftInvariant.map_mul_left_eq_self]

theorem m_Ioi_ne_zero : m ν (Ioi 0) ≠ 0 := by
  rw [m_apply ν measurableSet_Ioi]
  refine (Measure.IsOpenPosMeasure.open_pos _ (continuous_T.isOpen_preimage _ isOpen_Ioi) ⟨1, ?_⟩)
  show (0 : ℝ) < T 1
  rw [show T 1 = 1 from by simp [T, map_one]]
  exact one_pos

abbrev mlog : Measure ℝ := Measure.map Real.log ((m ν).restrict (Ioi 0))

theorem map_mul_left_restrict_Ioi {c : ℝ} (hc : 0 < c) :
    Measure.map (fun y => c * y) ((m ν).restrict (Ioi 0)) = (m ν).restrict (Ioi 0) := by
  have hpre : (fun y => c * y) ⁻¹' (Ioi (0 : ℝ)) = Ioi 0 := by
    ext y; simp [mul_pos_iff_of_pos_left hc]
  rw [← hpre, ← Measure.restrict_map (measurable_const_mul c) measurableSet_Ioi, hpre, map_mul_left_m ν hc.ne']

theorem isAddLeftInvariant_mlog : (mlog ν).IsAddLeftInvariant := by
  refine ⟨fun t => ?_⟩
  show Measure.map (fun x => t + x) (Measure.map Real.log ((m ν).restrict (Ioi 0))) = mlog ν
  rw [Measure.map_map (measurable_const_add t) Real.measurable_log]
  have hae : ((fun x => t + x) ∘ Real.log) =ᶠ[ae ((m ν).restrict (Ioi 0))] (Real.log ∘ fun y => Real.exp t * y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    show t + Real.log y = Real.log (Real.exp t * y)
    rw [Real.log_mul (Real.exp_pos t).ne' (ne_of_gt hy), Real.log_exp]
  rw [Measure.map_congr hae, ← Measure.map_map Real.measurable_log (measurable_const_mul _),
    map_mul_left_restrict_Ioi ν (Real.exp_pos t)]

theorem isFiniteMeasureOnCompacts_mlog : IsFiniteMeasureOnCompacts (mlog ν) := by
  refine ⟨fun K hK => ?_⟩
  show (Measure.map Real.log ((m ν).restrict (Ioi 0))) K < ⊤
  rw [Measure.map_apply Real.measurable_log hK.isClosed.measurableSet,
    Measure.restrict_apply' measurableSet_Ioi]
  have hset : Real.log ⁻¹' K ∩ Ioi 0 = Real.exp '' K := by
    ext y
    constructor
    · rintro ⟨hy, hy0⟩
      exact ⟨Real.log y, hy, Real.exp_log hy0⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by simpa using ht, Real.exp_pos t⟩
  rw [hset]
  exact m_lt_top_of_isCompact ν (hK.image Real.continuous_exp) (by
    rintro y ⟨t, -, rfl⟩; exact (Real.exp_pos t).ne')

theorem restrict_Ioi_eq_map_exp_mlog : (m ν).restrict (Ioi 0) = Measure.map Real.exp (mlog ν) := by
  show (m ν).restrict (Ioi 0) = Measure.map Real.exp (Measure.map Real.log ((m ν).restrict (Ioi 0)))
  rw [Measure.map_map Real.measurable_exp Real.measurable_log]
  have hae : (Real.exp ∘ Real.log) =ᶠ[ae ((m ν).restrict (Ioi 0))] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact Real.exp_log hy
  rw [Measure.map_congr hae, Measure.map_id]

abbrev D : Measure ℝ := (volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹

theorem map_exp_volume : Measure.map Real.exp (volume : Measure ℝ) = D.restrict (Ioi 0) := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply Real.measurable_exp hA, Measure.restrict_apply hA]
  set s : Set ℝ := A ∩ Ioi 0 with hs
  have hsm : MeasurableSet s := hA.inter measurableSet_Ioi
  have hpre : Real.exp ⁻¹' A = Real.log '' s := by
    ext t
    constructor
    · intro ht
      exact ⟨Real.exp t, ⟨ht, Real.exp_pos t⟩, Real.log_exp t⟩
    · rintro ⟨y, ⟨hyA, hy0⟩, rfl⟩
      show Real.exp (Real.log y) ∈ A
      rwa [Real.exp_log hy0]
  have hderiv : ∀ x ∈ s, HasDerivWithinAt Real.log (x⁻¹) s x := fun x hx =>
    (Real.hasDerivAt_log (ne_of_gt hx.2)).hasDerivWithinAt
  have hinj : InjOn Real.log s := Real.log_injOn_pos.mono (fun x hx => hx.2)
  have h := lintegral_image_eq_lintegral_abs_deriv_mul hsm hderiv hinj (fun _ => 1)
  simp only [mul_one, setLIntegral_one] at h
  rw [hpre, h, withDensity_apply _ hsm]
  refine setLIntegral_congr_fun hsm (fun x hx => ?_)
  rw [abs_inv]

theorem map_neg_restrict_Ioi_D : Measure.map Neg.neg (D.restrict (Ioi 0)) = D.restrict (Iio 0) := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply measurable_neg hA, Measure.restrict_apply (measurable_neg hA), Measure.restrict_apply hA]
  set s : Set ℝ := A ∩ Iio 0 with hs
  have hsm : MeasurableSet s := hA.inter measurableSet_Iio
  have himg : Neg.neg ⁻¹' A ∩ Ioi 0 = Neg.neg '' s := by
    ext y
    constructor
    · rintro ⟨hy, hy0⟩
      exact ⟨-y, ⟨hy, by simpa using hy0⟩, neg_neg y⟩
    · rintro ⟨x, ⟨hxA, hx0⟩, rfl⟩
      exact ⟨by simpa using hxA, by simpa using hx0⟩
  have hderiv : ∀ x ∈ s, HasDerivWithinAt Neg.neg (-1 : ℝ) s x := fun x _ =>
    (hasDerivAt_neg x).hasDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_deriv_mul hsm hderiv neg_injective.injOn
    (fun y => ENNReal.ofReal |y|⁻¹)
  have hsm' : MeasurableSet (Neg.neg '' s) := by
    rw [← himg]; exact (measurable_neg hA).inter measurableSet_Ioi
  rw [himg, withDensity_apply _ hsm', withDensity_apply _ hsm, h]
  refine setLIntegral_congr_fun hsm (fun x _ => ?_)
  simp [abs_neg]

theorem map_neg_restrict_Ioi_m : Measure.map Neg.neg ((m ν).restrict (Ioi 0)) = (m ν).restrict (Iio 0) := by
  have hneg : Measure.map Neg.neg (m ν) = m ν := by
    have h := map_mul_left_m ν (neg_ne_zero.mpr one_ne_zero : (-1 : ℝ) ≠ 0)
    rwa [show (fun y : ℝ => -1 * y) = Neg.neg from funext fun y => neg_one_mul y] at h
  have hpre : Neg.neg ⁻¹' (Iio (0 : ℝ)) = Ioi 0 := by ext y; simp
  rw [← hpre, ← Measure.restrict_map measurable_neg measurableSet_Iio, hneg]

omit [BorelSpace (InfiniteAdeleRing ℚ)ˣ] [ν.IsHaarMeasure] in

theorem measure_eq_three (μ : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    μ A = μ.restrict (Ioi 0) A + μ.restrict (Iio 0) A + μ (A ∩ {0}) := by
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  have huniv : A = (A ∩ Ioi 0 ∪ A ∩ Iio 0) ∪ A ∩ {0} := by
    ext y
    simp only [mem_union, mem_inter_iff, mem_Ioi, mem_Iio, mem_singleton_iff]
    rcases lt_trichotomy y 0 with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h]
  have hd1 : Disjoint (A ∩ Ioi 0) (A ∩ Iio 0) :=
    Set.disjoint_left.mpr fun y hy hy' => (lt_asymm (Set.mem_Ioi.mp hy.2) (Set.mem_Iio.mp hy'.2)).elim
  have hd2 : Disjoint (A ∩ Ioi 0 ∪ A ∩ Iio 0) (A ∩ {0}) := by
    refine Set.disjoint_left.mpr ?_
    rintro y (hy | hy) ⟨-, (h0 : y = 0)⟩
    · exact (lt_irrefl (0 : ℝ)) (h0 ▸ hy.2)
    · exact (lt_irrefl (0 : ℝ)) (h0 ▸ hy.2)
  conv_lhs => rw [huniv]
  rw [measure_union hd2 (hA.inter (measurableSet_singleton 0)),
    measure_union hd1 (hA.inter measurableSet_Iio)]

theorem exists_pos_map_eq : ∃ κ : ℝ, 0 < κ ∧ m ν = ENNReal.ofReal κ • D := by
  haveI := isAddLeftInvariant_mlog ν
  haveI := isFiniteMeasureOnCompacts_mlog ν
  set κ : NNReal := (mlog ν).addHaarScalarFactor volume with hκ
  have hmlog : mlog ν = κ • (volume : Measure ℝ) := Measure.isAddLeftInvariant_eq_smul _ _

  have hpos : (m ν).restrict (Ioi 0) = κ • D.restrict (Ioi 0) := by
    rw [restrict_Ioi_eq_map_exp_mlog ν, hmlog, Measure.map_smul, map_exp_volume]

  have hnegray : (m ν).restrict (Iio 0) = κ • D.restrict (Iio 0) := by
    rw [← map_neg_restrict_Ioi_m ν, hpos, Measure.map_smul, map_neg_restrict_Ioi_D]

  have hκ0 : κ ≠ 0 := by
    intro h0
    have h1 : (m ν).restrict (Ioi 0) (Ioi 0) = 0 := by rw [hpos, h0]; simp
    rw [Measure.restrict_apply_self] at h1
    exact m_Ioi_ne_zero ν h1
  refine ⟨(κ : ℝ), by exact_mod_cast (pos_iff_ne_zero.mpr hκ0), ?_⟩
  rw [ENNReal.ofReal_coe_nnreal]

  have hm0 : m ν {0} = 0 := by
    rw [m_apply ν (measurableSet_singleton 0)]
    have : T ⁻¹' ({0} : Set ℝ) = ∅ := by
      ext z; simpa using T_ne_zero z
    rw [this, measure_empty]
  have hD0 : D {0} = 0 := by
    show ((volume : Measure ℝ).withDensity fun y => ENNReal.ofReal |y|⁻¹) {0} = 0
    rw [withDensity_apply _ (measurableSet_singleton 0)]
    exact setLIntegral_measure_zero _ _ Real.volume_singleton

  refine Measure.ext fun A hA => ?_
  rw [measure_eq_three (m ν) hA, measure_eq_three ((κ : ENNReal) • D) hA, hpos, hnegray,
    Measure.restrict_smul, Measure.restrict_smul,
    measure_mono_null inter_subset_right hm0]
  have : ((κ : ENNReal) • D) (A ∩ {0}) = 0 := by
    rw [Measure.smul_apply, measure_mono_null inter_subset_right hD0, smul_zero]
  rw [this]
  rfl

end Measure

end AutomorphicForm.StandardKernel.HaarRealCoord

end

open AutomorphicForm.StandardKernel.HaarRealCoord in
theorem solution
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure] :
    ∃ κ : ℝ, 0 < κ ∧
      MeasureTheory.Measure.map
          (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
        ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
          fun y => ENNReal.ofReal |y|⁻¹ :=
  exists_pos_map_eq ν_mul

end S_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv
end P2MW
export P2MW.S_AutomorphicForm_StandardKernel_exists_pos_map_realCoord_eq_smul_volume_withDensity_abs_inv (solution)
