-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
-- name    : GroundTheory_AutomorphicForms_MeasuresChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:49.202222+00:00
-- url     : https://prove2.me/theorems/1f3c137d-0554-4ff2-ae32-b1b6a32688e8
-- title:
--   Measures Chart
-- statement:
--   Definitions and structural lemmas for Measures Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresChart.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Theorems.Thm_GroundTheory_Automorphic_exists_compactOpenSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
namespace Measures
structure LinearChart (F : Type*) [Field F] [TopologicalSpace F] (ι : Type*) (G : Type*) [Mul G]
    [TopologicalSpace G] where

  toFun : G → ι → F
  isOpenEmbedding : IsOpenEmbedding toFun

  left : G → ((ι → F) ≃ₗ[F] (ι → F))

  right : G → ((ι → F) ≃ₗ[F] (ι → F))
  toFun_mul_left : ∀ g x, toFun (g * x) = left g (toFun x)
  toFun_mul_right : ∀ h x, toFun (x * h) = right h (toFun x)
namespace LinearChart
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {ι : Type*} [Fintype ι]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] (C : LinearChart F ι G)
noncomputable def leftModulus (g : G) : ℝ≥0 := distribHaarChar (ι → F) (C.left g)
noncomputable def rightModulus (h : G) : ℝ≥0 := distribHaarChar (ι → F) (C.right h)
theorem leftModulus_pos (g : G) : 0 < C.leftModulus g := distribHaarChar_pos
theorem rightModulus_pos (h : G) : 0 < C.rightModulus h := distribHaarChar_pos
theorem measurableEmbedding : MeasurableEmbedding C.toFun :=
  C.isOpenEmbedding.measurableEmbedding
theorem image_preimage_mul_left (g : G) (s : Set G) :
    C.toFun '' ((g * ·) ⁻¹' s) = (C.left g)⁻¹ • (C.toFun '' s) := by
  rw [← Set.preimage_smul]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨g * x, hx, (C.toFun_mul_left g x).trans rfl⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨g⁻¹ * z, by simpa using hz, ?_⟩
    apply (C.left g).injective
    rw [← C.toFun_mul_left, mul_inv_cancel_left, hzy]
    rfl
theorem image_preimage_mul_right (h : G) (s : Set G) :
    C.toFun '' ((· * h) ⁻¹' s) = (C.right h)⁻¹ • (C.toFun '' s) := by
  rw [← Set.preimage_smul]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x * h, hx, (C.toFun_mul_right h x).trans rfl⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z * h⁻¹, by simpa using hz, ?_⟩
    apply (C.right h).injective
    rw [← C.toFun_mul_right, inv_mul_cancel_right, hzy]
    rfl
variable (μ₀ : Measure (ι → F)) [μ₀.IsAddHaarMeasure]
theorem map_mul_left_comap (g : G) :
    map (g * ·) (μ₀.comap C.toFun) = (C.leftModulus g)⁻¹ • μ₀.comap C.toFun := by
  ext s hs
  rw [map_apply (continuous_const_mul g).measurable hs, C.measurableEmbedding.comap_apply,
    Measure.smul_apply, C.measurableEmbedding.comap_apply, image_preimage_mul_left,
    ← distribHaarChar_mul, map_inv, ENNReal.smul_def, smul_eq_mul]
  rfl
theorem map_mul_right_comap (h : G) :
    map (· * h) (μ₀.comap C.toFun) = (C.rightModulus h)⁻¹ • μ₀.comap C.toFun := by
  ext s hs
  rw [map_apply (continuous_mul_const h).measurable hs, C.measurableEmbedding.comap_apply,
    Measure.smul_apply, C.measurableEmbedding.comap_apply, image_preimage_mul_right,
    ← distribHaarChar_mul, map_inv, ENNReal.smul_def, smul_eq_mul]
  rfl
theorem comap_lt_top_of_isCompact {K : Set G} (hK : IsCompact K) : μ₀.comap C.toFun K < ∞ := by
  rw [C.measurableEmbedding.comap_apply]
  exact (hK.image C.isOpenEmbedding.continuous).measure_lt_top
theorem comap_pos_of_isOpen {U : Set G} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < μ₀.comap C.toFun U := by
  rw [C.measurableEmbedding.comap_apply]
  exact (C.isOpenEmbedding.isOpenMap U hU).measure_pos μ₀ (hne.image _)
variable [LocallyCompactSpace G]
theorem eq_of_smul_comap_eq {a b : ℝ≥0} (h : a • μ₀.comap C.toFun = b • μ₀.comap C.toFun) :
    a = b := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : 0 < μ₀.comap C.toFun K :=
    (C.comap_pos_of_isOpen μ₀ isOpen_interior ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).trans_le
      (measure_mono interior_subset)
  have h' := congrArg (fun ν : Measure G => ν K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h'
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj hpos.ne'
    (C.comap_lt_top_of_isCompact μ₀ hK).ne).1 h')
theorem leftModulus_mul (g h : G) : C.leftModulus (g * h) = C.leftModulus g * C.leftModulus h := by
  let μ₀ : Measure (ι → F) := addHaar
  have e1 := C.map_mul_left_comap μ₀ (g * h)
  have e2 : map ((g * h) * ·) (μ₀.comap C.toFun) =
      map (g * ·) (map (h * ·) (μ₀.comap C.toFun)) := by
    rw [map_map (continuous_const_mul g).measurable (continuous_const_mul h).measurable]
    congr 1
    funext x
    simp [mul_assoc]
  rw [e2, C.map_mul_left_comap μ₀ h, Measure.map_smul, C.map_mul_left_comap μ₀ g, smul_smul]
    at e1
  have := C.eq_of_smul_comap_eq μ₀ e1
  rw [← mul_inv] at this
  rw [mul_comm]
  exact inv_injective this.symm
theorem rightModulus_mul (g h : G) :
    C.rightModulus (g * h) = C.rightModulus g * C.rightModulus h := by
  let μ₀ : Measure (ι → F) := addHaar
  have e1 := C.map_mul_right_comap μ₀ (g * h)
  have e2 : map (· * (g * h)) (μ₀.comap C.toFun) =
      map (· * h) (map (· * g) (μ₀.comap C.toFun)) := by
    rw [map_map (continuous_mul_const h).measurable (continuous_mul_const g).measurable]
    congr 1
    funext x
    simp [mul_assoc]
  rw [e2, C.map_mul_right_comap μ₀ g, Measure.map_smul, C.map_mul_right_comap μ₀ h, smul_smul]
    at e1
  have := C.eq_of_smul_comap_eq μ₀ e1
  rw [← mul_inv] at this
  exact inv_injective this.symm
noncomputable def leftModulusHom : G →* ℝ≥0 where
  toFun := C.leftModulus
  map_one' := by
    have h := C.leftModulus_mul 1 1
    rw [one_mul] at h
    exact ((mul_eq_left₀ (C.leftModulus_pos 1).ne').1 h.symm)
  map_mul' := C.leftModulus_mul
noncomputable def rightModulusHom : G →* ℝ≥0 where
  toFun := C.rightModulus
  map_one' := by
    have h := C.rightModulus_mul 1 1
    rw [one_mul] at h
    exact ((mul_eq_left₀ (C.rightModulus_pos 1).ne').1 h.symm)
  map_mul' := C.rightModulus_mul
@[simp] theorem leftModulusHom_apply (g : G) : C.leftModulusHom g = C.leftModulus g := rfl
@[simp] theorem rightModulusHom_apply (g : G) : C.rightModulusHom g = C.rightModulus g := rfl
theorem leftModulus_eq_one_of_preimage {g : G} {s : Set G} (hs : MeasurableSet s)
    (hgs : (g * ·) ⁻¹' s = s) (h0 : μ₀.comap C.toFun s ≠ 0) (hT : μ₀.comap C.toFun s ≠ ∞) :
    C.leftModulus g = 1 := by
  have e := congrArg (fun ν : Measure G => ν s) (C.map_mul_left_comap μ₀ g)
  simp only [map_apply (continuous_const_mul g).measurable hs, hgs, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul] at e
  have : ((C.leftModulus g)⁻¹ : ℝ≥0) = 1 := by
    have := (ENNReal.mul_eq_right h0 hT).1 e.symm
    exact_mod_cast this
  exact inv_eq_one.1 this
theorem rightModulus_eq_one_of_preimage {h : G} {s : Set G} (hs : MeasurableSet s)
    (hhs : (· * h) ⁻¹' s = s) (h0 : μ₀.comap C.toFun s ≠ 0) (hT : μ₀.comap C.toFun s ≠ ∞) :
    C.rightModulus h = 1 := by
  have e := congrArg (fun ν : Measure G => ν s) (C.map_mul_right_comap μ₀ h)
  simp only [map_apply (continuous_mul_const h).measurable hs, hhs, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul] at e
  have : ((C.rightModulus h)⁻¹ : ℝ≥0) = 1 := by
    have := (ENNReal.mul_eq_right h0 hT).1 e.symm
    exact_mod_cast this
  exact inv_eq_one.1 this
theorem modulus_eq_one_of_mem {V : OpenSubgroup G} (hV : IsCompact (V : Set G)) {v : G}
    (hv : v ∈ V) : C.leftModulus v = 1 ∧ C.rightModulus v = 1 := by
  let μ₀ : Measure (ι → F) := addHaar
  have h0 : μ₀.comap C.toFun V ≠ 0 :=
    (C.comap_pos_of_isOpen μ₀ V.isOpen ⟨1, V.one_mem⟩).ne'
  have hT : μ₀.comap C.toFun V ≠ ∞ := (C.comap_lt_top_of_isCompact μ₀ hV).ne
  refine ⟨C.leftModulus_eq_one_of_preimage μ₀ V.isOpen.measurableSet ?_ h0 hT,
    C.rightModulus_eq_one_of_preimage μ₀ V.isOpen.measurableSet ?_ h0 hT⟩
  · ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact (V : Subgroup G).mul_mem_cancel_left hv
  · ext x
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact (V : Subgroup G).mul_mem_cancel_right hv
theorem continuous_of_eq_one_on_openSubgroup (χ : G →* ℝ≥0) (V : OpenSubgroup G)
    (hV : ∀ v ∈ V, χ v = 1) : Continuous χ := by
  refine IsLocallyConstant.continuous fun s => isOpen_iff_forall_mem_open.2 fun g hg =>
    ⟨g • (V : Set G), ?_, V.isOpen.smul g, ⟨1, V.one_mem, mul_one g⟩⟩
  rintro _ ⟨v, hv, rfl⟩
  simp only [Set.mem_preimage, smul_eq_mul, map_mul, hV v hv, mul_one]
  exact hg
variable [T2Space G] [TotallyDisconnectedSpace G]
theorem continuous_leftModulus : Continuous C.leftModulus := by
  obtain ⟨V, hV⟩ := exists_compactOpenSubgroup (G := G)
  exact continuous_of_eq_one_on_openSubgroup C.leftModulusHom V fun v hv =>
    (C.modulus_eq_one_of_mem hV hv).1
theorem continuous_density : Continuous fun g : G => (C.leftModulus g)⁻¹ :=
  C.continuous_leftModulus.inv₀ fun g => (C.leftModulus_pos g).ne'
theorem measurable_density : Measurable fun g : G => (((C.leftModulus g)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp C.continuous_density).measurable
noncomputable def haar : Measure G :=
  (μ₀.comap C.toFun).withDensity fun g => (((C.leftModulus g)⁻¹ : ℝ≥0) : ℝ≥0∞)
theorem map_withDensity_of_scale {X : Type*} [MeasurableSpace X] {T : X → X} (hT : Measurable T)
    {ν : Measure X} {ρ : X → ℝ≥0∞} (hρ : Measurable ρ) {a b : ℝ≥0} (hν : map T ν = a • ν)
    (hρT : ∀ x, ρ x = b * ρ (T x)) : map T (ν.withDensity ρ) = (a * b) • ν.withDensity ρ := by
  ext s hs
  rw [map_apply hT hs, withDensity_apply _ (hT hs), Measure.smul_apply, withDensity_apply _ hs,
    ← lintegral_indicator (hT hs), ← lintegral_indicator hs]
  have h1 : (T ⁻¹' s).indicator ρ = fun x => (b : ℝ≥0∞) * s.indicator ρ (T x) := by
    funext x
    by_cases hx : T x ∈ s
    · rw [indicator_of_mem (show x ∈ T ⁻¹' s from hx), indicator_of_mem hx, hρT]
    · rw [indicator_of_notMem (show x ∉ T ⁻¹' s from hx), indicator_of_notMem hx, mul_zero]
  rw [h1]
  show ∫⁻ x, (b : ℝ≥0∞) * s.indicator ρ (T x) ∂ν = _
  rw [lintegral_const_mul (f := fun x => s.indicator ρ (T x)) _ ((hρ.indicator hs).comp hT),
    ← lintegral_map (hρ.indicator hs) hT, hν, lintegral_smul_measure, ENNReal.smul_def,
    smul_eq_mul, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_mul]
  ring
instance isMulLeftInvariant_haar : (C.haar μ₀).IsMulLeftInvariant := ⟨fun g => by
  rw [haar, map_withDensity_of_scale (continuous_const_mul g).measurable C.measurable_density
    (C.map_mul_left_comap μ₀ g) (b := C.leftModulus g) fun x => ?_,
    inv_mul_cancel₀ (C.leftModulus_pos g).ne', one_smul]
  rw [← ENNReal.coe_mul, ENNReal.coe_inj, C.leftModulus_mul, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (C.leftModulus_pos g).ne', one_mul]⟩
instance isHaarMeasure_haar : (C.haar μ₀).IsHaarMeasure where
  lt_top_of_isCompact := fun K hK => by
    rw [haar, withDensity_apply _ hK.isClosed.measurableSet]
    exact setLIntegral_lt_top_of_isCompact (C.comap_lt_top_of_isCompact μ₀ hK).ne hK
      C.continuous_density
  map_mul_left_eq_self := (C.isMulLeftInvariant_haar μ₀).map_mul_left_eq_self
  open_pos := fun U hU hne => by
    rw [haar, ne_eq, withDensity_apply_eq_zero' C.measurable_density.aemeasurable]
    have e : {g | (((C.leftModulus g)⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0} ∩ U = U :=
      Set.inter_eq_right.2 fun g _ => by
        simpa using (C.leftModulus_pos g).ne'
    rw [e]
    exact (C.comap_pos_of_isOpen μ₀ hU hne).ne'
end LinearChart
end Measures
end GroundTheory.Automorphic


