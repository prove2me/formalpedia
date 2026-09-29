-- Prove2me | solution 1 for AutomorphicForm.lintegral_mul_density_eq_tsum_torusShells_localGL2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0f6813fe-1132-546d-9525-98ab75c78561

import Mathlib
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Theorems.Thm_HaarQuotient_lintegral_eq_lintegral_lintegral_mul_out
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_LocalGL2_iwasawa_decomposition_diag
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace HaarQuotient
p2m_export "HaarQuotient" "weight density measure lintegral_eq_lintegral_lintegral_mul_out lintegral_density_mul_eq_one"
namespace CellMajorantLoc
p2m_open "HaarQuotient"

section Algebra

variable {G : Type*} [Group G] {H : Subgroup G}

theorem apply_out_mk {α : Type*} {f : G → α} (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (g : G) :
    f (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = f g := by
  have h : (MulAction.orbitRel H G) (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out g :=
    Quotient.exact (Quotient.out_eq _)
  obtain ⟨x, hx⟩ := MulAction.orbitRel_apply.1 h
  rw [← hx]
  exact hfH x x.2 g

theorem apply_coe_mul {α : Type*} {f : G → α} (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g)
    (x : H) (g : G) : f ((x : G) * g) = f g :=
  hfH x x.2 g

end Algebra

section Measurability

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

theorem measurable_weight [BorelSpace G] (H : Subgroup G) (μH : Measure H) :
    Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · exact Measurable.tsum fun n =>
      (measurable_const.mul measurable_const).mul
        (measurable_const.indicator isOpen_interior.measurableSet)
  · exact measurable_const

theorem measurable_density [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] :
    Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

omit [TopologicalSpace G] in

theorem measurable_comp_out {α : Type*} [MeasurableSpace α] {H : Subgroup G} {f : G → α}
    (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => f q.out := by
  refine measurable_from_quotient.2 ?_
  have : (fun q : MulAction.orbitRel.Quotient H G => f q.out) ∘ Quotient.mk'' = f :=
    funext fun g => apply_out_mk hfH g
  rw [this]
  exact hf

end Measurability

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [BorelSpace G] in

theorem sFinite_of_isClosed (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
    [μH.IsHaarMeasure] : SFinite μH := by
  haveI : SigmaCompactSpace H := hH.sigmaCompactSpace
  infer_instance

noncomputable def cellDensity {ι : Type*} (A : ι → Set G) (c : ι → ℝ≥0∞) (g : G) : ℝ≥0∞ :=
  ∑' i, c i * (A i).indicator (fun _ => (1 : ℝ≥0∞)) g

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in
theorem measurable_cellDensity {ι : Type*} [Countable ι] (A : ι → Set G)
    (hA : ∀ i, MeasurableSet (A i)) (c : ι → ℝ≥0∞) : Measurable (cellDensity A c) :=
  Measurable.tsum fun i => measurable_const.mul (measurable_const.indicator (hA i))

omit [LocallyCompactSpace G] [SecondCountableTopology G] in

theorem lintegral_cellDensity_mul {ι : Type*} [Countable ι] (H : Subgroup G) (μH : Measure H)
    (A : ι → Set G) (hA : ∀ i, MeasurableSet (A i)) (c : ι → ℝ≥0∞) (g : G) :
    ∫⁻ x : H, cellDensity A c ((x : G) * g) ∂μH = ∑' i, c i * μH {x : H | (x : G) * g ∈ A i} := by
  have hmeas : ∀ i, MeasurableSet {x : H | (x : G) * g ∈ A i} := fun i =>
    (hA i).preimage (continuous_subtype_val.mul continuous_const).measurable
  have hind : ∀ i (x : H), (A i).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) =
      ({x : H | (x : G) * g ∈ A i}).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro i x
    by_cases hx : (x : G) * g ∈ A i
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : H | (x : G) * g ∈ A i} from hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (show x ∉ {x : H | (x : G) * g ∈ A i} from hx)]
  unfold cellDensity
  rw [lintegral_tsum fun i => ?_]
  · refine tsum_congr fun i => ?_
    rw [lintegral_const_mul _ ?_]
    · simp_rw [hind i]
      rw [show (fun x : H => ({x : H | (x : G) * g ∈ A i}).indicator (fun _ => (1 : ℝ≥0∞)) x) =
          ({x : H | (x : G) * g ∈ A i}).indicator 1 from rfl, lintegral_indicator_one (hmeas i)]
    · simp_rw [hind i]
      exact measurable_const.indicator (hmeas i)
  · exact (measurable_const.mul ((measurable_const.indicator (hA i)).comp
      (continuous_subtype_val.mul continuous_const).measurable)).aemeasurable

omit [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [BorelSpace G] in

theorem tsum_mul_setLIntegral_eq_lintegral_mul_cellDensity {ι : Type*} [Countable ι] (μ : Measure G)
    (A : ι → Set G) (hA : ∀ i, MeasurableSet (A i)) (c : ι → ℝ≥0∞) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∑' i, c i * ∫⁻ g in A i, f g ∂μ = ∫⁻ g, f g * cellDensity A c g ∂μ := by
  have hind : ∀ i g, (A i).indicator f g = f g * (A i).indicator (fun _ => (1 : ℝ≥0∞)) g := by
    intro i g
    by_cases hg : g ∈ A i
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, mul_one]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero]
  calc ∑' i, c i * ∫⁻ g in A i, f g ∂μ
      = ∑' i, ∫⁻ g, c i * (A i).indicator f g ∂μ := by
        refine tsum_congr fun i => ?_
        rw [← lintegral_indicator (hA i), lintegral_const_mul _ (hf.indicator (hA i))]
    _ = ∫⁻ g, ∑' i, c i * (A i).indicator f g ∂μ := by
        rw [lintegral_tsum fun i => (measurable_const.fun_mul (hf.indicator (hA i))).aemeasurable]
    _ = ∫⁻ g, f g * cellDensity A c g ∂μ := by
        refine lintegral_congr fun g => ?_
        unfold cellDensity
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun i => ?_
        rw [hind i g]
        ring

theorem lintegral_mul_density_eq_lintegral_out (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g, f g * HaarQuotient.density H μH g ∂μ =
      ∫⁻ q, f q.out ∂(HaarQuotient.measure μ H μH) := by
  haveI := sFinite_of_isClosed H hH μH
  have hD := measurable_density H μH
  rw [HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH _ (hf.fun_mul hD)]
  refine lintegral_congr fun q => ?_
  have h1 : ∀ x : H, f ((x : G) * q.out) * HaarQuotient.density H μH ((x : G) * q.out) =
      f q.out * HaarQuotient.density H μH ((x : G) * q.out) := fun x => by
    rw [apply_coe_mul hfH]
  simp_rw [h1]
  have hm : Measurable fun x : H => HaarQuotient.density H μH ((x : G) * q.out) :=
    hD.comp (continuous_subtype_val.mul continuous_const).measurable
  rw [lintegral_const_mul _ hm, HaarQuotient.lintegral_density_mul_eq_one H hH μH, mul_one]

theorem lintegral_mul_cellDensity_eq_lintegral_out {ι : Type*} [Countable ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (A : ι → Set G) (hA : ∀ i, MeasurableSet (A i)) (c : ι → ℝ≥0∞)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g, f g * cellDensity A c g ∂μ =
      ∫⁻ q, f q.out * ∑' i, c i * μH {x : H | (x : G) * q.out ∈ A i} ∂(HaarQuotient.measure μ H μH) := by
  have hρ := measurable_cellDensity A hA c
  rw [HaarQuotient.lintegral_eq_lintegral_lintegral_mul_out μ H hH μH _ (hf.fun_mul hρ)]
  refine lintegral_congr fun q => ?_
  have h1 : ∀ x : H, f ((x : G) * q.out) * cellDensity A c ((x : G) * q.out) =
      f q.out * cellDensity A c ((x : G) * q.out) := fun x => by
    rw [apply_coe_mul hfH]
  simp_rw [h1]
  have hm : Measurable fun x : H => cellDensity A c ((x : G) * q.out) :=
    hρ.comp (continuous_subtype_val.mul continuous_const).measurable
  rw [lintegral_const_mul _ hm, lintegral_cellDensity_mul H μH A hA c]

theorem lintegral_mul_density_eq_tsum_mul_setLIntegral_of_tsum_eq_one {ι : Type*} [Countable ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (A : ι → Set G) (hA : ∀ i, MeasurableSet (A i)) (c : ι → ℝ≥0∞)
    (hcov : ∀ g : G, ∑' i, c i * μH {x : H | (x : G) * g ∈ A i} = 1)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g, f g * HaarQuotient.density H μH g ∂μ = ∑' i, c i * ∫⁻ g in A i, f g ∂μ := by
  rw [lintegral_mul_density_eq_lintegral_out μ H hH μH f hf hfH,
    tsum_mul_setLIntegral_eq_lintegral_mul_cellDensity μ A hA c f hf,
    lintegral_mul_cellDensity_eq_lintegral_out μ H hH μH A hA c f hf hfH]
  refine lintegral_congr fun q => ?_
  rw [hcov, mul_one]

theorem lintegral_mul_density_le_tsum_mul_setLIntegral_of_one_le_tsum {ι : Type*} [Countable ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (A : ι → Set G) (hA : ∀ i, MeasurableSet (A i)) (c : ι → ℝ≥0∞)
    (hcov : ∀ g : G, 1 ≤ ∑' i, c i * μH {x : H | (x : G) * g ∈ A i})
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g, f g * HaarQuotient.density H μH g ∂μ ≤ ∑' i, c i * ∫⁻ g in A i, f g ∂μ := by
  rw [lintegral_mul_density_eq_lintegral_out μ H hH μH f hf hfH,
    tsum_mul_setLIntegral_eq_lintegral_mul_cellDensity μ A hA c f hf,
    lintegral_mul_cellDensity_eq_lintegral_out μ H hH μH A hA c f hf hfH]
  refine lintegral_mono fun q => ?_
  calc f q.out = f q.out * 1 := (mul_one _).symm
    _ ≤ f q.out * ∑' i, c i * μH {x : H | (x : G) * q.out ∈ A i} := by gcongr; exact hcov _

theorem integrable_withDensity_density_of_norm_le {ι : Type*} [Countable ι]
    {E : Type*} [NormedAddCommGroup E]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (A : ι → Set G) (hA : ∀ i, MeasurableSet (A i)) (c : ι → ℝ≥0∞)
    (hcov : ∀ g : G, 1 ≤ ∑' i, c i * μH {x : H | (x : G) * g ∈ A i})
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hΦH : ∀ x ∈ H, ∀ g : G, Φ (x * g) = Φ g)
    (hfin : ∑' i, c i * ∫⁻ g in A i, Φ g ∂μ ≠ ∞)
    (F : G → E) (hFm : AEStronglyMeasurable F μ) (hFΦ : ∀ g, (‖F g‖₊ : ℝ≥0∞) ≤ Φ g) :
    Integrable F (μ.withDensity (HaarQuotient.density H μH)) := by
  haveI := sFinite_of_isClosed H hH μH
  have hD := measurable_density H μH
  refine ⟨hFm.mono_ac (withDensity_absolutelyContinuous μ _), ?_⟩
  rw [HasFiniteIntegral, lintegral_withDensity_eq_lintegral_mul₀ hD.aemeasurable hFm.enorm]
  calc ∫⁻ g, (HaarQuotient.density H μH * fun g => ‖F g‖ₑ) g ∂μ
      ≤ ∫⁻ g, Φ g * HaarQuotient.density H μH g ∂μ := by
        refine lintegral_mono fun g => ?_
        rw [Pi.mul_apply, mul_comm]
        gcongr
        exact hFΦ g
    _ ≤ ∑' i, c i * ∫⁻ g in A i, Φ g ∂μ :=
        lintegral_mul_density_le_tsum_mul_setLIntegral_of_one_le_tsum μ H hH μH A hA c hcov Φ hΦ hΦH
    _ < ∞ := lt_top_iff_ne_top.mpr hfin

def shellCell (K₀ : Subgroup G) (a : G) : Set G := {g : G | a⁻¹ * g ∈ K₀}

def shellSlice (H K₀ : Subgroup G) (a : G) : Set H := {x : H | a⁻¹ * (x : G) * a ∈ K₀}

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem measurableSet_shellCell (K₀ : Subgroup G) (hK : MeasurableSet (K₀ : Set G)) (a : G) :
    MeasurableSet (shellCell K₀ a) :=
  hK.preimage (continuous_const.mul continuous_id).measurable

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem measurableSet_shellSlice (H K₀ : Subgroup G) (hK : MeasurableSet (K₀ : Set G)) (a : G) :
    MeasurableSet (shellSlice H K₀ a) :=
  hK.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in

theorem setOf_mul_mem_shellCell_self (H K₀ : Subgroup G) {ι : Type*} (a : ι → G) (i : ι)
    (x₀ : H) (k : K₀) :
    {x : H | (x : G) * ((x₀ : G) * a i * k) ∈ shellCell K₀ (a i)} =
      (fun x : H => x * x₀) ⁻¹' shellSlice H K₀ (a i) := by
  ext x
  simp only [shellCell, shellSlice, Set.mem_setOf_eq, Set.mem_preimage, Subgroup.coe_mul]
  have hrw : (a i)⁻¹ * ((x : G) * ((x₀ : G) * a i * (k : G))) = (a i)⁻¹ * ((x : G) * (x₀ : G)) * a i * k := by
    group
  rw [hrw]
  constructor
  · intro h
    have := K₀.mul_mem h (K₀.inv_mem k.2)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at this
  · intro h
    exact K₀.mul_mem h k.2

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in

theorem setOf_mul_mem_shellCell_of_ne (H K₀ : Subgroup G) {ι : Type*} (a : ι → G)
    (hU : ∀ (i j : ι) (x : H) (k k' : K₀), (x : G) * a i * k = a j * k' → i = j)
    {i j : ι} (hij : j ≠ i) (x₀ : H) (k : K₀) :
    {x : H | (x : G) * ((x₀ : G) * a i * k) ∈ shellCell K₀ (a j)} = ∅ := by
  ext x
  simp only [shellCell, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  apply hij
  refine (hU i j (x * x₀) k ⟨_, h⟩ ?_).symm
  simp only [Subgroup.coe_mul]
  group

theorem lintegral_mul_density_eq_tsum_of_iwasawa {ι : Type*} [Countable ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (K₀ : Subgroup G) (hK : MeasurableSet (K₀ : Set G)) (a : ι → G)
    (hI : ∀ g : G, ∃ (x : H) (i : ι) (k : K₀), g = (x : G) * a i * k)
    (hU : ∀ (i j : ι) (x : H) (k k' : K₀), (x : G) * a i * k = a j * k' → i = j)
    (h0 : ∀ i, μH (shellSlice H K₀ (a i)) ≠ 0) (htop : ∀ i, μH (shellSlice H K₀ (a i)) ≠ ∞)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g, f g * HaarQuotient.density H μH g ∂μ =
      ∑' i, (μH (shellSlice H K₀ (a i)))⁻¹ * ∫⁻ g in shellCell K₀ (a i), f g ∂μ := by
  classical
  refine lintegral_mul_density_eq_tsum_mul_setLIntegral_of_tsum_eq_one μ H hH μH
    (fun i => shellCell K₀ (a i)) (fun i => measurableSet_shellCell K₀ hK (a i)) _ ?_ f hf hfH
  intro g
  obtain ⟨x₀, i, k, rfl⟩ := hI g
  rw [tsum_eq_single i]
  · rw [setOf_mul_mem_shellCell_self H K₀ a i x₀ k, measure_preimage_mul_right,
      ENNReal.inv_mul_cancel (h0 i) (htop i)]
  · intro j hij
    rw [setOf_mul_mem_shellCell_of_ne H K₀ a hU hij x₀ k, measure_empty, mul_zero]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in

theorem setLIntegral_shellCell (μ : Measure G) [μ.IsMulLeftInvariant]
    (K₀ : Subgroup G) (hK : MeasurableSet (K₀ : Set G)) (a : G) (f : G → ℝ≥0∞) :
    ∫⁻ g in shellCell K₀ a, f g ∂μ = ∫⁻ k in (K₀ : Set G), f (a * k) ∂μ := by
  rw [← lintegral_indicator (measurableSet_shellCell K₀ hK a), ← lintegral_indicator hK,
    ← lintegral_mul_left_eq_self _ a]
  refine lintegral_congr fun g => ?_
  by_cases hg : g ∈ (K₀ : Set G)
  · have : a * g ∈ shellCell K₀ a := by
      simp only [shellCell, Set.mem_setOf_eq, inv_mul_cancel_left]; exact hg
    rw [Set.indicator_of_mem this, Set.indicator_of_mem hg]
  · have : a * g ∉ shellCell K₀ a := by
      simp only [shellCell, Set.mem_setOf_eq, inv_mul_cancel_left]; exact hg
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hg]

theorem lintegral_mul_density_eq_tsum_setLIntegral_translate_of_iwasawa {ι : Type*} [Countable ι]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (K₀ : Subgroup G) (hK : MeasurableSet (K₀ : Set G)) (a : ι → G)
    (hI : ∀ g : G, ∃ (x : H) (i : ι) (k : K₀), g = (x : G) * a i * k)
    (hU : ∀ (i j : ι) (x : H) (k k' : K₀), (x : G) * a i * k = a j * k' → i = j)
    (h0 : ∀ i, μH (shellSlice H K₀ (a i)) ≠ 0) (htop : ∀ i, μH (shellSlice H K₀ (a i)) ≠ ∞)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    ∫⁻ g, f g * HaarQuotient.density H μH g ∂μ =
      ∑' i, (μH (shellSlice H K₀ (a i)))⁻¹ * ∫⁻ k in (K₀ : Set G), f (a i * k) ∂μ := by
  rw [lintegral_mul_density_eq_tsum_of_iwasawa μ H hH μH K₀ hK a hI hU h0 htop f hf hfH]
  refine tsum_congr fun i => ?_
  rw [setLIntegral_shellCell μ K₀ hK (a i) f]

omit [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] in

theorem shellSlice_ne_zero_and_ne_top (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure]
    (K₀ : Subgroup G) (hKo : IsOpen (K₀ : Set G)) (hKc : IsCompact (K₀ : Set G)) (a : G) :
    μH (shellSlice H K₀ a) ≠ 0 ∧ μH (shellSlice H K₀ a) ≠ ∞ := by
  have hcont : Continuous fun x : H => a⁻¹ * (x : G) * a :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  constructor
  · refine (hKo.preimage hcont).measure_ne_zero μH ⟨1, ?_⟩
    simp [K₀.one_mem]
  · refine ne_of_lt (IsCompact.measure_lt_top ?_)

    have hce : Topology.IsClosedEmbedding ((↑) : H → G) := hH.isClosedEmbedding_subtypeVal
    have heq : shellSlice H K₀ a = ((↑) : H → G) ⁻¹' ((fun g : G => a * g * a⁻¹) '' (K₀ : Set G)) := by
      ext x
      simp only [shellSlice, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image, SetLike.mem_coe]
      constructor
      · intro h; exact ⟨_, h, by group⟩
      · rintro ⟨k, hk, hkx⟩
        have : a⁻¹ * (x : G) * a = k := by rw [← hkx]; group
        rw [this]; exact hk
    rw [heq]
    exact hce.isCompact_preimage (hKc.image ((continuous_const.mul continuous_id).mul continuous_const))

end Main

end HaarQuotient.CellMajorantLoc

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace HaarQuotient
p2m_export "HaarQuotient" "weight density measure lintegral_eq_lintegral_lintegral_mul_out lintegral_density_mul_eq_one"
namespace CellMajorantLoc
namespace LocalGL2Iwasawa
p2m_open "HaarQuotient"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "F" => (HeightOneSpectrum.adicCompletion K v)
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers K v)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v))
local notation "Mat" => (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))

abbrev unip : Subgroup G := (unipotentGL2Hom (R := HeightOneSpectrum.adicCompletion K v)).range

abbrev kzero : Subgroup G := AdelicDock.localLevelOne (𝓞 K) K v ⊤

def diagU (a b : (HeightOneSpectrum.adicCompletion K v)ˣ) : G where
  val := !![(a : F), 0; 0, (b : F)]
  inv := !![((a⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F), 0; 0, ((b⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem coe_diagU (a b : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    ((diagU K v a b : G) : Mat) = !![(a : F), 0; 0, (b : F)] := rfl

theorem diagU_inv (a b : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    (diagU K v a b)⁻¹ = diagU K v a⁻¹ b⁻¹ := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  change ((diagU K v a b : G) : Mat) * ((diagU K v a⁻¹ b⁻¹ : G) : Mat) = 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagU_mul (a b a' b' : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    diagU K v a b * diagU K v a' b' = diagU K v (a * a') (b * b') := by
  refine Units.ext ?_
  change ((diagU K v a b : G) : Mat) * ((diagU K v a' b' : G) : Mat) = ((diagU K v (a * a') (b * b') : G) : Mat)
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section Setup

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → HeightOneSpectrum.adicCompletion K v))

scoped instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountableTopology_localGL : SecondCountableTopology G :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem coe_unip_eq :
    ((unip K v : Subgroup G) : Set G) =
      {g : G | (g : Mat) 0 0 = 1 ∧ (g : Mat) 1 0 = 0 ∧ (g : Mat) 1 1 = 1} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, rfl⟩
    simp [unipotentGL2Hom, unipotentGL2_coe]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Mat) 0 1), Units.ext ?_⟩
    change ((unipotentGL2 ((g : Mat) 0 1) : G) : Mat) = (g : Mat)
    rw [unipotentGL2_coe]
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

theorem isClosed_unip : IsClosed ((unip K v : Subgroup G) : Set G) := by
  rw [coe_unip_eq]
  have hc : ∀ i j : Fin 2, Continuous fun g : G => (g : Mat) i j := fun i j =>
    (Units.continuous_val).matrix_elem i j
  exact ((isClosed_singleton.preimage (hc 0 0)).inter
    ((isClosed_singleton.preimage (hc 1 0)).inter (isClosed_singleton.preimage (hc 1 1))))

theorem unip_comm (a b : (unip K v : Subgroup G)) : a * b = b * a := by
  obtain ⟨x, hx⟩ := a.2
  obtain ⟨y, hy⟩ := b.2
  refine Subtype.ext ?_
  change (a : G) * b = b * a
  rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]

theorem isLocalLevelOne_top_of_integral {m : Mat} (h : ∀ i j, m i j ∈ (O)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v ⊤ m := by
  refine ⟨h, ?_, ?_⟩
  · rw [AdelicLevel.idealBound_top]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
  · rw [AdelicLevel.idealBound_top]
    calc Valued.v (m 1 1 - 1) ≤ max (Valued.v (m 1 1)) (Valued.v (1 : F)) := Valuation.map_sub _ _ _
      _ ≤ 1 := max_le ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 1)) (by simp)

theorem mem_kzero_iff (k : G) :
    k ∈ kzero K v ↔ (∀ i j, (k : Mat) i j ∈ (O)) ∧ ∀ i j, ((k⁻¹ : G) : Mat) i j ∈ (O) := by
  rw [AdelicDock.mem_localLevelOne_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.integral, h2.integral⟩
  · rintro ⟨h1, h2⟩
    exact ⟨isLocalLevelOne_top_of_integral K v h1, isLocalLevelOne_top_of_integral K v h2⟩

theorem coe_kzero_eq_localIntegralSet :
    ((kzero K v : Subgroup G) : Set G) = localIntegralSet K v := by
  ext k
  rw [SetLike.mem_coe, mem_kzero_iff, mem_localIntegralSet]

theorem isOpen_kzero : IsOpen ((kzero K v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isOpen_localIntegralSet K v

theorem isCompact_kzero : IsCompact ((kzero K v : Subgroup G) : Set G) := by
  rw [coe_kzero_eq_localIntegralSet]; exact isCompact_localIntegralSet K v

theorem mem_kzero_of_mem_integralSubgroup {k : G}
    (hk : k ∈ LocalGL2.integralSubgroup (HeightOneSpectrum.adicCompletionIntegers K v)
      (HeightOneSpectrum.adicCompletion K v)) : k ∈ kzero K v := by
  have hinj : Function.Injective (algebraMap (O) (F)) := Subtype.val_injective
  rw [FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem hinj] at hk
  rw [mem_kzero_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · obtain ⟨r, hr⟩ := hk.1 i j; rw [← hr]; exact r.2
  · obtain ⟨r, hr⟩ := hk.2 i j; rw [← hr]; exact r.2

theorem diagU_mem_kzero {a b : (HeightOneSpectrum.adicCompletion K v)ˣ}
    (ha : Valued.v (a : F) = 1) (hb : Valued.v (b : F) = 1) : diagU K v a b ∈ kzero K v := by
  have key : ∀ c d : (HeightOneSpectrum.adicCompletion K v)ˣ, Valued.v (c : F) = 1 → Valued.v (d : F) = 1 →
      ∀ i j, ((diagU K v c d : G) : Mat) i j ∈ (O) := by
    intro c d hc hd i j
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, coe_diagU]
    fin_cases i <;> fin_cases j <;> simp [hc, hd]
  rw [mem_kzero_iff]
  refine ⟨key a b ha hb, ?_⟩
  rw [diagU_inv]
  refine key a⁻¹ b⁻¹ ?_ ?_
  · rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]
  · rw [Units.val_inv_eq_inv_val, map_inv₀, hb, inv_one]

end Setup

section Uniformizer

theorem coe_uniformizer_ne_zero (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) : ((ϖ : O) : F) ≠ 0 := by
  intro h
  rw [h, map_zero] at hϖ
  exact WithZero.exp_ne_zero hϖ.symm

def piUnit (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) : (HeightOneSpectrum.adicCompletion K v)ˣ :=
  Units.mk0 ((ϖ : O) : F) (coe_uniformizer_ne_zero K v ϖ hϖ)

theorem v_piUnit_zpow (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (((piUnit K v ϖ hϖ) ^ k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) = WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  change Valued.v ((ϖ : O) : F) ^ k = _
  rw [hϖ, ← WithZero.exp_zsmul, smul_neg, zsmul_one, Int.cast_id]

theorem exists_eq_piUnit_zpow_mul (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) (u : (HeightOneSpectrum.adicCompletion K v)ˣ) :
    ∃ (m : ℤ) (w : (HeightOneSpectrum.adicCompletion K v)ˣ), Valued.v (w : F) = 1 ∧ u = piUnit K v ϖ hϖ ^ m * w := by
  have hu : Valued.v (u : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  set e : ℤ := WithZero.log (Valued.v (u : F)) with he
  refine ⟨-e, piUnit K v ϖ hϖ ^ e * u, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, v_piUnit_zpow, ← WithZero.exp_log hu, ← he, ← WithZero.exp_add,
      neg_add_cancel, WithZero.exp_zero]
  · rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

theorem piUnit_zpow_mem_integers_iff (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    (((piUnit K v ϖ hϖ) ^ k : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) ∈ (O) ↔ 0 ≤ k := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, v_piUnit_zpow, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

def shellRep (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) (mn : ℤ × ℤ) : G :=
  diagU K v (piUnit K v ϖ hϖ ^ mn.1) (piUnit K v ϖ hϖ ^ mn.2)

end Uniformizer

section Shells

theorem coe_unipotentGL2Hom (z : Multiplicative (HeightOneSpectrum.adicCompletion K v)) :
    ((unipotentGL2Hom z : G) : Mat) = !![1, z.toAdd; 0, 1] := rfl

theorem coe_diagU_inv_mul_unipotent_mul_diagU (a b a' b' : (HeightOneSpectrum.adicCompletion K v)ˣ)
    (z : Multiplicative (HeightOneSpectrum.adicCompletion K v)) :
    ((((diagU K v a b)⁻¹ * unipotentGL2Hom z * diagU K v a' b' : G)) : Mat) =
      !![((a⁻¹ * a' : (HeightOneSpectrum.adicCompletion K v)ˣ) : F), ((a⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) * z.toAdd * b';
        0, ((b⁻¹ * b' : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)] := by
  rw [diagU_inv, Units.val_mul, Units.val_mul, coe_diagU, coe_diagU, coe_unipotentGL2Hom]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem shell_unique (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ))
    (mn mn' : ℤ × ℤ) (x : (unip K v : Subgroup G)) (k k' : (kzero K v : Subgroup G))
    (h : (x : G) * shellRep K v ϖ hϖ mn * k = shellRep K v ϖ hϖ mn' * k') : mn = mn' := by
  obtain ⟨z, hz⟩ := x.2
  set π := piUnit K v ϖ hϖ with hπ

  set M : G := (shellRep K v ϖ hϖ mn')⁻¹ * (x : G) * shellRep K v ϖ hϖ mn with hM
  have hMk : M = (k' : G) * (k : G)⁻¹ := by
    rw [hM, eq_mul_inv_iff_mul_eq, mul_assoc, mul_assoc, ← mul_assoc (x : G), h, inv_mul_cancel_left]
  have hMmem : M ∈ kzero K v := by rw [hMk]; exact mul_mem k'.2 (inv_mem k.2)
  have hMinv : M⁻¹ ∈ kzero K v := inv_mem hMmem

  have hcoeM : (M : Mat) = !![((π ^ (mn.1 - mn'.1) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F),
      (((π ^ mn'.1)⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) * z.toAdd * ((π ^ mn.2 : (HeightOneSpectrum.adicCompletion K v)ˣ) : F);
      0, ((π ^ (mn.2 - mn'.2) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)] := by
    rw [hM, ← hz, shellRep, shellRep, coe_diagU_inv_mul_unipotent_mul_diagU, ← zpow_neg, ← zpow_neg, ← zpow_add,
      ← zpow_add, neg_add_eq_sub, neg_add_eq_sub]
  have hcoeMinv : ((M⁻¹ : G) : Mat) = !![((π ^ (mn'.1 - mn.1) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F),
      (((π ^ mn.1)⁻¹ : (HeightOneSpectrum.adicCompletion K v)ˣ) : F) * (z⁻¹).toAdd * ((π ^ mn'.2 : (HeightOneSpectrum.adicCompletion K v)ˣ) : F);
      0, ((π ^ (mn'.2 - mn.2) : (HeightOneSpectrum.adicCompletion K v)ˣ) : F)] := by
    have : M⁻¹ = (shellRep K v ϖ hϖ mn)⁻¹ * unipotentGL2Hom z⁻¹ * shellRep K v ϖ hϖ mn' := by
      rw [hM, ← hz, map_inv]; group
    rw [this, shellRep, shellRep, coe_diagU_inv_mul_unipotent_mul_diagU, ← zpow_neg, ← zpow_neg, ← zpow_add,
      ← zpow_add, neg_add_eq_sub, neg_add_eq_sub]
  have i1 : 0 ≤ mn.1 - mn'.1 := by
    rw [← piUnit_zpow_mem_integers_iff K v ϖ hϖ]
    have := ((mem_kzero_iff K v M).mp hMmem).1 0 0
    rwa [hcoeM] at this
  have i2 : 0 ≤ mn'.1 - mn.1 := by
    rw [← piUnit_zpow_mem_integers_iff K v ϖ hϖ]
    have := ((mem_kzero_iff K v (M⁻¹)).mp hMinv).1 0 0
    rwa [hcoeMinv] at this
  have i3 : 0 ≤ mn.2 - mn'.2 := by
    rw [← piUnit_zpow_mem_integers_iff K v ϖ hϖ]
    have := ((mem_kzero_iff K v M).mp hMmem).1 1 1
    rwa [hcoeM] at this
  have i4 : 0 ≤ mn'.2 - mn.2 := by
    rw [← piUnit_zpow_mem_integers_iff K v ϖ hϖ]
    have := ((mem_kzero_iff K v (M⁻¹)).mp hMinv).1 1 1
    rwa [hcoeMinv] at this
  exact Prod.ext (by omega) (by omega)

theorem exists_shell (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) (g : G) :
    ∃ (x : (unip K v : Subgroup G)) (mn : ℤ × ℤ) (k : (kzero K v : Subgroup G)),
      g = (x : G) * shellRep K v ϖ hϖ mn * k := by
  obtain ⟨z, a₁, a₂, k, hk, hg⟩ :=
    LocalGL2.iwasawa_decomposition_diag (HeightOneSpectrum.adicCompletionIntegers K v)
      (HeightOneSpectrum.adicCompletion K v) g
  obtain ⟨m, w₁, hw₁, ha₁⟩ := exists_eq_piUnit_zpow_mul K v ϖ hϖ a₁
  obtain ⟨n, w₂, hw₂, ha₂⟩ := exists_eq_piUnit_zpow_mul K v ϖ hϖ a₂
  refine ⟨⟨unipotentGL2Hom (Multiplicative.ofAdd z), ⟨_, rfl⟩⟩, (m, n),
    ⟨diagU K v w₁ w₂ * k, mul_mem (diagU_mem_kzero K v hw₁ hw₂) (mem_kzero_of_mem_integralSubgroup K v hk)⟩, ?_⟩
  have hprod : shellRep K v ϖ hϖ (m, n) * (diagU K v w₁ w₂ * k) = diagU K v a₁ a₂ * k := by
    rw [← mul_assoc, shellRep, diagU_mul, ← ha₁, ← ha₂]
  refine Units.ext ?_
  change (g : Mat) = ((unipotentGL2Hom (Multiplicative.ofAdd z) * shellRep K v ϖ hϖ (m, n) *
    (diagU K v w₁ w₂ * k) : G) : Mat)
  rw [mul_assoc, hprod, Units.val_mul, Units.val_mul, coe_diagU, coe_unipotentGL2Hom, hg, Matrix.mul_assoc]
  rfl

end Shells

section Formula

theorem lintegral_mul_density_eq_tsum_shells (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hϖ : Valued.v ((ϖ : O) : F) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace G := localGLBorel K v
    haveI : BorelSpace G := borelSpace_localGLBorel K v
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (μN : Measure (unip K v : Subgroup G)) [μN.IsHaarMeasure]
      (f : G → ℝ≥0∞), Measurable f → (∀ x ∈ (unip K v : Subgroup G), ∀ g : G, f (x * g) = f g) →
      (∀ mn : ℤ × ℤ, μN (shellSlice (unip K v) (kzero K v) (shellRep K v ϖ hϖ mn)) ≠ 0 ∧
          μN (shellSlice (unip K v) (kzero K v) (shellRep K v ϖ hϖ mn)) ≠ ∞) ∧
      ∫⁻ g, f g * HaarQuotient.density (unip K v : Subgroup G) μN g ∂μ =
        ∑' mn : ℤ × ℤ, (μN (shellSlice (unip K v) (kzero K v) (shellRep K v ϖ hϖ mn)))⁻¹ *
          ∫⁻ k in ((kzero K v : Subgroup G) : Set G), f (shellRep K v ϖ hϖ mn * k) ∂μ := by
  intro μ _ μN _ f hf hfH
  letI : MeasurableSpace G := localGLBorel K v
  haveI : BorelSpace G := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  haveI := secondCountableTopology_localGL K v
  haveI : μN.IsMulRightInvariant :=
    ⟨fun g => by
      have : (fun h : (unip K v : Subgroup G) => h * g) = fun h => g * h := funext fun h => unip_comm K v h g
      rw [this]
      exact map_mul_left_eq_self μN g⟩
  have hsl := fun mn : ℤ × ℤ => shellSlice_ne_zero_and_ne_top (unip K v) (isClosed_unip K v) μN (kzero K v)
    (isOpen_kzero K v) (isCompact_kzero K v) (shellRep K v ϖ hϖ mn)
  refine ⟨hsl, ?_⟩
  exact lintegral_mul_density_eq_tsum_setLIntegral_translate_of_iwasawa μ (unip K v) (isClosed_unip K v) μN
    (kzero K v) (isOpen_kzero K v).measurableSet (shellRep K v ϖ hϖ) (exists_shell K v ϖ hϖ)
    (fun i j x k k' h => shell_unique K v ϖ hϖ i j x k k' h) (fun mn => (hsl mn).1) (fun mn => (hsl mn).2)
    f hf hfH

end Formula

end HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc"
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient"

end
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"

namespace HaarQuotient
p2m_export "HaarQuotient" "weight density measure lintegral_eq_lintegral_lintegral_mul_out lintegral_density_mul_eq_one"
namespace CellMajorantLoc
namespace LocalGL2Iwasawa
p2m_open "HaarQuotient"

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

noncomputable def diagUHom : (HeightOneSpectrum.adicCompletion K v)ˣ × (HeightOneSpectrum.adicCompletion K v)ˣ →*
    GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) where
  toFun p := diagU K v p.1 p.2
  map_one' := by
    refine Units.ext ?_
    change ((diagU K v 1 1 : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)) :
      Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) = 1
    rw [coe_diagU]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := (diagU_mul K v p.1 p.2 q.1 q.2).symm

theorem diagU_zpow (a b : (HeightOneSpectrum.adicCompletion K v)ˣ) (n : ℤ) :
    (diagU K v a b) ^ n = diagU K v (a ^ n) (b ^ n) := by
  change (diagUHom K v (a, b)) ^ n = diagUHom K v ((a, b) ^ n)
  rw [map_zpow]

theorem scalarPi_eq_diagU (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)
    (hϖ : Valued.v ((ϖ : HeightOneSpectrum.adicCompletionIntegers K v) : HeightOneSpectrum.adicCompletion K v) =
      WithZero.exp (-1 : ℤ)) :
    scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ =
      diagU K v (piUnit K v ϖ hϖ) (piUnit K v ϖ hϖ) := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [scalarPi, piUnit]

theorem diagZ_eq_diagU (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)
    (hϖ : Valued.v ((ϖ : HeightOneSpectrum.adicCompletionIntegers K v) : HeightOneSpectrum.adicCompletion K v) =
      WithZero.exp (-1 : ℤ)) (d : ℤ) :
    diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ d = diagU K v (piUnit K v ϖ hϖ ^ d) 1 := by
  refine Units.ext ?_
  rw [coe_diagU]
  simp [diagZ, piUnit, Units.val_zpow_eq_zpow_val]

theorem scalarPi_zpow_mul_diagZ_eq_shellRep (ϖ : HeightOneSpectrum.adicCompletionIntegers K v)
    (hπ : algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) ϖ ≠ 0)
    (hϖ : Valued.v ((ϖ : HeightOneSpectrum.adicCompletionIntegers K v) : HeightOneSpectrum.adicCompletion K v) =
      WithZero.exp (-1 : ℤ)) (dn : ℤ × ℤ) :
    scalarPi (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ ^ dn.2 *
        diagZ (algebraMap _ (HeightOneSpectrum.adicCompletion K v) ϖ) hπ dn.1 =
      shellRep K v ϖ hϖ (dn.2 + dn.1, dn.2) := by
  rw [scalarPi_eq_diagU K v ϖ hπ hϖ, diagZ_eq_diagU K v ϖ hπ hϖ, diagU_zpow, diagU_mul, shellRep, zpow_add, mul_one]

def shellEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun dn := (dn.2 + dn.1, dn.2)
  invFun mn := (mn.1 - mn.2, mn.2)
  left_inv dn := by ext <;> simp
  right_inv mn := by ext <;> simp

end HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2.HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa"

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker HaarQuotient.CellMajorantLoc HaarQuotient.CellMajorantLoc.LocalGL2Iwasawa in

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion K))) [μ.IsHaarMeasure]
      (μN : Measure ↥(unipotentGL2Hom (R := v.adicCompletion K)).range) [μN.IsHaarMeasure]
      (f : GL (Fin 2) (v.adicCompletion K) → ℝ≥0∞), Measurable f →
      (∀ x ∈ (unipotentGL2Hom (R := v.adicCompletion K)).range, ∀ g : GL (Fin 2) (v.adicCompletion K),
        f (x * g) = f g) →
      (∀ dn : ℤ × ℤ,
        μN {x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range |
            (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1)⁻¹ *
              (x : GL (Fin 2) (v.adicCompletion K)) *
              (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1) ∈
            AdelicDock.localLevelOne (𝓞 K) K v ⊤} ≠ 0 ∧
        μN {x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range |
            (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1)⁻¹ *
              (x : GL (Fin 2) (v.adicCompletion K)) *
              (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1) ∈
            AdelicDock.localLevelOne (𝓞 K) K v ⊤} ≠ ∞) ∧
      ∫⁻ g, f g * HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion K)).range μN g ∂μ =
        ∑' dn : ℤ × ℤ,
          (μN {x : ↥(unipotentGL2Hom (R := v.adicCompletion K)).range |
              (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1)⁻¹ *
                (x : GL (Fin 2) (v.adicCompletion K)) *
                (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1) ∈
              AdelicDock.localLevelOne (𝓞 K) K v ⊤})⁻¹ *
            ∫⁻ k in ((AdelicDock.localLevelOne (𝓞 K) K v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion K))) :
                Set (GL (Fin 2) (v.adicCompletion K))),
              f (scalarPi (algebraMap _ (v.adicCompletion K) ϖ) hπ ^ dn.2 * diagZ (algebraMap _ (v.adicCompletion K) ϖ) hπ dn.1 * k) ∂μ := by
  intro μ _ μN _ f hf hfH
  have hϖ' : Valued.v ((ϖ : HeightOneSpectrum.adicCompletionIntegers K v) : HeightOneSpectrum.adicCompletion K v) =
      WithZero.exp (-1 : ℤ) := hϖ
  obtain ⟨hsl, hmain⟩ := lintegral_mul_density_eq_tsum_shells K v ϖ hϖ' μ μN f hf hfH
  have key := scalarPi_zpow_mul_diagZ_eq_shellRep K v ϖ hπ hϖ'
  refine ⟨fun dn => ?_, ?_⟩
  · rw [key dn]
    exact hsl _
  · rw [hmain, ← (shellEquiv).tsum_eq]
    refine tsum_congr fun dn => ?_
    rw [key dn]
    rfl

end S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2
end P2MW
export P2MW.S_AutomorphicForm_lintegral_mul_density_eq_tsum_torusShells_localGL2 (solution)
