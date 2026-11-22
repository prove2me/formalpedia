-- Prove2me | solution 1 for Auto.ContinuousOn.matSqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:21:36.279968+00:00
-- url     : https://prove2.me/submissions/05102463-54ef-4a9c-b501-a954065e753b

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sqrt_hsSq_sqrt_sub_le

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Auto
namespace ContinuousOn
theorem _root_.solution {Z : Type*} [TopologicalSpace Z] {f : Z → Matrix n n ℂ} {s : Set Z}
    (hf : ContinuousOn f s) {η : ℝ} (hη : 0 < η)
    (hpos : ∀ z ∈ s, (f z - (η : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    ContinuousOn (fun z => CFC.sqrt (f z)) s := by
  intro z hz
  refine tendsto_entry_of_hsSq ?_
  have h0 := tendsto_sqrt_hsSq_sub (hf z hz)
  have h1 : Tendsto (fun a => √(hsSq (f a - f z)) / (√η + √η)) (𝓝[s] z) (𝓝 0) := by
    simpa using h0.div_const (√η + √η)
  refine squeeze_zero' (Eventually.of_forall fun _ => Real.sqrt_nonneg _) ?_ h1
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact sqrt_hsSq_sqrt_sub_le hη (hpos a ha) (hpos z hz)
end ContinuousOn
end Auto
