-- Prove2me | solution 1 for Auto.integrable_prod_of_le_gdom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:27:08.128469+00:00
-- url     : https://prove2.me/submissions/295ca1f5-aa5b-43bd-8621-6a6b5ad2d061

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_integrable_gdom

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
namespace Auto
theorem _root_.solution {f : ℝ × (Fin 3 → ℝ) → ℝ} {sa sb : ℝ} (hsa : 0 < sa)
    (hf : ContinuousOn f (Set.Ioi 0 ×ˢ Set.univ)) {C ε : ℝ} (hε : 0 < ε)
    (hb : ∀ s ∈ Set.Ioc sa sb, ∀ p, |f (s, p)| ≤ C * gdom ε p) :
    Integrable f ((volume.restrict (Set.Ioc sa sb)).prod volume) := by
  have hμ : (volume.restrict (Set.Ioc sa sb)).prod (volume : Measure (Fin 3 → ℝ)) = ((volume :
      Measure ℝ).prod volume).restrict (Set.Ioc sa sb ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hg : Integrable (fun z : ℝ × (Fin 3 → ℝ) => C * gdom ε z.2) ((volume.restrict (Set.Ioc sa
      sb)).prod volume) := by
    have := (integrable_const (1 : ℝ) (μ := volume.restrict (Set.Ioc sa sb))).mul_prod
        ((integrable_gdom hε).const_mul C)
    simpa using this
  refine hg.mono' ?_ ?_
  · rw [hμ]
    refine (hf.mono ?_).aestronglyMeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
    exact Set.prod_mono (fun s hs => hsa.trans hs.1) le_rfl
  · rw [hμ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    rw [Real.norm_eq_abs]
    exact hb z.1 hz.1 z.2
end Auto
