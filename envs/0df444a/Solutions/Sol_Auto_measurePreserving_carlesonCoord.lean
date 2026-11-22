-- Prove2me | solution 1 for Auto.measurePreserving_carlesonCoord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:47:52.658973+00:00
-- url     : https://prove2.me/submissions/a8b55eee-5ba7-44ec-be94-d993eb9eb037

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution : MeasurePreserving carlesonCoord := by
  have h₁ : MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.2 - p.1 / 2)) := by
    refine (MeasurePreserving.id volume).skew_product (g := fun x u => u - x / 2) (by fun_prop)
      (ae_of_all _ fun x => ?_)
    exact (measurePreserving_sub_right volume (x / 2)).map_eq
  have h₂ : MeasurePreserving
      (fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.1.2 - q.1.1 / 2), q.2 - q.1.2 - q.1.1 / 2)) := by
    refine h₁.skew_product (g := fun p t => t - p.2 - p.1 / 2) (by fun_prop)
      (ae_of_all _ fun p => ?_)
    have he : (fun t : ℝ => t - p.2 - p.1 / 2) = fun t => t - (p.2 + p.1 / 2) := by
      ext t; ring
    rw [he]
    exact (measurePreserving_sub_right volume _).map_eq
  have hA := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure ℝ)
  have h₃ : MeasurePreserving (fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2), q.1.2)) :=
    (hA.symm MeasurableEquiv.prodAssoc).comp
      (((MeasurePreserving.id (volume : Measure ℝ)).prod
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ)))).comp hA)
  exact h₂.comp h₃
end Auto
