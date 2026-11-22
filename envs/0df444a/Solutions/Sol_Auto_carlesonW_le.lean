-- Prove2me | solution 1 for Auto.carlesonW_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:58:48.3803+00:00
-- url     : https://prove2.me/submissions/b37024df-e6bd-465e-a2b3-127fe4fef142

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
theorem _root_.solution (t u : ℝ) : carlesonW t u ≤ carlesonBump₀ u := by
  unfold carlesonW
  have h₀ := carlesonBump₀.nonneg (x := u)
  have h₁ := carlesonBump₁.nonneg (x := 2 * u - t)
  have h₂ := carlesonBump₁.le_one (x := 2 * u - t)
  have h₃ := carlesonBump₁.nonneg (x := t - u)
  have h₄ := carlesonBump₁.le_one (x := t - u)
  calc carlesonBump₀ u * carlesonBump₁ (2 * u - t) * carlesonBump₁ (t - u)
      ≤ carlesonBump₀ u * 1 * 1 := by gcongr
    _ = carlesonBump₀ u := by ring
end Auto
