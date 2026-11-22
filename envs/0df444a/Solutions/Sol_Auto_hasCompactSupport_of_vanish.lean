-- Prove2me | solution 1 for Auto.hasCompactSupport_of_vanish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:58:38.830378+00:00
-- url     : https://prove2.me/submissions/4c91ce81-4e15-4aa3-bab9-b62fb8f0e08e

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {A : ℝ}
    (hf : ∀ x, A < |x| → f x = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) fun x hx =>
    hf x (lt_of_not_ge fun h => hx (abs_le.mp h))
end Auto
