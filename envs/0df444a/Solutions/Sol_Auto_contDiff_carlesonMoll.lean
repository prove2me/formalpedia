-- Prove2me | solution 1 for Auto.contDiff_carlesonMoll
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:49:36.872492+00:00
-- url     : https://prove2.me/submissions/2eae4a4f-bea4-4134-90c2-5305726a59f9

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Auto
theorem _root_.solution (k : ℕ) {h : ℝ → E} (hh : LocallyIntegrable h) :
    ContDiff ℝ ∞ (carlesonMoll k h) :=
  (carlesonMollifier k).hasCompactSupport_normed.contDiff_convolution_left _
    ((carlesonMollifier k).contDiff_normed (n := ⊤)) hh
end Auto
