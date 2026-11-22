-- Prove2me | solution 1 for Auto.contDiff_ofReal_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T18:29:08.655785+00:00
-- url     : https://prove2.me/submissions/744cc260-b195-4ea2-b8a3-f05bd7f82b3c

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
theorem _root_.solution {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p => (f p : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hf
end Auto
