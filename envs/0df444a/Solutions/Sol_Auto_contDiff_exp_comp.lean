-- Prove2me | solution 1 for Auto.contDiff_exp_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:00:00.977892+00:00
-- url     : https://prove2.me/submissions/6d60df75-3f7a-470e-a3a5-12be8cdf431e

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_contDiff_ofReal_comp

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p => Complex.exp ((f p : ℂ) * Complex.I) :=
  Complex.contDiff_exp.comp ((contDiff_ofReal_comp hf).mul contDiff_const)
end Auto
