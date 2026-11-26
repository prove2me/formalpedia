-- Prove2me | solution 1 for Auto.MemW0.aux_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:30.2488+00:00
-- url     : https://prove2.me/submissions/9d2458a5-6df4-46b1-a33c-e16356f728e5

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {E 𝕜 : Type*} [NormedAddCommGroup E] [MeasureSpace E]
    [NormedAddCommGroup 𝕜] {f : E → 𝕜} (hf : MemW0 f) : Continuous f :=
  hf.1
end MemW0
end Auto
