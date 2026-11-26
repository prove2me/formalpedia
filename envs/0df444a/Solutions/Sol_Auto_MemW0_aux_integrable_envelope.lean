-- Prove2me | solution 1 for Auto.MemW0.aux_integrable_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:36.646021+00:00
-- url     : https://prove2.me/submissions/c938699c-0ff7-4efd-990a-68817bee9b3b

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
    [NormedAddCommGroup 𝕜] {f : E → 𝕜} (hf : MemW0 f) : Integrable (wienerEnvelope f 1) :=
  hf.2
end MemW0
end Auto
