-- Prove2me | solution 1 for Auto.MemW0.aux_integrable_wienerEnvelope_slice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:49.730394+00:00
-- url     : https://prove2.me/submissions/e36189b5-9935-4299-8306-aba1a084dfa2

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_integrable
public import Theorems.Thm_Auto_MemW0_aux_mem_wienerEnvelope_prod
public import Theorems.Thm_Auto_MemW0_aux_memW0_slice

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {m l : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin l) → 𝕜}
    (hf : MemW0 f) (u : EuclideanSpace ℝ (Fin m)) :
    Integrable (fun v ↦ wienerEnvelope f 1 (u, v)) :=
  MemW0.aux_integrable (MemW0.aux_memW0_slice (hf.aux_mem_wienerEnvelope_prod zero_le_one) u)
end MemW0
end Auto
