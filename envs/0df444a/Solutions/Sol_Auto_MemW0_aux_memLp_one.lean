-- Prove2me | solution 1 for Auto.MemW0.aux_memLp_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:01:10.236361+00:00
-- url     : https://prove2.me/submissions/40461154-145d-4f62-966a-32f52dab2a2a

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_integrable

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {f : EuclideanSpace ℝ (Fin d) → 𝕜} (hf : MemW0 f) : MemLp f 1 volume :=
  memLp_one_iff_integrable.mpr hf.aux_integrable
end MemW0
end Auto
