-- Prove2me | solution 1 for Auto.MemW0.aux_mul_finAdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:01.465611+00:00
-- url     : https://prove2.me/submissions/16b31480-ce39-4183-a5d3-7eb35cfe1777

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_MemW0_aux_mul_prod
public import Theorems.Thm_Auto_aux_memW0_finAdd_tensor_of_memW0_prod

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
namespace MemW0
theorem _root_.solution {n m : ℕ} {𝕜 : Type*} [NormedField 𝕜]
    {f : EuclideanSpace ℝ (Fin n) → 𝕜} {g : EuclideanSpace ℝ (Fin m) → 𝕜}
    (hf : MemW0 f) (hg : MemW0 g) :
    MemW0 (fun z : EuclideanSpace ℝ (Fin (n + m)) ↦
      f (EuclideanSpace.finAddEquivProd z).1 * g (EuclideanSpace.finAddEquivProd z).2) :=
  aux_memW0_finAdd_tensor_of_memW0_prod hf.1 hg.1 (hf.aux_mul_prod hg)
end MemW0
end Auto
