-- Prove2me | solution 1 for Auto.aux_norm_finAdd_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:59.087978+00:00
-- url     : https://prove2.me/submissions/d8151985-0d4e-494a-8270-f9dc5ae40217

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Theorems.Thm_Auto_aux_norm_finAdd_fst_le
public import Theorems.Thm_Auto_aux_norm_finAdd_snd_le

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function
namespace Auto
theorem _root_.solution {n m : ℕ} (w : EuclideanSpace ℝ (Fin (n + m))) :
    ‖EuclideanSpace.finAddEquivProd w‖ ≤ ‖w‖ := by
  rw [Prod.norm_def]
  exact max_le (aux_norm_finAdd_fst_le w) (aux_norm_finAdd_snd_le w)
end Auto
