-- Prove2me | solution 1 for Auto.aux_liftRaw_toLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:42.126616+00:00
-- url     : https://prove2.me/submissions/1736a411-fd35-4236-bb15-0e7af487bc97

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} (F : aux_RVector n → ℝ)
    (x : aux_RVector n) :
    aux_liftRaw F (WithLp.toLp 2 x) = F x :=
  rfl
end Auto
