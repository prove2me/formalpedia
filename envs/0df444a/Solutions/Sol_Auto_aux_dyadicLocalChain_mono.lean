-- Prove2me | solution 1 for Auto.aux_dyadicLocalChain_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:44.412618+00:00
-- url     : https://prove2.me/submissions/3b087c5b-03a3-4498-84e7-d6fdee649506

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Auto
theorem _root_.solution {J : ℕ} {k : ℤ} {t : Fin (J + 1) → ℝ}
    (ht : Monotone t) : Monotone (aux_dyadicLocalChain J k t) := by
  exact (Set.monotone_projIcc _).comp ht
end Auto
