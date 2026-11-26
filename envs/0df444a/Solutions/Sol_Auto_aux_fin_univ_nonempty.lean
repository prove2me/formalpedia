-- Prove2me | solution 1 for Auto.aux_fin_univ_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:19.958777+00:00
-- url     : https://prove2.me/submissions/d36d1c4f-3359-4220-bbb6-62f160a27b1e

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
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty := by
  refine ⟨⟨0, hn⟩, Finset.mem_univ _⟩
end Auto
