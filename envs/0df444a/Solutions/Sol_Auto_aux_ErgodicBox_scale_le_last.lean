-- Prove2me | solution 1 for Auto.aux_ErgodicBox.scale_le_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:09.165157+00:00
-- url     : https://prove2.me/submissions/10eea6a6-2d20-485b-9dbc-1aea4b2609eb

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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution {J : ℕ} (N : Fin (J + 1) → ℕ)
    (hN : StrictMono N) (q : Fin (J + 1)) :
    N q ≤ N (Fin.last J) :=
  hN.monotone (Fin.le_last q)
end Auto.aux_ErgodicBox
