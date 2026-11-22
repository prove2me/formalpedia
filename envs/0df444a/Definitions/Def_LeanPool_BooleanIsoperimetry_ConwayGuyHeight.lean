-- Prove2me | Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
-- name    : LeanPool_BooleanIsoperimetry_ConwayGuyHeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:16:03.810264+00:00
-- url     : https://prove2.me/theorems/9c37418a-0ee3-49aa-a3a8-8560026823a3
-- title:
--   Conway Guy Height
-- statement:
--   Definitions and structural lemmas for Conway Guy Height, from Alexey Milovanov; Egor Lyfar; LeanPool contributors's pinned Boolean Isoperimetry and Conway--Guy Coherent Gaps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
namespace BooleanIsoperimetry.CoherentGap
noncomputable def residual (width dimension : ℕ) : ℤ :=
  conwayGuyHeight dimension -
    ∑ index : Fin width,
      conwayGuyHeight (dimension - index.val - 1)
end BooleanIsoperimetry.CoherentGap


