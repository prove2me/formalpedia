-- Prove2me | Definitions.Def_ChandraFurstLipton_LowerBoundEval
-- name    : ChandraFurstLipton_LowerBoundEval
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T18:14:08.224309+00:00
-- url     : https://prove2.me/theorems/d1a920b6-0f79-4503-a77b-240ffbe646b0
-- title:
--   Lower Bound Eval
-- statement:
--   Definitions and structural lemmas for Lower Bound Eval, from Yaël Dillies and Isabel Dahlgren's pinned Chandra–Furst–Lipton: number-on-the-forehead protocols development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/LowerBoundEval.lean

module
public import Definitions.Def_ChandraFurstLipton_NOFModel
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace NOF
variable {ι G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ} [NeZero d]
  {P : Protocol G d} {t : ℕ} {B : List Bool} {a : ZMod d → ZMod d → G} [Fintype ι]
def eval (x : ι → G) : Bool :=
  ∑ i, x i == 0
variable [DecidableEq ι]
def getBits (B : List Bool) (i : ℕ) (d : ℕ) : List Bool := Id.run do
  let mut L := []
  for j in [0:B.length] do
    L := L ++ [B.getI ((i - 1) % d + j)]
  pure L
variable [Fintype G]
noncomputable def Protocol.trivial (hd : 3 ≤ d) (F : (ZMod d → G) → Bool) : Protocol G d where
  nextBit i x B := by
    refine (Nat.bits (Fintype.equivFin G (x ⟨i + 1, ?_ ⟩))).getI (B.length / d)
    rw [Ne, add_eq_left, ← Nat.cast_one, ZMod.natCast_eq_zero_iff, Nat.dvd_one]
    omega
  guess i x B := F fun j ↦
    if h : j = i then
      (Fintype.equivFin G).symm <| (ZMod.finEquiv _).symm
        (BitVec.toNat (BitVec.ofBoolListLE (getBits B i.val d)))
    else
      x ⟨j, h⟩
end NOF


