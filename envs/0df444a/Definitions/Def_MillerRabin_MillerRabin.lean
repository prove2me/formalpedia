-- Prove2me | Definitions.Def_MillerRabin_MillerRabin
-- name    : MillerRabin_MillerRabin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T08:03:18.781849+00:00
-- url     : https://prove2.me/theorems/ae73fc50-c9e7-4200-9689-f8ffefd544f6
-- title:
--   Miller Rabin
-- statement:
--   Definitions and structural lemmas for Miller Rabin, from hanwenzhu/miller-rabin contributors (see pinned LICENSE and source headers)'s pinned Miller–Rabin primality test error bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/MillerRabin.lean

import Definitions.Def_MillerRabin_StrongProbable
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_Subgroup_mem_closure_neg_one
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
import Theorems.Thm_ZMod_unitsMap_neg
attribute [local simp] P2M_ZMod_fst_chineseRemainder__e38dff19d888
attribute [local simp] P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
attribute [local simp] Subgroup.mem_closure_neg_one
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder
attribute [local simp] ZMod.unitsMap_neg


set_option autoImplicit false
section randNat
lemma lo_le_randNat {gen : Type _} [RandomGen gen] (g : gen) (lo hi : Nat) (h : lo ≤ hi) :
    lo ≤ (randNat g lo hi).1 := by
  simp [randNat, h.not_gt]
lemma randNat_le_hi {gen : Type _} [RandomGen gen] (g : gen) (lo hi : Nat) (h : lo ≤ hi) :
    (randNat g lo hi).1 ≤ hi := by
  simp [randNat, h.not_gt]
  have (n : ℕ) : n % (hi - lo + 1) ≤ hi - lo := Nat.lt_succ.mp (Nat.mod_lt n (by omega))
  grw [this]
  omega
end randNat
class RandomNatGen (g : Type _) where
  next : g → (lo hi : Nat) → Nat × g
  next_lawful : ∀ g lo hi, lo ≤ hi → lo ≤ (next g lo hi).1 ∧ (next g lo hi).1 ≤ hi
instance (g : Type _) [RandomGen g] : RandomNatGen g := {
  next g lo hi := randNat g lo hi
  next_lawful g lo hi h := ⟨lo_le_randNat g lo hi h, randNat_le_hi g lo hi h⟩
}
namespace MillerRabin
def millerRabinCoreLoop {gen : Type _} [RandomNatGen gen] (g : gen) (n rep : ℕ) : Bool := Id.run do
  let s := val₂ (n - 1)
  let k := (n - 1) / 2 ^ s
  let mut g := g
  for _ in List.range rep do
    let (a, g') := RandomNatGen.next g 1 (n - 1)
    let b := a ^ k
    unless b == 1 || SPP.millerRabinAux n s b do return false
    g := g'
  return true
def millerRabin {gen : Type _} [RandomNatGen gen] (g : gen) (n rep : ℕ) : Bool := Id.run do
  if n ≤ 1 then return false
  else if n = 2 then return true
  else if n % 2 = 0 then return false
  else if rep = 0 then return false
  else return millerRabinCoreLoop g n rep
def millerRabinIO (n rep : ℕ) : IO Bool := do
  let gen ← IO.stdGenRef.get
  let (gen, gen') := RandomGen.split gen
  IO.stdGenRef.set gen
  return millerRabin gen' n rep
end MillerRabin


