-- Prove2me | Definitions.Def_MillerRabin_StrongProbable
-- name    : MillerRabin_StrongProbable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T08:00:58.068292+00:00
-- url     : https://prove2.me/theorems/be66d80c-5795-47a6-a290-59b955372d30
-- title:
--   Strong Probable
-- statement:
--   Definitions and structural lemmas for Strong Probable, from hanwenzhu/miller-rabin contributors (see pinned LICENSE and source headers)'s pinned Miller–Rabin primality test error bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Theorems.Thm_P2M_ZMod_fst_chineseRemainder__e38dff19d888
import Theorems.Thm_P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
import Theorems.Thm_P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
import Theorems.Thm_Subgroup_mem_closure_neg_one
import Theorems.Thm_ZMod_fst_chineseRemainder
import Theorems.Thm_ZMod_snd_chineseRemainder
import Theorems.Thm_ZMod_unitsMap_neg
import Theorems.Thm_oddPart_pos
attribute [local simp] P2M_ZMod_fst_chineseRemainder__e38dff19d888
attribute [local simp] P2M_ZMod_snd_chineseRemainder__54cb5b0df9be
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm__ebf12eca55d4
attribute [local simp] P2M_ZMod_unitsMap_chineseRemainder__symm_e0b61d79a158
attribute [local simp] Subgroup.mem_closure_neg_one
attribute [local simp] ZMod.fst_chineseRemainder
attribute [local simp] ZMod.snd_chineseRemainder
attribute [local simp] ZMod.unitsMap_neg


set_option autoImplicit false
open Nat
def SPP (n : ℕ) (a : ZMod n) : Prop :=
  a ^ oddPart (n - 1) = 1 ∨
  ∃ s < val₂ (n - 1), a ^ (2 ^ s * oddPart (n - 1)) = -1
namespace SPP
section Algorithm
def millerRabinAux (n s : ℕ) (b : ZMod n) : Bool := Id.run do
  let mut b := b
  for _ in List.range s do
    if b == -1 then return true
    b := b * b
  return false
lemma _root_.List.range_succ_eq_cons_map_succ (s : ℕ) :
    List.range (s + 1) = 0 :: (List.range s).map Nat.succ := by
  induction s with
  | zero => simp
  | succ s ih =>
    conv_lhs => rw [List.range_succ]
    conv_rhs => rw [List.range_succ]
    simp [ih]
lemma millerRabinAux_eq_true_iff {n : ℕ} (s : ℕ) (b : ZMod n) :
    millerRabinAux n s b = true ↔ ∃ s' : ℕ, s' < s ∧ b ^ 2 ^ s' = -1 := by
  unfold millerRabinAux
  induction s generalizing b with
  | zero => simp
  | succ s ih =>
    rw [List.range_succ_eq_cons_map_succ]
    by_cases h : b = -1
    · simp [h]; exact ⟨0, Nat.zero_le _, by norm_num⟩
    · suffices (∃ s' < s, (b * b) ^ 2 ^ s' = -1) ↔ ∃ s' < s + 1, b ^ 2 ^ s' = -1 by
        simpa [h] using (ih (b * b)).trans this
      constructor
      · intro ⟨s', hs', hs''⟩
        use s' + 1, by omega, by simpa [_root_.pow_succ', pow_mul, pow_two] using hs''
      · intro ⟨s', hs', hs''⟩
        have : s' ≠ 0 := by rintro rfl; apply h; simpa using hs''
        rw [show s' = s' - 1 + 1 by omega] at hs''
        use s' - 1, by omega, by simpa [_root_.pow_succ', pow_mul, pow_two] using hs''
def millerRabin (n : ℕ) (a : ZMod n) : Bool := Id.run do
  let s := val₂ (n - 1)
  let k := (n - 1) / 2 ^ s
  let b := a ^ k
  return b == 1 || millerRabinAux n s b
lemma millerRabin_eq_true_iff {n : ℕ} (a : ZMod n) :
    millerRabin n a = true ↔ SPP n a := by
  simp [millerRabin, millerRabinAux_eq_true_iff, SPP, pow_mul, pow_right_comm]
end Algorithm
@[simp]
theorem not_spp_zero (n : ℕ) [Fact (1 < n)] : ¬SPP n 0 := by
  simp [SPP, pow_mul, zero_pow (oddPart_pos (n := n - 1)).ne']
section Decidable
instance decidable {n : ℕ} {a : ZMod n} :
    Decidable (SPP n a) :=
  propext (millerRabin_eq_true_iff a) ▸ decEq _ _
end Decidable
section FPP
end FPP
section NonwitnessGroup
open Subgroup
def nonwitnessGroup (n : ℕ) : Subgroup (ZMod n)ˣ :=
  closure { a | SPP n a }
variable {n : ℕ}
section OfPrimePow
variable {m p : ℕ} [pp : Fact p.Prime]
noncomputable abbrev rem (y : ZMod (p ^ (m + 1))) :
    { r : ZMod (p ^ (m + 1)) //
      y = ((y.cast : ZMod (p ^ m)).cast : ZMod (p ^ (m + 1))) + (p : ZMod (p ^ (m + 1))) ^ m * r } := by
  have := ZMod.natCast_val (R := ZMod (p ^ m)) y
  choose r hr using (ZMod.natCast_eq_iff _ _ _).mp this
  apply_fun Nat.cast (R := ZMod (p ^ (m + 1))) at hr
  rw [ZMod.natCast_zmod_val, cast_add, ← ZMod.cast_eq_val, cast_mul, cast_pow] at hr
  exact ⟨(r : ZMod (p ^ (m + 1))), hr⟩
end OfPrimePow
section DefS₀G
def s₀ (n : ℕ) : ℕ :=
  Nat.findGreatest (fun s ↦ ∃ a : (ZMod n)ˣ, a ^ (2 ^ s * oddPart (n - 1)) = -1) (val₂ (n - 1) - 1)
abbrev G (n : ℕ) : Subgroup (ZMod n)ˣ :=
  comap (powMonoidHom (2 ^ s₀ n * oddPart (n - 1))) (closure {-1})
end DefS₀G
section OfNotCarmichael
abbrev F (n : ℕ) : Subgroup (ZMod n)ˣ :=
  (powMonoidHom (n - 1)).ker
end OfNotCarmichael
section OfCarmichael
abbrev H {m n : ℕ} (h : m ∣ n) : Subgroup (ZMod n)ˣ :=
  comap (powMonoidHom (2 ^ s₀ n * oddPart (n - 1))) (comap (ZMod.unitsMap h) (closure {-1}))
end OfCarmichael
end NonwitnessGroup
open Finset
section Probability
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable def millerRabinRandomSource (n : ℕ) [Fact (1 < n)] : PMF (ZMod n) :=
  PMF.uniformOfFinset {0}ᶜ ⟨1, by simp⟩
end Probability
end SPP


