-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSResidueCoordinates
-- name    : QEC_Coding_ExpanderCodes_LPSResidueCoordinates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:26:35.889208+00:00
-- url     : https://prove2.me/theorems/f84b0456-9a61-4b28-8413-15dcf7df7021
-- title:
--   LPSResidue Coordinates
-- statement:
--   Definitions and structural lemmas for LPSResidue Coordinates, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSResidueCoordinates.lean

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Find
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
def lpsResiduePairCandidate (q n : ℕ) : Prop :=
  n < q ^ 2 ∧
    ((n / q : ℕ) : ZMod q) ^ 2 + ((n % q : ℕ) : ZMod q) ^ 2 + 1 = 0
instance (q : ℕ) : DecidablePred (lpsResiduePairCandidate q) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))
theorem exists_lpsResiduePairCandidate (q : ℕ) [Fact q.Prime] :
    ∃ n, lpsResiduePairCandidate q n := by
  let : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨x, y, hxy⟩ := ZMod.sq_add_sq q (-1)
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  refine ⟨x.val * q + y.val, ?_, ?_⟩
  · have hx' : x.val + 1 ≤ q := by omega
    calc
      x.val * q + y.val < x.val * q + q := by omega
      _ = (x.val + 1) * q := by ring
      _ ≤ q * q := Nat.mul_le_mul_right q hx'
      _ = q ^ 2 := by ring
  · have hDiv : (x.val * q + y.val) / q = x.val := by
      rw [Nat.add_div (by omega)]
      simp [Nat.div_eq_of_lt hy, Nat.mod_eq_of_lt hy, Nat.not_le_of_lt hy, Nat.mul_div_cancel _ hq]
    have hMod : (x.val * q + y.val) % q = y.val := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hy]
    rw [hDiv, hMod, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination hxy
def lpsEffectiveResiduePairIndex (q : ℕ) [Fact q.Prime] : ℕ :=
  Nat.find (exists_lpsResiduePairCandidate q)
def lpsEffectiveResidueX (q : ℕ) [Fact q.Prime] : ZMod q :=
  (lpsEffectiveResiduePairIndex q / q : ℕ)
def lpsEffectiveResidueY (q : ℕ) [Fact q.Prime] : ZMod q :=
  (lpsEffectiveResiduePairIndex q % q : ℕ)
end QEC.Coding.TannerLiftedProduct


