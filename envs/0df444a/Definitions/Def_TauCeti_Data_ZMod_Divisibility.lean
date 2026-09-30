-- Prove2me | Definitions.Def_TauCeti_Data_ZMod_Divisibility
-- name    : TauCeti_Data_ZMod_Divisibility
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:31:22.33244+00:00
-- url     : https://prove2.me/theorems/a40d49c0-f772-4469-931d-539e88bd8735
-- title:
--   Integer divisibility read off congruences modulo n
-- statement:
--   If integers $z,w$ have nonnegative product and are congruent modulo $m$, then their absolute values are congruent modulo $m$:
--
--   $$
--   zw\geq0,\quad z\equiv w\pmod m\quad\Longrightarrow\quad |z|\equiv|w|\pmod m.
--   $$
--
--   This supports congruence calculations involving absolute norms.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Data/ZMod/Divisibility.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Data/ZMod/Divisibility.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units

section
set_option autoImplicit true
/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/-!
# Integer divisibility read off congruences modulo `n`

Facts about integers read off congruences in `ZMod n`.

A linear congruence with unit coefficient is solvable: if `b` is a unit modulo `n`, then some
residue `j : ZMod n` satisfies `n ∣ a - j.val * b` over `ℤ`. The solution is `j = a b⁻¹`, and it
is returned as a residue class together with its canonical representative `j.val`, which is the
form a coset representative indexed by `Fin n` needs.

`ZMod.exists_dvd_sub_val_mul` was extracted from
`TauCeti/NumberTheory/ModularForms/CongruenceSubgroups.lean`, where it was private; that index
calculation was ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GL2/CongruenceIndex.lean`, Chris Birkbeck, Apache-2.0). The lemma is
consumed there and in `HeckeRing/GL2/Gamma1/CoprimeCosets.lean`.

`ZMod.natCast_dvd_val_sub_of_unitsMap_eq` is adapted from the same project (Chris Birkbeck,
`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `2baa76f74`, file
`projects/LeanModularForms/LeanModularForms/Eigenforms/ConductorTheorem.lean`, declaration
`natCast_val_sub_dvd_of_unitsMap_eq` (:665). Two departures from the source: it is stated for an
arbitrary divisor `d ∣ N` rather than only for the reduction modulo `N / l`, which is all its
proof uses, and the name places the divisibility in Mathlib's operand order.

## Main results

* `ZMod.exists_dvd_sub_val_mul`: the congruence `j b ≡ a (mod n)` has a solution `j : ZMod n`
  whenever `b` is a unit modulo `n`.
* `ZMod.natCast_dvd_val_sub_of_unitsMap_eq`: two units with the same image under `ZMod.unitsMap`
  along `d ∣ N` have representatives congruent modulo `d`, as integers.
* `ZMod.intCast_lcm_eq_of_eq_of_eq`: one residue modulo `lcm a b` from the residues modulo `a`
  and `b` — the Chinese remainder theorem for a single integer.
* `ZMod.natCast_natAbs_eq_of_mul_nonneg`: congruent integers with nonnegative product have
  congruent absolute values.
-/

 section

namespace ZMod







/-- **Congruent integers with nonnegative product have congruent absolute values.** If
`z * w ≥ 0` and `z ≡ w` modulo `m`, then `|z| ≡ |w|` modulo `m`. -/
theorem natCast_natAbs_eq_of_mul_nonneg {m : ℕ} {z w : ℤ} (hzw : 0 ≤ z * w)
    (h : (z : ZMod m) = w) : (z.natAbs : ZMod m) = w.natAbs := by
  rcases hzw.lt_or_eq with hzw | hzw
  · rcases pos_and_pos_or_neg_and_neg_of_mul_pos hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩ <;>
      simp [← Int.cast_natCast (R := ZMod m), abs_of_pos, abs_of_neg, hz, hw, h]
  -- if one of them vanishes, both are divisible by `m`, and so are their absolute values
  rcases mul_eq_zero.mp hzw.symm with rfl | rfl
  · rw [Int.cast_zero, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [Int.natAbs_zero, Nat.cast_zero, eq_comm, ZMod.natCast_eq_zero_iff]
    exact Int.natCast_dvd.mp h
  · rw [Int.cast_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rw [Int.natAbs_zero, Nat.cast_zero, ZMod.natCast_eq_zero_iff]
    exact Int.natCast_dvd.mp h

end ZMod

end
end


