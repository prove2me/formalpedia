-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCentStarBit
-- name    : IntMul_Kappa_R8_Data_BitOppbankCentStarBit
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:43:02.406074+00:00
-- url     : https://prove2.me/theorems/588b4284-798f-4c32-8919-4c6fde1ff135
-- title:
--   starC bit agreement with triL
-- statement:
--   # Star masks match triple membership
--
--   For each centre index $c<23$ and each triple index $i<1771$,
--   $$
--   (\mathrm{starC}\,c).\mathrm{testBit}\,i = (\mathrm{triL}\,i).\mathrm{testBit}\,c.
--   $$
--   Proved by `decide` on `Fin 1771` for each of the twenty-three explicit star constants (no `native_decide`). This converts the Boolean support certificate $\mathrm{centredStar}$ into the geometric centre condition used by $\mathrm{HasCentre}$.
-- source:
--   R8 BitOppbank densified HasCentre / LocSlots TPTS; companion to BitOppbankCent

-- CentStarBit: starC c agrees with triL membership (Fin 1771 decide packs).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankCent
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.Cent

namespace IntMul.Kappa.R8.Bit.Oppbank.CentStarBit

theorem starC0_bit : ∀ i : Fin 1771, (starC 0).testBit i.val = (triL i.val).testBit 0 := by decide
theorem starC1_bit : ∀ i : Fin 1771, (starC 1).testBit i.val = (triL i.val).testBit 1 := by decide
theorem starC2_bit : ∀ i : Fin 1771, (starC 2).testBit i.val = (triL i.val).testBit 2 := by decide
theorem starC3_bit : ∀ i : Fin 1771, (starC 3).testBit i.val = (triL i.val).testBit 3 := by decide
theorem starC4_bit : ∀ i : Fin 1771, (starC 4).testBit i.val = (triL i.val).testBit 4 := by decide
theorem starC5_bit : ∀ i : Fin 1771, (starC 5).testBit i.val = (triL i.val).testBit 5 := by decide
theorem starC6_bit : ∀ i : Fin 1771, (starC 6).testBit i.val = (triL i.val).testBit 6 := by decide
theorem starC7_bit : ∀ i : Fin 1771, (starC 7).testBit i.val = (triL i.val).testBit 7 := by decide
theorem starC8_bit : ∀ i : Fin 1771, (starC 8).testBit i.val = (triL i.val).testBit 8 := by decide
theorem starC9_bit : ∀ i : Fin 1771, (starC 9).testBit i.val = (triL i.val).testBit 9 := by decide
theorem starC10_bit : ∀ i : Fin 1771, (starC 10).testBit i.val = (triL i.val).testBit 10 := by decide
theorem starC11_bit : ∀ i : Fin 1771, (starC 11).testBit i.val = (triL i.val).testBit 11 := by decide
theorem starC12_bit : ∀ i : Fin 1771, (starC 12).testBit i.val = (triL i.val).testBit 12 := by decide
theorem starC13_bit : ∀ i : Fin 1771, (starC 13).testBit i.val = (triL i.val).testBit 13 := by decide
theorem starC14_bit : ∀ i : Fin 1771, (starC 14).testBit i.val = (triL i.val).testBit 14 := by decide
theorem starC15_bit : ∀ i : Fin 1771, (starC 15).testBit i.val = (triL i.val).testBit 15 := by decide
theorem starC16_bit : ∀ i : Fin 1771, (starC 16).testBit i.val = (triL i.val).testBit 16 := by decide
theorem starC17_bit : ∀ i : Fin 1771, (starC 17).testBit i.val = (triL i.val).testBit 17 := by decide
theorem starC18_bit : ∀ i : Fin 1771, (starC 18).testBit i.val = (triL i.val).testBit 18 := by decide
theorem starC19_bit : ∀ i : Fin 1771, (starC 19).testBit i.val = (triL i.val).testBit 19 := by decide
theorem starC20_bit : ∀ i : Fin 1771, (starC 20).testBit i.val = (triL i.val).testBit 20 := by decide
theorem starC21_bit : ∀ i : Fin 1771, (starC 21).testBit i.val = (triL i.val).testBit 21 := by decide
theorem starC22_bit : ∀ i : Fin 1771, (starC 22).testBit i.val = (triL i.val).testBit 22 := by decide

theorem starC_bit {c : ℕ} (hc : c < 23) :
    ∀ i : Fin 1771, (starC c).testBit i.val = (triL i.val).testBit c :=
  match c, hc with
  | 0, _ => starC0_bit
  | 1, _ => starC1_bit
  | 2, _ => starC2_bit
  | 3, _ => starC3_bit
  | 4, _ => starC4_bit
  | 5, _ => starC5_bit
  | 6, _ => starC6_bit
  | 7, _ => starC7_bit
  | 8, _ => starC8_bit
  | 9, _ => starC9_bit
  | 10, _ => starC10_bit
  | 11, _ => starC11_bit
  | 12, _ => starC12_bit
  | 13, _ => starC13_bit
  | 14, _ => starC14_bit
  | 15, _ => starC15_bit
  | 16, _ => starC16_bit
  | 17, _ => starC17_bit
  | 18, _ => starC18_bit
  | 19, _ => starC19_bit
  | 20, _ => starC20_bit
  | 21, _ => starC21_bit
  | 22, _ => starC22_bit
  | k + 23, h => False.elim (Nat.not_lt_of_ge (Nat.le_add_left 23 k) h)

end IntMul.Kappa.R8.Bit.Oppbank.CentStarBit


