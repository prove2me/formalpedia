-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
-- name    : IntMul_Kappa_R8_Data_BitOppbankWireLayout
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:31:29.618872+00:00
-- url     : https://prove2.me/theorems/f9c686c7-621c-4b73-a377-1413237cf8a3
-- title:
--   R8 opp-bank wire layout maps g1/g2 (NR=27794)
-- statement:
--   # Round-eight bit-network wire layout
--
--   This module retargets the round-six BitNB local/global wiring
--   (`NR`, `wX`/`wY`/`wS`/`wT`, `g1`/`g2`, merge $\rho_n$) from aux-slot count
--   $R=40077$ to the R7/R8 schedule value $R=27794$, with role count
--   $W=2N+2vR=104719230$ and temporary budget $T=3217907$.
--
--   These maps are the geometry half of a `Defs52`-style `net` assembly. Packed
--   GenData/Loc/ChkBit tables remain blocked on regenerating slot indices
--   (`injS`/`retS` reach $40076$ in R6 LocData and do not fit $R=27794$).
-- source:
--   Geometry identities as Prove2me IntMul_Kappa_R6_Defs52 / Defs51; R=27794 from Jain certificate_round7 witness 2; constants IntMul_Kappa_R8_Data_BitOppbankConsts.

import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R8 opp-bank local/global wire layout (`NR = 27794`)

Retarget of R6 BitNB maps (`Defs51`/`Defs52`: `NR`, `wX`/`wY`/`wS`/`wT`, `g1`/`g2`)
to the R7/R8 aux-slot count. Numerals match published
`IntMul_Kappa_R8_Data_BitOppbankConsts` (`W = 104719230`, `T = 3217907`, `m = 529`).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank

def h : ℕ := 23
def v : ℕ := 1771
def NR : ℕ := 27794
def N : ℕ := 3136441
def W : ℕ := 104719230
def Tmp : ℕ := 3217907
def wEnt : ℕ := 3542
def wAuxEnd : ℕ := 31336
def NL : ℕ := 31359

def wX (t : ℕ) : ℕ := t
def wY (T : ℕ) : ℕ := v + T
def wS (q : ℕ) : ℕ := wEnt + q
def wT (c : ℕ) : ℕ := wAuxEnd + c
def wU (s : ℕ) : ℕ := NL + s

def IsSlot (w : ℕ) : Prop := wEnt ≤ w ∧ w < wAuxEnd
def IsTgt (w : ℕ) : Prop := v ≤ w ∧ w < wEnt

/-- Stage-one local→global role map. -/
def g1 (b w : ℕ) : ℕ :=
  if w < v then w * v + b
  else if w < wEnt then N + (w - v) * v + b
  else if w < wAuxEnd then 2 * N + b * NR + (w - wEnt)
  else W + h * b + (w - wAuxEnd)

/-- Stage-two local→global role map. -/
def g2 (a w : ℕ) : ℕ :=
  if w < v then N + a * v + w
  else if w < wEnt then a * v + (w - v)
  else if w < wAuxEnd then 2 * N + v * NR + a * NR + (w - wEnt)
  else if w < NL then W + h * v + h * a + (w - wAuxEnd)
  else W + 2 * h * v + a * v + (w - NL)

/-- Merge on the first `2N` roles. -/
def ρn (g : ℕ) : ℕ :=
  if g < N then g + N else if g < 2 * N then g - N else g

theorem NR_eq : NR = 27794 := rfl
theorem W_eq : W = 2 * N + 2 * v * NR := by decide
theorem wAuxEnd_eq : wAuxEnd = wEnt + NR := by decide
theorem NL_eq : NL = wAuxEnd + h := by decide

end IntMul.Kappa.R8.Bit.Oppbank


