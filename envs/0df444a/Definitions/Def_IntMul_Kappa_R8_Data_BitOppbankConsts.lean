-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankConsts
-- name    : IntMul_Kappa_R8_Data_BitOppbankConsts
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:27:40.77137+00:00
-- url     : https://prove2.me/theorems/f40ce27e-6c62-4b43-993e-2da3b1e58511
-- title:
--   R8 / R7-plain bit QHNet geometry constants (opp-bank)
-- statement:
--   # Round-eight bit-network geometry constants
--
--   This module records the **role / temporary / wire layout integers** for Jain's round-seven witness 2 bit schedule at frame height $h=23$, as reused by the round-eight opposite-bank compile.
--
--   With $v=1771$ invocations and aux-slot block $R=27794$ (versus $R=40077$ in the published round-six BitNB network), the same identities used by R6 BitNB give
--   $$
--   N=v^2,\qquad W=2N+2vR=104719230,\qquad T=46v+N=3217907,\qquad m=h^2=529.
--   $$
--   Local wire cut-points are $w_{\mathrm{ent}}=2v$, $w_{\mathrm{aux}}=2v+R$, and $w_{U_0}=2v+R+h$. The merge map $\rho_n$ swaps the first $2N$ roles exactly as in R6.
--
--   These constants are the geometry half of a BitNB transplant targeting `BitNetMomStmtG 104719230 529 Jain.bitR8` (and the sister plain histogram). Packed stage words / Loc / ChkBit tables are **not** included here: R6 LocData hardcodes `NR=40077` and must be regenerated for $R=27794$.
-- source:
--   Swapnil Jain, integer-mult-kappa (certificates/round7 witness 2; independent/round8-oppbank bit_hist.py); geometry identities as in Prove2me IntMul_Kappa_R6_Defs52 (xuanji R6 BitNB).

import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Round-eight / R7-plain bit network geometry constants (opp-bank target)

Derived from Jain `integer-mult-kappa` frozen round-seven witness 2
(`certificates/round7/` via `certificate_round7.build`) with the same role-count
identity used by R6 BitNB:

`W = 2N + 2vR`, `T = 46v + N`, `m = h^2`, `N = v^2`.

For the R7/R8 schedule one has `h = 23`, `v = 1771`, `R = 27794`, hence
`W = 104719230` and `T = 3217907` (same temporary budget as R6; only the aux-slot
block `R` shrinks relative to R6's `R = 40077`).

These constants are the geometry half of an R8 BitNB transplant. Packed
`SG*` / `GREC` / `ChkBit*` tables still require the skeleton-subtraction generator
retargeted to `R = 27794` (R6 LocData hardcodes `NR = 40077`).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank

/-- Frame height `h` (square frame `m = h^2`). -/
def h : ℕ := 23

/-- Triple / invocation count `v`. -/
def v : ℕ := 1771

/-- Aux-slot block size `R` (R7/R8 deferred schedule; R6 used `40077`). -/
def Rslots : ℕ := 27794

/-- `N = v^2`. -/
def N : ℕ := 3136441

/-- Child-frame width `m = h^2`. -/
def m : ℕ := 529

/-- Role count `W = 2N + 2vR`. -/
def W : ℕ := 104719230

/-- Temporary budget `T = 46v + N`. -/
def T : ℕ := 3217907

/-- First local wire after the two length-`v` entrance blocks (`= 2v`). -/
def wEnt : ℕ := 3542

/-- End of aux-slot local wires (`= 2v + R`). -/
def wAuxEnd : ℕ := 31336

/-- Base index of local `u_S` wires (`= 2v + R + h`). -/
def wU0 : ℕ := 31359

theorem N_eq : N = v * v := by decide
theorem m_eq : m = h * h := by decide
theorem W_eq : W = 2 * N + 2 * v * Rslots := by decide
theorem T_eq : T = 46 * v + N := by decide
theorem wAuxEnd_eq : wAuxEnd = wEnt + Rslots := by decide
theorem wU0_eq : wU0 = wAuxEnd + h := by decide

/-- Target platform moment width (roles) for `BitNetMomStmtG` / `oppbank_net`. -/
theorem W_target : W = 104719230 := by decide

theorem m_target : m = 529 := by decide

/-- Merge permutation on the first `2N` roles (same shape as R6 `ρn`). -/
def ρn (g : ℕ) : ℕ :=
  if g < N then g + N else if g < 2 * N then g - N else g

end IntMul.Kappa.R8.Bit.Oppbank


