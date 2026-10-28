-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0PndB
-- name    : IntMul_Kappa_R8_Data_BitOppbankNet0PndB
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:32:43.57923+00:00
-- url     : https://prove2.me/theorems/b6cfc582-ab5d-42b3-a636-829645ad97a6
-- title:
--   R8 net0PndB: QHNet on honest Pnd.ch0P (Pnd published)
-- statement:
--   Opp-bank network with densified honest ND projectors:
--   $$\mathrm{net0Pnd}=\mathrm{NB.net}(\mathrm{toNB}(\mathrm{Pnd.ch0P})),$$
--   at $W=104719230$, $T=3217907$, $m=529$, $\mathrm{codeBound}=64251$. Uses published `BitOppbankPnd` ($1351eb81$) so ND `Pc` is `NB.Pnd\circ\mathrm{densSupG}`, not the zero stub.
-- source:
--   Pnd 1351eb81; Net0P 373d80bb; MomPack cddcbe7a; GoodPrimes fac3e30f; NetMom 84ad4683

-- Opp-bank net0 on densified-Pnd ch0P (honest ND Pc).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# `net0Pnd` — densified program + honest `Pnd.ch0P`

Uses published self-contained `BitOppbankPnd` (HasCentre/orthOK/Pnd on densSupG).
Coerces into `NB.Ch` / `NB.net` for Track A `net0_ok` with GoodPrimes/NetMom/NetFB.
-/

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank

namespace IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd

noncomputable def toNB (ch : Pnd.Ch) : NB.Ch where
  S := ch.S
  Si := ch.Si
  e1 := ch.e1
  e2 := ch.e2
  ex := ch.ex
  en := ch.en
  ei := ch.ei
  ec := ch.ec

noncomputable def net0Pnd : QHNet (ZMod 2) 104719230 3217907 529 :=
  NB.net (toNB Pnd.ch0P)

noncomputable def net0 : QHNet (ZMod 2) 104719230 3217907 529 := net0Pnd

theorem net0Pnd_eq : net0Pnd = NB.net (toNB Pnd.ch0P) := rfl
theorem net0_W : W = 104719230 := rfl
theorem net0_T : Tmp = 3217907 := rfl
theorem codeBound_eq : SupG.codeBound = 64251 := rfl

end IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd


