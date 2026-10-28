-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0P
-- name    : IntMul_Kappa_R8_Data_BitOppbankNet0P
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:05:05.227189+00:00
-- url     : https://prove2.me/theorems/373d80bb-9662-4766-87e5-23207e392df8
-- title:
--   R8 BitNB net0P = QHNet.prog + ProjB.ch0P pickE
-- statement:
--   # Opp-bank network on real ProjB edges
--
--   `net0P : QHNet (ZMod 2) 104719230 3217907 529` is the densified BitOppbank
--   program from `BitOppbankQHNet` with edge families from `BitOppbankProjB.ch0P`
--   (`pickE`/`PE`/`SideR`/`DataR`/`AuxR` over densified `Pl`/`Dm`/`rkC`/`nestOK` at
--   `codeBound=64251`). Replaces QHNet's `dfltE` `ch0` and NetD's stub projectors.
-- source:
--   BitOppbankQHNet + BitOppbankProjB bridge

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Opp-bank `net0` on ProjB `ch0P` (real pickE / Pl / Dm / rkC)

Published QHNet (`52d9e9e0`) keeps program `NB.net` / densified `cs1`/`cs2` but its
own `ch0` still uses `dfltE`. Published NetD (`88df9bd7`) has pickE wiring with
**stub** Pl/Dm/rkC. ProjB (`b18c4ed9`) fills real densified projectors + `ch0P`.

This module coerces `ProjB.ch0P` into `NB.Ch` and defines
`net0P : QHNet (ZMod 2) 104719230 3217907 529 := NB.net (toNB ch0P)`.

ND `Pc` still uses `Pnd = 0` (no densified centre / `supG`); `orthOK` is the
always-true stub. Those are the remaining NetD→FormalOK gaps.
-/

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R8.Bit.Oppbank

namespace IntMul.Kappa.R8.Bit.Oppbank.Net0P

/-- Coerce ProjB edge families into the published QHNet `NB.Ch` carrier. -/
noncomputable def toNB (ch : ProjB.Ch) : NB.Ch where
  S := ch.S
  Si := ch.Si
  e1 := ch.e1
  e2 := ch.e2
  ex := ch.ex
  en := ch.en
  ei := ch.ei
  ec := ch.ec

/-- Named opp-bank network: densified BitOppbank program + ProjB `pickE`/`ch0P`. -/
noncomputable def net0P : QHNet (ZMod 2) 104719230 3217907 529 :=
  NB.net (toNB ProjB.ch0P)

theorem net0P_eq : net0P = NB.net (toNB ProjB.ch0P) := rfl
theorem net0P_W : W = 104719230 := rfl
theorem net0P_T : Tmp = 3217907 := rfl
theorem net0P_codeBound : ProjB.codeBound = 64251 := rfl

/-- Alias matching oppbank_net packaging (`⟨Tmp, net0, …⟩`). -/
noncomputable def net0 : QHNet (ZMod 2) 104719230 3217907 529 := net0P

end IntMul.Kappa.R8.Bit.Oppbank.Net0P


