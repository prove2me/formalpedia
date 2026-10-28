-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNet0Pnd
-- name    : IntMul_Kappa_R8_Data_BitOppbankNet0Pnd
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T07:30:53.362995+00:00
-- url     : https://prove2.me/theorems/ecd62ac2-b1d5-4169-96cb-80839f572e87
-- title:
--   R8 net0Pnd with Pnd.ch0P
-- statement:
--   # Network with honest densified Pnd edges
--
--   The opp-bank QH-network $\mathrm{net0Pnd}=\mathrm{NB.net}(\mathrm{toNB}\,\mathrm{Pnd.ch0P})$
--   over the densified BitOppbank program, using honest ND projectors.
-- source:
--   Track A

-- Opp-bank net0 on densified-Pnd ch0P (honest ND Pc).

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# `net0Pnd` — densified program + honest `Pnd`/`ch0P`

Rewires Track A away from stub-`Pc` ProjB/NetD: uses `Pnd.ch0P` whose ND
projectors are Defs51 `NB.Pnd ∘ densSupG`. Coerces into published `NB.Ch` /
`NB.net` for `oppbank_net` packaging.
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

/-- Named opp-bank network with honest densified ND projectors. -/
noncomputable def net0Pnd : QHNet (ZMod 2) 104719230 3217907 529 :=
  NB.net (toNB Pnd.ch0P)

noncomputable def net0 : QHNet (ZMod 2) 104719230 3217907 529 := net0Pnd

theorem net0Pnd_eq : net0Pnd = NB.net (toNB Pnd.ch0P) := rfl
theorem net0_W : W = 104719230 := rfl
theorem net0_T : Tmp = 3217907 := rfl
theorem codeBound_eq : SupG.codeBound = 64251 := rfl

/-- Bridge lemma: ND `Pc` is `NB.Pnd` on densified support (not `0`). -/
theorem Pc_eq_PndD (n : ℕ) (hn : 1773 + n < SupG.codeBound) :
    Pnd.Pc (1773 + n) = Pnd.PndD n :=
  Pnd.Pc_of_ND n hn

end IntMul.Kappa.R8.Bit.Oppbank.Net0Pnd


