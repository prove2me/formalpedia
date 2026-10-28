-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
-- name    : IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:49:47.629537+00:00
-- url     : https://prove2.me/theorems/3f441284-58c5-4be2-8c94-1dcf8ce8f717
-- title:
--   EOKO package on corrected OneRun2 carrier
-- statement:
--   # EOKO on the corrected one-run carrier
--
--   Retarget of the densified edge-OK package $\mathrm{EOKO}$ from the legacy padded `OneRun` predicate to **OneRun2**, where each residual of rank $r$ is a single Bruhat child of width $r$:
--
--   $$
--   \mathrm{oneRun}\,r\,\mathrm{rs}\ :\Longleftrightarrow\ 0<r<529\ \wedge\ \mathrm{rs}=[(0,0,r)].
--   $$
--
--   Defines `GoodM`, structure `EOKO`, channel `ch0NB := toNB ch0O`, and packaging statements `EOKOLargeStmt` / `FormalOKOfEOKOStmt` for $\mathrm{net0O}$ at $W=104719230$, $T=3217907$, $m=529$, $\mathrm{codeBound}=64251$.
--
--   **Formalization Note.** Namespace `IntMul.Kappa.R8.Bit.Oppbank.EOKO2`; imports `BitOppbankOneRun2`.
-- source:
--   OneRun2 e0d447f6; EOKOPack 76603340 retarget; Jain bit_hist.onerun_hist

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-!
# Densified EOKO2 for corrected OneRun2 carrier

Same EOKO package on OneRun2 (`oneRun` = single width-r child, no pads).
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.EOKO2

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R6.Bit.QHNet (FormalOK)
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2
open Matrix

/-- Local copy of R6 Defs51 `GoodM` (avoid heavy Defs51 import). -/
def GoodM (N : ℕ) {l p : Type*} [Fintype l] [Fintype p]
    (A : Matrix l p ℚ) : Prop :=
  ∀ i j, Nat.Coprime (A i j).den N

/-- Densified edge-OK hypotheses at field size `N` (`SupG.codeBound = 64251`). -/
structure EOKO (ch : NB.Ch) (N : ℕ) : Prop where
  hS : ch.S * ch.Si = 1
  hSi : ch.Si * ch.S = 1
  gS : GoodM N ch.S
  gSi : GoodM N ch.Si
  gPc : ∀ c < SupG.codeBound, GoodM N (Pc c)
  gPl : ∀ b < 1771, GoodM N (Pl b)
  m1 : ∀ b < 1771, ∀ o < SupG.codeBound, ∀ c < SupG.codeBound, nestOK o c = true →
    edgeMat N (ch.e1 b o c) = redM N (pswQ (K ch.S ch.Si (Dm o c) (Pl b)))
  m2 : ∀ a < 1771, ∀ o < SupG.codeBound, ∀ c < SupG.codeBound, nestOK o c = true →
    edgeMat N (ch.e2 a o c) = redM N (pswQ (K ch.S ch.Si (Pl a) (Dm o c)))
  mx : ∀ b < 1771, edgeMat N (ch.ex b) = redM N (pswQ (K ch.S ch.Si 1 (1 - Pl b)))
  mn : ∀ a < 1771, ∀ t < 1771, edgeMat N (ch.en a t) =
    redM N (pswQ (K ch.S ch.Si (1 - Pl a) (1 - Pl t)))
  mi : ∀ a < 1771, edgeMat N (ch.ei a) = redM N (pswQ (K ch.S ch.Si (1 - Pl a) 1))
  mc : ∀ a < 1771, ∀ s < 1771, edgeMat N (ch.ec a s) =
    redM N (pswQ (K ch.S ch.Si (Pl a) (Pl s)))

theorem codeBound_eq : SupG.codeBound = 64251 := rfl

noncomputable def ch0NB : NB.Ch := toNB ch0O

def EOKOLargeStmt : Prop :=
  ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f, EOKO ch0NB (q ^ f)

def FormalOKOfEOKOStmt : Prop :=
  ∀ N, EOKO ch0NB N → FormalOK (m := 529) net0O N

end IntMul.Kappa.R8.Bit.Oppbank.EOKO2


