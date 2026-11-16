-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2Rec
-- name    : IntMul_Kappa_R8_Data_BitOppbankEOKOPack2Rec
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T07:17:10.160648+00:00
-- url     : https://prove2.me/theorems/8ba6deb1-aa9a-4e91-9f28-109102005a6a
-- title:
--   EOKO package on corrected OneRun2Rec carrier (QHNetRec)
-- statement:
--   # Densified `EOKO` package on `OneRun2Rec`
--
--   This is a `QHNetRec` fork of the published package `IntMul_Kappa_R8_Data_BitOppbankEOKOPack2`. The edge-OK hypotheses are unchanged: for a channel \(ch\) and a field size \(N\), the structure \(\mathrm{EOKO}(ch,N)\) asserts invertibility and coprimality of the flag bases together with the six densified edge-matrix identities
--
--   $$
--   \mathrm{edgeMat}_N(ch.e_\ast)=\mathrm{redM}_N\bigl(\mathrm{pswQ}(K(ch.S,ch.Si,\ldots))\bigr)
--   $$
--
--   at \(\mathrm{codeBound}=64251\), on the corrected one-run carrier (`oneRun` is a single width-\(r\) child, with no pads).
--
--   The packaged statements
--
--   $$
--   \mathrm{EOKOLargeStmt},\qquad \mathrm{FormalOKOfEOKOStmt}
--   $$
--
--   are likewise unchanged, now taking \(\mathrm{ch0NB}=\mathrm{toNB}(\mathrm{ch0O})\) and \(\mathrm{net0O}\) from `IntMul_Kappa_R8_Data_BitOppbankOneRun2Rec`. That carrier imports the total-decoder network `QHNetRec`, so later densify lemmas may use this package together with `QHNetRec` without mixing the parent `OneRun2` / `QHNet` modules.
--
--   **Formalization Note.** The Lean namespace remains `IntMul.Kappa.R8.Bit.Oppbank.EOKO2`. Do not import both `BitOppbankEOKOPack2` and `BitOppbankEOKOPack2Rec` in one file, and do not import both `BitOppbankQHNet` and `BitOppbankQHNetRec`. This definition does not close or replace `3f441284-58c5-4be2-8c94-1dcf8ce8f717`.
-- source:
--   Fork of published definition IntMul_Kappa_R8_Data_BitOppbankEOKOPack2 (definition_id 3f441284-58c5-4be2-8c94-1dcf8ce8f717, created 2026-10-28): same densified EOKO hypotheses and FormalOK/EOKOLarge statement abbreviations on the corrected OneRun2 carrier (single width-r child, no pads), retargeted to import IntMul_Kappa_R8_Data_BitOppbankOneRun2Rec (definition_id a4df37e2-2ae8-4bb8-816e-808fb4f5e6f8, created 2026-11-15) instead of IntMul_Kappa_R8_Data_BitOppbankOneRun2 (definition_id e0d447f6-cd60-4e42-86c4-534cc0c33db5). Parent source: OneRun2 e0d447f6; EOKOPack 76603340 retarget; Jain bit_hist.onerun_hist. Local source: Definitions/Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2Rec.lean (0-sorry).

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2Rec
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-!
# Densified EOKO2 for corrected OneRun2Rec carrier (QHNetRec)

Same EOKO package on OneRun2Rec (`oneRun` = single width-r child, no pads).
This is the QHNetRec fork of `BitOppbankEOKOPack2`: the `EOKO` hypotheses,
`ch0NB`, and statement abbreviations are unchanged, but the carrier import is
`BitOppbankOneRun2Rec` (which imports `BitOppbankQHNetRec`) rather than
`BitOppbankOneRun2`. Do not import both EOKOPack2 and EOKOPack2Rec (same
`EOKO2` namespace), and do not import both QHNet and QHNetRec, in one file.
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


