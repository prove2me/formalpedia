-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun
-- name    : IntMul_Kappa_R8_Data_BitOppbankOneRun
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:40:19.920774+00:00
-- url     : https://prove2.me/theorems/b652717e-648c-467d-82af-33994253165c
-- title:
--   R8 opp-bank one-run edge families (bitR8-compatible)
-- statement:
--   # One-run opp-bank edges
--
--   Jain's opposite-bank recompile (PR #104) turns each residual of rank $r$ into one contiguous child of width $r$. The R6 predicates $\mathrm{SideR}/\mathrm{DataR}/\mathrm{AuxR}$ emit only odd widths and cannot match $\mathrm{Jain.bitR8}$ (which has even widths); that mismatch was disproved as `Oppbank.mom_eq` on `net0P`.
--
--   This definition introduces the one-run predicate and the densified network
--   $$\mathrm{net0O}:\mathrm{QHNet}(\mathbb{Z}/2\mathbb{Z},\,104719230,\,3217907,\,529)$$
--   with `Pnd` projectors and one-run edge families for packaging `oppbank_net`.
-- source:
--   Jain round8-oppbank bit_hist.onerun_hist; icekylinx PR #104

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankWireLayout
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.dupNamespace false

/-!
# Opp-bank one-run edge families (Jain PR #104 / bit_hist.onerun_hist)

R6 `SideR`/`DataR`/`AuxR` were disproved as a match for `Jain.bitR8` (even widths).
Opposite-bank orders compile each residual of rank `r` as one contiguous run of width `r`.

`ch0O` / `net0O` retarget densified `Pnd` projectors onto one-run predicates for
`oppbank_net` packaging.
-/

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open Matrix
open scoped Kronecker

namespace IntMul.Kappa.R8.Bit.Oppbank.OneRunNet

open Pnd
def codeBound : ℕ := 64251

/-- One contiguous Bruhat run of width `r` (opp-bank child of rank `r`). -/
def oneRun (r : ℕ) (rs : List (ℕ × ℕ × ℕ)) : Prop :=
  ∃ rs', rs = (0, 0, r) :: rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧ rs'.length + 1 = r

def PE (q : Matrix (Fin 529) (Fin 529) ℚ) (R : List (ℕ × ℕ × ℕ) → Prop)
    (e : Edge 529) : Prop :=
  EdgeQ e q ∧ R e.runs

def dfltE : Edge 529 := ⟨1, [], 1⟩

open Classical in
noncomputable def pickE (P : Edge 529 → Prop) : Edge 529 :=
  if h : ∃ e, P e then Classical.choose h else dfltE

/-- Opp-bank `ch0` with one-run predicates. -/
noncomputable def ch0O : Pnd.Ch where
  S := S0
  Si := Si0
  e1 b o c :=
    if b < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0 Si0 (Dm o c) (Pl b)) (oneRun (rkC o c)))
    else dfltE
  e2 a o c :=
    if a < v ∧ o < codeBound ∧ c < codeBound then
      pickE (PE (K S0 Si0 (Pl a) (Dm o c)) (oneRun (rkC o c)))
    else dfltE
  ex b :=
    if b < v then pickE (PE (K S0 Si0 1 (1 - Pl b)) (oneRun 22)) else dfltE
  en a t :=
    if a < v ∧ t < v then
      pickE (PE (K S0 Si0 (1 - Pl a) (1 - Pl t)) (oneRun 484))
    else dfltE
  ei a :=
    if a < v then pickE (PE (K S0 Si0 (1 - Pl a) 1) (oneRun 22)) else dfltE
  ec a s :=
    if a < v ∧ s < v then pickE (PE (K S0 Si0 (Pl a) (Pl s)) (oneRun 1)) else dfltE

noncomputable def toNB (ch : Pnd.Ch) : NB.Ch where
  S := ch.S
  Si := ch.Si
  e1 := ch.e1
  e2 := ch.e2
  ex := ch.ex
  en := ch.en
  ei := ch.ei
  ec := ch.ec

noncomputable def net0O : QHNet (ZMod 2) 104719230 3217907 529 :=
  NB.net (toNB ch0O)

noncomputable def net0 : QHNet (ZMod 2) 104719230 3217907 529 := net0O

theorem net0O_T : Tmp = 3217907 := rfl
theorem net0O_W : W = 104719230 := rfl
theorem codeBound_eq : codeBound = 64251 := rfl

theorem runOK_origin {r : ℕ} (hr : 0 < r) (hrm : r < 529) :
    RunOK 529 (0, 0, r) := by
  refine ⟨hr, hrm, ?_, ?_⟩
  · simpa using (by omega : 0 + r ≤ 529)
  · simpa using (by omega : 0 + r ≤ 529)

end IntMul.Kappa.R8.Bit.Oppbank.OneRunNet


