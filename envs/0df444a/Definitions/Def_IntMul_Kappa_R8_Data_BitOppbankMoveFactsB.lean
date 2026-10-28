-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFactsB
-- name    : IntMul_Kappa_R8_Data_BitOppbankMoveFactsB
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T16:57:50.244909+00:00
-- url     : https://prove2.me/theorems/fb2e38ad-3821-4b30-a48c-47ce3fad0365
-- title:
--   Move/projector idempotence feed toward hPis0 / FB0_ex (B)
-- statement:
--   Idempotence lemmas for densified opp-bank projectors toward full $\mathrm{hPis0}$ / $\mathrm{FB0\_ex}$ (republish of MoveFacts content).
--
--   Proves $(1-P)^2=1-P$ from $P^2=P$, idempotence of $\mathrm{prjM}$, $\mathrm{Pnd}(\mathrm{sup})$ when $\mathrm{HasCentre}$, and $\mathrm{Pc}$ on LOW/HIGH/PT/ND branches.
-- source:
--   Jain R8; Pnd 1351eb81; NetFB cb08d016; R6 move_facts pattern

-- Densified Pc/Pl idempotence feed (PT/LOW/HIGH); ND Pnd_idem companion stmt.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# Move facts (PT/LOW/HIGH) toward full `hPis0`

`Pc_idem` on codes `< 1773` via NetFB `Pl_idem`. ND idempotence packaged as `PndIdemStmt`.
-/

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetFB
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.MoveFacts

theorem one_sub_idem {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (h : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  rw [sub_mul, mul_sub, mul_sub, h]; simp

theorem Pc_low : Pc 0 = 0 := by simp [Pc]
theorem Pc_high : Pc 1 = 1 := by simp [Pc]
theorem Pc_idem_low : Pc 0 * Pc 0 = Pc 0 := by simp [Pc_low]
theorem Pc_idem_high : Pc 1 * Pc 1 = Pc 1 := by simp [Pc_high]

theorem Pc_idem_PT {c : ℕ} (_h1 : 2 ≤ c) (h2 : c < 1773) :
    Pc c * Pc c = Pc c := by
  have hP : Pc c = 1 - Pl (c - 2) := by
    simp [Pc, show c ≠ 0 by omega, show c ≠ 1 by omega, h2]
  rw [hP]
  exact one_sub_idem (Pl_idem (T := c - 2) (by omega))

/-- Package: centred densified supports give idempotent `Pnd`. -/
def PndIdemStmt : Prop :=
  ∀ {sup : ℕ}, HasCentre sup → Pnd sup * Pnd sup = Pnd sup

def AllDensCentred : Prop := ∀ n < nNodes, HasCentre (densSupG n)

def PcIdemNDStmt : Prop :=
  ∀ n, 1773 + n < codeBound → HasCentre (densSupG n) →
    Pc (1773 + n) * Pc (1773 + n) = Pc (1773 + n)

end IntMul.Kappa.R8.Bit.Oppbank.MoveFacts


