-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts4
-- name    : IntMul_Kappa_R8_Data_BitOppbankMoveFacts4
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:15:22.99238+00:00
-- url     : https://prove2.me/theorems/65a14d1b-cd31-4e6e-b51c-792305f6b5e3
-- title:
--   Dm 0 c idempotent + hPis0_Dm packaging
-- statement:
--   Proves $\mathrm{Dm}(0,c)^2=\mathrm{Dm}(0,c)$ for every densified code $c$, via $\mathrm{Le}(\mathrm{Pc}\,0,\mathrm{Pc}\,c)$ and $\mathrm{dimCF}\,0=0$. Packages $\mathrm{hPis0\_Dm}$ as this LOW-origin case plus Open $\mathrm{DmIdemPosOStmt}$ ($o\neq 0$).
-- source:
--   MoveFacts3; Pnd Dm/dimCF; R6 Le

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# MoveFacts4 — `Dm 0 c` idempotent + packaging toward `hPis0_Dm`
-/

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.MoveFacts4

private theorem zero_lt_codeBound : 0 < codeBound := by decide

/-- From LOW origin: `dimCF 0 = 0 ≤ dimCF c`, so `Dm 0 c` is idempotent. -/
theorem Dm_idem_o0 {c : ℕ} (hc : c < codeBound) :
    Dm 0 c * Dm 0 c = Dm 0 c := by
  have hLe : Le (Pc 0) (Pc c) := ⟨by simp [Pc_low], by simp [Pc_low]⟩
  have hdim : dimCF 0 ≤ dimCF c := by simp [dimCF]
  exact Dm_idem_le zero_lt_codeBound hc hLe hdim

/-- Open remainder for `hPis0_Dm` once `o ≠ 0`. -/
def DmIdemPosOStmt : Prop :=
  ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
    o ≠ 0 → Dm o c * Dm o c = Dm o c

theorem hPis0_Dm_of_posO (h : DmIdemPosOStmt) :
    ∀ A ∈ idxD.image (fun p => Dm p.1 p.2), A * A = A := by
  intro A hA
  obtain ⟨⟨o, c⟩, hp, rfl⟩ := Finset.mem_image.1 hA
  have hp' := (mem_idxD _).1 hp
  have ho : o < codeBound := hp'.1.1
  have hc : c < codeBound := hp'.1.2
  have hn : nestOK o c = true := hp'.2
  by_cases ho0 : o = 0
  · subst ho0; exact Dm_idem_o0 hc
  · exact h o c ho hc hn ho0

end IntMul.Kappa.R8.Bit.Oppbank.MoveFacts4


