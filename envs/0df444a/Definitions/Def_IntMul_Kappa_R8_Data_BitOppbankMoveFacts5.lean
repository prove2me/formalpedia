-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts5
-- name    : IntMul_Kappa_R8_Data_BitOppbankMoveFacts5
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:26:45.763634+00:00
-- url     : https://prove2.me/theorems/9682605f-6252-486f-a4b4-43dd4112d637
-- title:
--   R8 Oppbank MoveFacts5 boundary Dm to0/to1/from0
-- statement:
--   Boundary move-projector lemmas: $\mathrm{Dm}(0,c)$ is idempotent; $\mathrm{Dm}(o,0)$ when $\dim\mathrm{CF}(o)>0$; $\mathrm{Dm}(o,1)$ when $\dim\mathrm{CF}(o)\le 23$. Feeds nestOK LOW/HIGH half of $h\mathrm{Pis0\_Dm}$.
-- source:
--   MoveFacts3 Dm_idem_le/ge; MoveFacts4 Dm_idem_o0.

-- MoveFacts5: clean boundary Dm idempotence lemmas.

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# MoveFacts5 — `Dm` from LOW / to HIGH (dim-bounded)
-/

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts4
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.MoveFacts5

private theorem zero_lt_cb : (0 : ℕ) < codeBound := by decide
private theorem one_lt_cb : (1 : ℕ) < codeBound := by decide

theorem Le_Pc0_left (c : ℕ) : Le (Pc 0) (Pc c) :=
  ⟨by simp [Pc_low], by simp [Pc_low]⟩

theorem Le_Pc1_right (c : ℕ) : Le (Pc c) (Pc 1) :=
  ⟨by simp [Pc_high], by simp [Pc_high]⟩

theorem Dm_idem_from0 {c : ℕ} (hc : c < codeBound) :
    Dm 0 c * Dm 0 c = Dm 0 c :=
  Dm_idem_o0 hc

theorem Dm_idem_to0_of_posdim {o : ℕ} (ho : o < codeBound) (hd : 0 < dimCF o) :
    Dm o 0 * Dm o 0 = Dm o 0 := by
  have hdim : ¬ dimCF o ≤ dimCF 0 := by
    have : dimCF 0 = 0 := by simp [dimCF]
    omega
  exact Dm_idem_ge ho zero_lt_cb (Le_Pc0_left o) hdim

theorem Dm_idem_to1_of_dim_le {o : ℕ} (ho : o < codeBound) (hd : dimCF o ≤ 23) :
    Dm o 1 * Dm o 1 = Dm o 1 := by
  have hdim : dimCF o ≤ dimCF 1 := by
    simpa [show dimCF 1 = 23 from (by simp [dimCF])] using hd
  exact Dm_idem_le ho one_lt_cb (Le_Pc1_right o) hdim

theorem Dm_idem_to1_lt_1773 {o : ℕ} (ho : o < 1773) :
    Dm o 1 * Dm o 1 = Dm o 1 := by
  have hc : o < codeBound := lt_trans ho (by decide : (1773 : ℕ) < codeBound)
  have hd : dimCF o ≤ 23 := by
    simp only [dimCF]; split_ifs <;> omega
  exact Dm_idem_to1_of_dim_le hc hd

theorem Dm_idem_o_eq_zero {c : ℕ} (hc : c < codeBound) :
    Dm 0 c * Dm 0 c = Dm 0 c :=
  Dm_idem_from0 hc

end IntMul.Kappa.R8.Bit.Oppbank.MoveFacts5


