-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
-- name    : IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:03:41.621474+00:00
-- url     : https://prove2.me/theorems/0299e476-22a7-41ab-8e67-f4871a744e84
-- title:
--   Unconditional Pc_idem + mem_Pis0_Dm + LOW nest / Dm_idem
-- statement:
--   Every densified code projector $\mathrm{Pc}(c)$ ($c<\mathrm{codeBound}$) is idempotent, using $\mathrm{Pnd\_idem\_all}$ on the ND branch (no $\mathrm{HasCentre}$ hypothesis).
--
--   Also: $\mathrm{mem\_Pis0\_Dm}$, LOW nest orientation ($o\le 1$ or $c\le 1$), and $\mathrm{Dm}$ idempotence under aligned $\mathrm{Le}$/$\mathrm{dimCF}$ hypotheses — steps toward full $\mathrm{move\_facts}$ and $\mathrm{hPis0}$.
-- source:
--   PndIdem 631e8adc; MoveFacts2 b43b3e76; R6 move_facts/Le

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPndIdem
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# MoveFacts3 — unconditional Pc idempotence + mem_Pis0_Dm + LOW nest

`Pnd_idem_all` ⇒ every densified `Pc` is idempotent. LOW nest orientation lemmas.
`Dm_idem` when `Le (Pc o) (Pc c)` and `dimCF o ≤ dimCF c` (or the reverse).
-/

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.PndIdem
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3

/-- Every code `< codeBound` has idempotent `Pc` (ND via `Pnd_idem_all`). -/
theorem Pc_idem {c : ℕ} (hc : c < codeBound) : Pc c * Pc c = Pc c := by
  by_cases h0 : c = 0
  · subst h0; exact Pc_idem_low
  by_cases h1 : c = 1
  · subst h1; exact Pc_idem_high
  by_cases hPT : c < 1773
  · exact Pc_idem_PT (by omega) hPT
  · have hn : 1773 + (c - 1773) < codeBound := by omega
    have : c = 1773 + (c - 1773) := by omega
    rw [this, Pc_of_ND _ hn, PndD]; exact Pnd_idem_all

theorem mem_idxD (p : ℕ × ℕ) :
    p ∈ idxD ↔ (p.1 < codeBound ∧ p.2 < codeBound) ∧ nestOK p.1 p.2 = true := by
  unfold idxD
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]

theorem mem_Pis0_Dm {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : nestOK o c = true) : Dm o c ∈ Pis0 := by
  rw [Pis0, Finset.mem_union, Finset.mem_image]
  exact Or.inl ⟨(o, c), (mem_idxD _).2 ⟨⟨ho, hc⟩, h⟩, rfl⟩

theorem nest_sound_low_o {o c : ℕ} (ho : o ≤ 1) (hc : c < codeBound) :
    Le (Pc o) (Pc c) ∨ Le (Pc c) (Pc o) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ho with rfl | rfl
  · exact Or.inl ⟨by simp [Pc_low], by simp [Pc_low]⟩
  · exact Or.inr ⟨by simp [Pc_high], by simp [Pc_high]⟩

theorem nest_sound_low_c {o c : ℕ} (ho : o < codeBound) (hc : c ≤ 1) :
    Le (Pc o) (Pc c) ∨ Le (Pc c) (Pc o) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with rfl | rfl
  · exact Or.inr ⟨by simp [Pc_low], by simp [Pc_low]⟩
  · exact Or.inl ⟨by simp [Pc_high], by simp [Pc_high]⟩

theorem Dm_idem_le {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (hLe : Le (Pc o) (Pc c)) (hdim : dimCF o ≤ dimCF c) :
    Dm o c * Dm o c = Dm o c := by
  unfold Dm; rw [if_pos hdim]
  exact le_sub_idem (Pc_idem ho) (Pc_idem hc) hLe

theorem Dm_idem_ge {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (hLe : Le (Pc c) (Pc o)) (hdim : ¬ dimCF o ≤ dimCF c) :
    Dm o c * Dm o c = Dm o c := by
  unfold Dm; rw [if_neg hdim]
  exact le_sub_idem (Pc_idem hc) (Pc_idem ho) hLe

end IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3


