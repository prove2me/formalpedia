-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNestBound
-- name    : IntMul_Kappa_R8_Data_BitOppbankNestBound
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:32:09.628862+00:00
-- url     : https://prove2.me/theorems/bd8f0507-23de-4bba-90de-07c6e77655cf
-- title:
--   NestBound: Dm idempotent on LOW/HIGH nest boundaries
-- statement:
--   On densified nest-ok pairs with a LOW or HIGH endpoint ($o\le 1$ or $c\le 1$), the move projector $\mathrm{Dm}(o,c)$ is idempotent. Uses $\mathrm{dimCF}\le 23$ from DimBound so HIGH strictly dominates every other code. Packages the interior remainder as $\mathrm{DmIdemInteriorStmt}$ toward full $\mathrm{hPis0\_Dm}$.
-- source:
--   R8 Bit Oppbank MoveFacts3/4/5 + DimBound; Track BitNB NestBound

-- NestBound: boundary Dm idempotence + packaging toward hPis0_Dm.

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts3
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts5
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-!
# NestBound — `Dm` idempotent on nestOK LOW/HIGH boundaries

Uses `DimBound.dimF_le_22` so HIGH (`dimCF = 23`) strictly dominates every other code.
-/

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts3
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts4
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts5
open IntMul.Kappa.R8.Bit.Oppbank.DimBound
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.NestBound

private theorem one_lt_cb : (1 : ℕ) < codeBound := by decide

theorem Dm_idem_o1 {c : ℕ} (hc : c < codeBound) :
    Dm 1 c * Dm 1 c = Dm 1 c := by
  by_cases hdim : dimCF 1 ≤ dimCF c
  · have : dimCF c = 23 := by
      have h1 : dimCF 1 = 23 := by simp [dimCF]
      have hle := dimCF_le_23 hc
      omega
    have hc1 : c = 1 := (dimCF_eq_23_iff hc).1 this
    subst hc1
    unfold Dm; simp [Pc_high, dimCF]
  · exact Dm_idem_ge one_lt_cb hc (Le_Pc1_right c) hdim

theorem Dm_idem_ble_o {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : o ≤ 1) : Dm o c * Dm o c = Dm o c := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with rfl | rfl
  · exact Dm_idem_from0 hc
  · exact Dm_idem_o1 hc

theorem Dm_idem_ble_c {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : c ≤ 1) : Dm o c * Dm o c = Dm o c := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with rfl | rfl
  · by_cases ho0 : o = 0
    · subst ho0; exact Dm_idem_from0 (by decide : (0 : ℕ) < codeBound)
    · have hd : 0 < dimCF o := by
        have hne0 : o ≠ 0 := ho0
        simp only [dimCF, hne0, ↓reduceIte]
        split_ifs with hEq1 hPT
        · -- o = 1 ⇒ dimCF = 23
          omega
        · -- PT code ⇒ dimCF = 22
          omega
        · -- ND code ⇒ dimF > 0
          have hn : o - 1773 < SupG.nNodes := by
            change o - 1773 < 62478
            have : codeBound = 64251 := rfl
            omega
          exact DimBound.dimF_pos (o - 1773) hn
      exact Dm_idem_to0_of_posdim ho hd
  · exact Dm_idem_to1_of_dim_le ho (dimCF_le_23 ho)

/-- Boundary half of nestOK. -/
theorem Dm_idem_boundary {o c : ℕ} (ho : o < codeBound) (hc : c < codeBound)
    (h : o ≤ 1 ∨ c ≤ 1) : Dm o c * Dm o c = Dm o c := by
  rcases h with h | h
  · exact Dm_idem_ble_o ho hc h
  · exact Dm_idem_ble_c ho hc h

/-- Interior remainder (ND–ND / ND–PT nests). -/
def DmIdemInteriorStmt : Prop :=
  ∀ o c, o < codeBound → c < codeBound → nestOK o c = true →
    ¬ o ≤ 1 → ¬ c ≤ 1 → Dm o c * Dm o c = Dm o c

theorem hPis0_Dm_of_interior (hInt : DmIdemInteriorStmt) :
    ∀ A ∈ idxD.image (fun p => Dm p.1 p.2), A * A = A := by
  intro A hA
  obtain ⟨⟨o, c⟩, hp, rfl⟩ := Finset.mem_image.1 hA
  have hp' := (mem_idxD _).1 hp
  have ho : o < codeBound := hp'.1.1
  have hc : c < codeBound := hp'.1.2
  have hn : nestOK o c = true := hp'.2
  by_cases hble : o ≤ 1 ∨ c ≤ 1
  · exact Dm_idem_boundary ho hc hble
  · have ho1 : ¬ o ≤ 1 := fun h => hble (Or.inl h)
    have hc1 : ¬ c ≤ 1 := fun h => hble (Or.inr h)
    exact hInt o c ho hc hn ho1 hc1

end IntMul.Kappa.R8.Bit.Oppbank.NestBound


