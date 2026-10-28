-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
-- name    : IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T17:00:26.283986+00:00
-- url     : https://prove2.me/theorems/b43b3e76-22ed-4ea5-bfb7-8f5449404ed8
-- title:
--   le_sub_idem / mem_Pis0_Pl / Pc_idem_<1773 / hPis0_Pl
-- statement:
--   Port of round-six nested-idempotent lemmas toward full $\mathrm{move\_facts}$ / $\mathrm{hPis0}$ on densified opp-bank codes.
--
--   Proves $\mathrm{Le}$-difference idempotence $(\mathrm{le\_sub\_idem})$, $\mathrm{Pl}\,b\in\mathrm{Pis0}$, unified $\mathrm{Pc}$-idempotence for $c<1773$, and the Pl-branch of $\mathrm{hPis0}$. Full $\mathrm{hPis0}$ reduces to idempotence of densified $\mathrm{Dm}$ images (`hPis0_of_Dm`).
-- source:
--   R6 le_sub_idem/Le; Pnd Pis0; NetFB Pl_idem; MoveFacts Pc_idem_*

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# MoveFacts2 — le_sub_idem, mem_Pis0_Pl, Pc_idem_<1773, hPis0_Pl

Port of R6 idempotent-difference lemmas toward full `move_facts` / `hPis0`.
ND `Dm` still needs `AllDensCentred` + `nest_sound`.
-/

open Matrix

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.NetFB
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2

/-- Nested idempotents (R6 `Le`): `B` dominates `A`. -/
def Le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) : Prop := B * A = A ∧ A * B = A


/-- Difference of nested idempotents is idempotent (R6 `le_sub_idem`). -/
theorem le_sub_idem {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ}
    (hA : A * A = A) (hB : B * B = B) (h : Le A B) :
    (B - A) * (B - A) = B - A := by
  obtain ⟨h1, h2⟩ := h
  rw [sub_mul, mul_sub, mul_sub, hA, hB, h1, h2]; abel

theorem mem_Pis0_Pl {b : ℕ} (hb : b < 1771) : Pl b ∈ Pis0 := by
  rw [Pis0, Finset.mem_union]
  exact Or.inr (Finset.mem_image_of_mem _ (Finset.mem_range.2 hb))

theorem mem_Lab0 {T : ℕ} (hT : T < 1771) : (xv T, yv T) ∈ Lab0 := by
  unfold Lab0
  exact Finset.mem_image_of_mem _ (Finset.mem_range.2 hT)

/-- Unified `Pc` idempotence on LOW/HIGH/PT (`c < 1773`). -/
theorem Pc_idem_lt_1773 {c : ℕ} (hc : c < 1773) : Pc c * Pc c = Pc c := by
  rcases c with _ | c
  · exact Pc_idem_low
  · rcases c with _ | c
    · exact Pc_idem_high
    · exact Pc_idem_PT (by omega) (by omega)

/-- Pl-part of `hPis0` (full `hPis0` still needs Dm via move_facts). -/
theorem hPis0_Pl : ∀ A ∈ (Finset.range 1771).image Pl, A * A = A := by
  intro A hA
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hA
  exact Pl_idem (Finset.mem_range.1 hT)

/-- Packaging: Pl branch of Pis0 is idempotent. -/
theorem hPis0_of_Dm
    (hDm : ∀ A ∈ idxD.image (fun p => Dm p.1 p.2), A * A = A) :
    ∀ A ∈ Pis0, A * A = A := by
  intro A hA
  rw [Pis0, Finset.mem_union] at hA
  rcases hA with h | h
  · exact hDm A h
  · exact hPis0_Pl A h

end IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2


