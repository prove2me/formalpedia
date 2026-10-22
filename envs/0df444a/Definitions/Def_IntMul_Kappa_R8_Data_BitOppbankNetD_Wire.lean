-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetD_Wire
-- name    : IntMul_Kappa_R8_Data_BitOppbankNetD_Wire
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:06:35.663776+00:00
-- url     : https://prove2.me/theorems/54e37bf3-dc3c-4a3e-b324-9f3135d46275
-- title:
--   R8 NetD wires ProjB+DagC into QHNet net0D + RunOK lemmas
-- statement:
--   Wires published densified projectors `BitOppbankProjB` ($b18c4ed9$) and DagC packs into the opp-bank QHNet program: $\mathrm{net0D}=\mathrm{net}(\mathrm{toNB}(\mathrm{ch0P}))$ on $W=104719230$, $T=3217907$, $m=529$, $\mathrm{codeBound}=64251$.
--
--   Also records `RunOK` lemmas for Defs52 run classes (`auxRuns 19`, `dataRuns 23 529`, `sideRuns 23 529 r` for $r\le 23$) and `AuxR`/`dfltE`, as pieces toward `net0_ok`.
-- source:
--   ProjB b18c4ed9; ChkBitArg e96b5336; ChkBitDagC 47a4be0b; QHNet 52d9e9e0

import Mathlib
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankChkBitDagC

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

/-!
# R8 opp-bank NetD — wire `ProjB` + DagC into published `QHNet`

`BitOppbankProjB` (`b18c4ed9`) supplies densified `Pl`/`Dm`/`nestOK`/`pickE`/`ch0P`.
`ChkBitDagC` supplies DagC `g*` for Track-C `orthOK`. Bridge `toNB`/`net0D` feeds
published `BitOppbankQHNet` (`52d9e9e0`). Includes `RunOK` lemmas toward `net0_ok`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank.NetD

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.ProjB
open IntMul.Kappa.R8.Bit.Oppbank.NB (net)
open IntMul.Kappa.R8.Bit.Oppbank.DagC

/-! ## Re-exports from ProjB -/

abbrev codeBound := ProjB.codeBound
abbrev Ch := ProjB.Ch
noncomputable def ch0 : Ch := ProjB.ch0P

theorem codeBound_eq : codeBound = 64251 := rfl

theorem dagC_imported : (g0 : List Nat) = g0 := rfl

/-! ## Bridge into published QHNet program -/

noncomputable def toNB (ch : Ch) : IntMul.Kappa.R8.Bit.Oppbank.NB.Ch where
  S := ch.S
  Si := ch.Si
  e1 := ch.e1
  e2 := ch.e2
  ex := ch.ex
  en := ch.en
  ei := ch.ei
  ec := ch.ec

noncomputable def net0D : QHNet (ZMod 2) W Tmp 529 := net (toNB ch0)

theorem net0D_W : W = 104719230 := rfl
theorem net0D_T : Tmp = 3217907 := rfl
theorem net0D_codeBound : codeBound = 64251 := codeBound_eq
theorem toNB_ex (ch : Ch) : (toNB ch).ex = ch.ex := rfl
theorem toNB_ei (ch : Ch) : (toNB ch).ei = ch.ei := rfl

/-! ## net0_ok pieces: RunOK for Defs52 run classes -/

theorem RunOK_auxRuns19_0 : RunOK 529 (0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4) := by
  simp [RunOK]

theorem RunOK_auxRuns19_1 :
    RunOK 529 ((19 + 4), (19 + 4), (19 + 4) * (19 + 4) - 2 * (19 + 4)) := by
  simp [RunOK]

theorem RunOK_of_mem_auxRuns19 {ρ : ℕ × ℕ × ℕ} (h : ρ ∈ auxRuns 19) :
    RunOK 529 ρ := by
  simp [auxRuns] at h
  rcases h with h | h
  · simpa [h] using RunOK_auxRuns19_0
  · simpa [h] using RunOK_auxRuns19_1

theorem RunOK_dataRuns23_0 : RunOK 529 (2 * 23 - 1, 2 * 23 - 1, 529 - 2 * (2 * 23 - 1)) := by
  simp [RunOK]

theorem RunOK_dataRuns23_1 : RunOK 529 (1, 529 - 23 + 1, 23 - 2) := by
  simp [RunOK]

theorem RunOK_of_mem_dataRuns23 {ρ : ℕ × ℕ × ℕ} (h : ρ ∈ dataRuns 23 529) :
    RunOK 529 ρ := by
  simp [dataRuns] at h
  rcases h with h | h
  · simpa [h] using RunOK_dataRuns23_0
  · simpa [h] using RunOK_dataRuns23_1

theorem RunOK_of_mem_sideRuns23 {r : ℕ} {ρ : ℕ × ℕ × ℕ}
    (hr : r ≤ 23) (h : ρ ∈ sideRuns 23 529 r) : RunOK 529 ρ := by
  unfold sideRuns at h
  by_cases hcond : 23 < 2 * r
  · simp [hcond] at h
    subst h
    have hpos : 0 < 2 * r - 23 := Nat.sub_pos_of_lt hcond
    have hlt : 2 * r - 23 < 529 := by omega
    have h1 : 23 - r + (2 * r - 23) ≤ 529 := by omega
    have h2 : 529 - r + (2 * r - 23) ≤ 529 := by
      have : 529 - r + (2 * r - 23) = 506 + r := by omega
      omega
    exact ⟨hpos, hlt, h1, h2⟩
  · simp [hcond] at h

theorem dfltE_runsOK : ∀ ρ ∈ (dfltE : Edge 529).runs, RunOK 529 ρ := by
  intro ρ h; simp [dfltE] at h

theorem AuxR_runsOK {rs : List (ℕ × ℕ × ℕ)} (h : AuxR rs) :
    ∀ ρ ∈ rs, RunOK 529 ρ := by
  intro ρ hρ
  have hrs : rs = auxRuns 19 := h
  exact RunOK_of_mem_auxRuns19 (by simpa [hrs] using hρ)

end IntMul.Kappa.R8.Bit.Oppbank.NetD


