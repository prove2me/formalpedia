-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_ColWire3a20261122
-- name    : LinearSetReconciliation327_Main_ColWire3a20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T08:28:35.937457+00:00
-- url     : https://prove2.me/theorems/885ea2a6-68f2-4a8d-8278-5a9f67c09dc6
-- title:
--   Non-vacuity of the column wiring at `y != 0`, `N = 4`, `ell = 3`
-- statement:
--   Non-vacuity companions to `ColWire`/`ColWire2a`, all at a non-degenerate instance (a non-zero stored syndrome `y != 0`, at least one coordinate per child, `ell = 3`): a `HintRootHeaderAt` header, the full premise package of `DownBlkSemAtW` (inhabited), the payload-carrying state and its memory equation, `colStep_applies_nonzero` — the loop body really runs from that state and returns to the head with the counter incremented — and `colStage_premises_nonvacuous`, all the column stage's premises at once.  Axiom-clean; local `cpl` 5 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's column stage and Theorem 5.1's decoder (the two-window `DownBlkSemAtW` contract).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_ColWire2aPart220261122

/-!
# `ColWire` III — non-vacuity of the column wiring

Everything here is at a **non-degenerate** instance: a non-zero stored syndrome (`y ≠ 0`), at least
one coordinate per child (`N ≥ 1`), and at least one child (`ℓ = 3`).

* `colHeader_inhabited` — a `HintRootHeaderAt` exists (extracted from the proved non-vacuity of the
  two-window contract);
* `colPayload_inhabited` — the full premise package of `DownBlkSemAtW` is inhabited with `y ≠ 0`;
* `colPayloadState` / `colPayloadState_mem` — the state whose memory carries that payload at `β`;
* `colStep_applies_nonzero` — **`colStep_of_downBlk` applied**: the loop body really runs (test,
  `jz`, empty child, `d65Inc`, `jmp`) from that non-degenerate state and returns to the head with
  the counter incremented;
* `colStage_premises_nonvacuous` — all the column stage's premises hold simultaneously at
  `ℓ = 3`, `N ≥ 1`, `y ≠ 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65

open RSD

/-! ## 4. Non-vacuity -/

/-- **A `HintRootHeaderAt` exists** — extracted from the proved non-vacuity of the two-window
contract (`downBlkSemAtW_premises_nonvacuous`). -/
theorem colHeader_inhabited :
    ∃ (E : RAMEnv) (δ header control hintMap resultMap listBase table count N : ℕ),
      HintRootHeaderAt E δ header control hintMap resultMap listBase table count N := by
  obtain ⟨E, δ, β, γ, ms, ws, header, control, hintMap, resultMap, listBase, table, count, N, Ms,
    y, -, -, -, -, -, hdr, -, -, -, -, -, -⟩ := downBlkSemAtW_premises_nonvacuous
  exact ⟨E, δ, header, control, hintMap, resultMap, listBase, table, count, N, hdr⟩

/-- **The full premise package of `DownBlkSemAtW`, with `y ≠ 0`.** -/
theorem colPayload_inhabited :
    ∃ (E : RAMEnv) (δ β γ ms ws header control hintMap resultMap listBase table count N Ms : ℕ)
      (y : Fin Ms → ZMod 2),
      y ≠ 0 ∧ wordsOf E.W Ms ≤ ms ∧ β + ms ≤ 2 ^ E.W ∧ ws ≤ 2 ^ E.W ∧ γ + ws ≤ 2 ^ E.W ∧
        HintRootHeaderAt E δ header control hintMap resultMap listBase table count N ∧
        γ ≤ hintMap ∧ hintMap + N < γ + ws ∧ γ ≤ control ∧ control + 4 ≤ γ + ws ∧
        γ ≤ listBase ∧ listBase + N ≤ γ + ws ∧ (β + ms ≤ γ ∨ γ + ws ≤ β) :=
  downBlkSemAtW_premises_nonvacuous

/-- The state whose memory carries the packed payload `y` at `β` and is zero elsewhere. -/
def colPayloadState (β : ℕ) {Ms : ℕ} (E : RAMEnv) (y : Fin Ms → ZMod 2) (a : ℕ)
    (r : Fin 16 → ℕ) : RAMState :=
  ⟨a, r, fun addr => if β ≤ addr ∧ addr < β + wordsOf E.W Ms then packMem E.W y (addr - β) else 0⟩

theorem colPayloadState_mem {β : ℕ} {Ms : ℕ} (E : RAMEnv) (y : Fin Ms → ZMod 2) (a : ℕ)
    (r : Fin 16 → ℕ) :
    ∀ q < wordsOf E.W Ms,
      (colPayloadState β E y a r).mem (β + q) = packMem E.W y q := by
  intro q hq
  have h1 : β ≤ β + q := Nat.le_add_right β q
  have h2 : β + q < β + wordsOf E.W Ms := by omega
  have h3 : β + q - β = q := Nat.add_sub_cancel_left β q
  simp only [colPayloadState, h1, h2, h3, if_pos, and_self]

/-- The register file of the witness head state: counter `0`, bound `3`, and the two interface
registers `r14 = δ`, `r15 = β`. -/
def colRegs (δ β : ℕ) : Fin 16 → ℕ :=
  Function.update (Function.update (Function.update (fun _ => 0) 2 3) 14 δ) 15 β

/-- **The one-iteration contract fires non-degenerately.**  At `Sdec = .code []`, `Tdec = 0`,
`j = 0 < 3`, the state carrying a **non-zero** payload is carried by the loop body — test, `jz`,
empty child, `d65Inc`, `jmp` — back to the loop head in at most `0 + 5` steps, with the counter
incremented.  This is `colStep_of_downBlk` *applied*, so all of the premises are simultaneously
satisfiable at `y ≠ 0`, `N ≥ 1`, `ℓ = 3 ≥ 1`. -/
theorem colStep_applies_nonzero {Sinit Srow Sassem Sres Scr : Stmt} {E : RAMEnv}
    {δ β γ ms ws header control hintMap resultMap listBase table count N Ms Bw : ℕ}
    {y : Fin Ms → ZMod 2} {I : ℕ → (ℕ → ℕ) → Prop}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (hy : y ≠ 0)
    (hW1 : 1 < 2 ^ E.W) (hell3 : 3 < 2 ^ E.W)
    (hfit : wordsOf E.W Ms ≤ ms) (hδB : δ + Bw ≤ 2 ^ E.W) (hβ : β + ms ≤ 2 ^ E.W)
    (hws : ws ≤ 2 ^ E.W) (hγws : γ + ws ≤ 2 ^ E.W)
    (hdr : HintRootHeaderAt E δ header control hintMap resultMap listBase table count N)
    (hHint : γ ≤ hintMap) (hHintTop : hintMap + N < γ + ws)
    (hControl : γ ≤ control) (hControlTop : control + 4 ≤ γ + ws)
    (hList : γ ≤ listBase) (hListTop : listBase + N ≤ γ + ws)
    (hDisj : β + ms ≤ γ ∨ γ + ws ≤ β)
    (hIFrame : ∀ n' mem, I n' mem → ∀ a', a' < γ ∨ γ + ws ≤ a' → mem a' = (colPayloadState β E y
      (zDColHead Sinit Srow 3) (colRegs δ β)).mem a') :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (0 : ℝ) + 5 ∧
      (step (zProgDecOfTop Sinit Srow (.code []) Sassem Sres Scr 3) E)^[k]
        (colPayloadState β E y (zDColHead Sinit Srow 3)
          (colRegs δ β)) = s' ∧
      s'.pc = zDColHead Sinit Srow 3 ∧ s'.regs 1 = 0 + 1 ∧ s'.regs 2 = 3 := by
  set r : Fin 16 → ℕ := colRegs δ β with hr
  set s : RAMState := colPayloadState β E y (zDColHead Sinit Srow 3) r with hs
  have hpc : s.pc = zDColHead Sinit Srow 3 := rfl
  have h1 : s.regs 1 = 0 := by rw [hs, hr]; simp [colPayloadState, colRegs]
  have h2 : s.regs 2 = 3 := by rw [hs, hr]; simp [colPayloadState, colRegs]
  have h14 : s.regs 14 = δ := by rw [hs, hr]; simp [colPayloadState, colRegs]
  have h15 : s.regs 15 = β := by rw [hs, hr]; simp [colPayloadState, colRegs]
  have hmem : ∀ q < wordsOf E.W Ms, s.mem (β + q) = packMem E.W y q := by
    rw [hs]; exact colPayloadState_mem E y _ r
  exact colStep_of_downBlk (P := zProgDecOfTop Sinit Srow (.code []) Sassem Sres Scr 3)
    (downBlkSemAtW_nonvacuous E (le_refl (0 : ℝ)) Bw ms ws N Ms I Hs)
    (colCounter_empty E)
    (zAt_col_loopD Sinit Srow (.code []) Sassem Sres Scr 3)
    hW1 hell3 δ β γ header control hintMap resultMap listBase table count y [] 0 s
    (by norm_num) hpc h1 h2 hfit hδB hβ hws hγws hdr h14 h15 hmem
    hHint hHintTop hControl hControlTop hList hListTop hDisj hIFrame

/-- **The contract package is inhabited at `ℓ = 3`, `N = d = 4 ≥ 1`, `y ≠ 0`.**  The concrete
numbers are the ones of `downBlkSemAtW_premises_nonvacuous` (`β = 100`, `γ = 0`, `ms = 1`,
`ws = 20`, `hintMap = 2`, `control = 7`, `listBase = 12`, `N = 4`, `Ms = 8`, `δ = 5`), with the
stored syndrome `winY ≠ 0`; the loop is run with `ℓ = 3` children. -/
theorem colStage_premises_nonvacuous :
    winY ≠ 0 ∧ 1 ≤ 4 ∧ wordsOf winEnv.W 8 ≤ 1 ∧ 100 + 1 ≤ 2 ^ winEnv.W ∧
      20 ≤ 2 ^ winEnv.W ∧ 0 + 20 ≤ 2 ^ winEnv.W ∧
      HintRootHeaderAt winEnv 5 32 7 2 20 12 20 0 4 ∧
      0 ≤ 2 ∧ 2 + 4 < 0 + 20 ∧ 0 ≤ 7 ∧ 7 + 4 ≤ 0 + 20 ∧ 0 ≤ 12 ∧ 12 + 4 ≤ 0 + 20 ∧
      (100 + 1 ≤ 0 ∨ 0 + 20 ≤ 100) := by
  have hW8 : winEnv.W = 8 := rfl
  refine ⟨winY_ne_zero, by norm_num, ?_, ?_, ?_, ?_, winHeader, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · show wordsOf winEnv.W 8 ≤ 1
    rw [hW8]; decide
  · show 100 + 1 ≤ 2 ^ winEnv.W
    rw [hW8]; norm_num
  · show 20 ≤ 2 ^ winEnv.W
    rw [hW8]; norm_num
  · show 0 + 20 ≤ 2 ^ winEnv.W
    rw [hW8]; norm_num

end W65
end LinearSetReconciliation327.Main


