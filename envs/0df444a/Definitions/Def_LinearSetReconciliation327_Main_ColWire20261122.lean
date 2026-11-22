-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_ColWire20261122
-- name    : LinearSetReconciliation327_Main_ColWire20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:45:21.713743+00:00
-- url     : https://prove2.me/theorems/12ea495b-fd7c-416c-926c-6f70b2cc04df
-- title:
--   Theorem 6.5's column workspace allocation (`ws = 2N + 5`, one shared workspace, `J` outside)
-- statement:
--   The allocation of Theorem 6.5's column block `topLoop Sdec`: one workspace of `colWs N = 2 N + 5` words shared by all `ell` children, child `j`'s payload in its own block `colPayBase beta0 ms j = beta0 + j * ms`, and the hint list `J` strictly below the workspace start `colGamma = beta0 + ell * ms`.  The structure `ZColLayout` carries the containment and word-width facts; `colWs_bounds` derives the size `2N + 5` from the packed chain; `ZColLayout.pay_disjoint`, `.j_outside`, `.hintMap_lt_control` are the consequences that `DownBlkSemAtW` asks for.  Non-vacuity is proved at `N = 4`, `ell = 3`, `Ms = 8`, `ms = 2`, `beta0 = 100`, `gamma = 106`.  Axiom-clean; local `cpl` 5 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's column stage and Theorem 5.1's decoder (the two-window `DownBlkSemAtW` contract).

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_RowStage2Mirror20261122
import Definitions.Def_LinearSetReconciliation327_Main_HintDecBase51At20261122

/-!
# `ColWire` — the column stage's workspace allocation

Theorem 6.5's column block is `topLoop Sdec`, and `RowStage2Mirror`'s `zColLoop_stageRun` already
proves the loop's *shape* from a per-iteration `hbody`.  What is missing is the **allocation**: one
workspace shared by all `ℓ` children, each child's payload in its own block, and the hint list `J`
outside the workspace.

This file supplies the allocation and discharges `DownBlkSemAtW`'s arithmetic from it:

* `colWs N = 2 * N + 5` — the workspace size forced by `ws_bounds_packed` when the decoder's three
  blocks are packed (`hintMap`, then the four control words, then the emitted list);
* `colPayBase β0 ms j = β0 + j * ms` — the `j`-th child's payload block, and
  `colGamma β0 ms ell = β0 + ell * ms` — the workspace start, *after* all payloads, so that every
  payload window is disjoint from the one workspace;
* `ZColLayout` — the allocation, with the strict `wordsOf E.W Ms < ms` that puts the hint list `J`
  (which sits just past the payload) strictly below `γ`, i.e. **outside** the workspace;
* `ZColLayout.ws_eq`, `.pay_disjoint`, `.j_outside`, `.hintMap_lt_control`, … — the consequences
  `DownBlkSemAtW` asks for;
* non-vacuity: an explicit non-degenerate instance (`N = 4`, `ell = 3`, `Ms = 8`, `ms = 2`,
  `ws = 13 = 2·4 + 5`, `β0 = 100`, `γ = 106`, `8`-bit machine).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace W65

open RSD

/-! ## 1. The allocation functions -/

/-- The shared workspace's size: `hintMap`'s block (with its one-word boundary), then the four
control words, then the emitted list — `2N + 5`. -/
def colWs (N : ℕ) : ℕ := 2 * N + 5

/-- The `j`-th child's payload block starts here.  The children are laid out consecutively. -/
def colPayBase (β0 ms j : ℕ) : ℕ := β0 + j * ms

/-- The one workspace starts after **all** the payload blocks, so that every payload window is
disjoint from it. -/
def colGamma (β0 ms ell : ℕ) : ℕ := β0 + ell * ms

/-- The decoder's bitmap block, at the bottom of the workspace. -/
def colHintMap (γ : ℕ) : ℕ := γ

/-- The four control words, immediately after the bitmap's `N + 1` words. -/
def colControl (γ N : ℕ) : ℕ := γ + N + 1

/-- The emitted list, immediately after the control words. -/
def colListBase (γ N : ℕ) : ℕ := γ + N + 5

theorem colWs_eq (N : ℕ) : colWs N = 2 * N + 5 := rfl

theorem colHintMap_le (γ : ℕ) : γ ≤ colHintMap γ := le_refl γ

theorem colHintMap_lt_control (γ N : ℕ) : colHintMap γ + N < colControl γ N := by
  simp only [colHintMap, colControl]; omega

theorem colControl_add_four (γ N : ℕ) : colControl γ N + 4 ≤ colListBase γ N := by
  simp only [colControl, colListBase]; omega

/-- **The workspace is exactly `2N + 5`.**  `ws_bounds_packed` gives the lower bound from the three
containments and `colWs` meets it with equality. -/
theorem colWs_bounds {γ ws N hintMap control listBase : ℕ}
    (hHint : γ ≤ hintMap) (h1 : hintMap + N < control) (h2 : control + 4 ≤ listBase)
    (h3 : listBase + N ≤ γ + ws) : colWs N ≤ ws := by
  have := ws_bounds_packed hHint h1 h2 h3
  simpa [colWs] using this

/-- The packed layout of the workspace realises `colWs`. -/
theorem colWs_packed (γ N : ℕ) :
    γ ≤ colHintMap γ ∧ colHintMap γ + N < colControl γ N ∧
      colControl γ N + 4 ≤ colListBase γ N ∧ colListBase γ N + N ≤ γ + colWs N := by
  refine ⟨le_refl γ, colHintMap_lt_control γ N, colControl_add_four γ N, ?_⟩
  simp only [colListBase, colWs]; omega

/-! ## 2. The allocation, as a structure -/

/-- **The column-stage allocation.**  `β0` is the first payload base, `ms` the per-child payload
window, `γ` the single shared workspace, `δ` the deterministic-table base and `Ms` the stored
syndrome's bit length.  The one *strict* inequality is `wordsOf E.W Ms < ms`: the hint list `J` sits
at `β + wordsOf E.W Ms`, so a child's block must have room for `J` *below* `γ` — otherwise `J` would
land in the workspace and the next child would read a corrupted list. -/
structure ZColLayout (E : RAMEnv) (N ell Ms ms : ℕ) (β0 δ γ : ℕ) : Prop where
  /-- At least one coordinate per child (`N = d ≥ 1`). -/
  hN : 1 ≤ N
  /-- At least one child (`ℓ ≥ 1`). -/
  hell : 1 ≤ ell
  /-- A non-empty stored syndrome. -/
  hMs : 1 ≤ Ms
  /-- The machine has at least two states per word. -/
  hW : 1 < 2 ^ E.W
  /-- **`J` is outside the workspace**: the payload uses strictly fewer words than its window. -/
  hfitJ : wordsOf E.W Ms < ms
  hms : ms ≤ 2 ^ E.W
  /-- The workspace starts after all payload blocks. -/
  hγ : γ = colGamma β0 ms ell
  /-- `ws = 2N + 5` fits. -/
  hws : colWs N ≤ 2 ^ E.W
  /-- The workspace fits. -/
  hγws : γ + colWs N ≤ 2 ^ E.W
  /-- The `det` base plus the decoder's own footprint fits. -/
  hδ : δ + wordsOf E.W Ms < 2 ^ E.W

namespace ZColLayout

variable {E : RAMEnv} {N ell Ms ms β0 δ γ : ℕ}

/-- The workspace really is `2N + 5` words. -/
theorem ws_eq (L : ZColLayout E N ell Ms ms β0 δ γ) : colWs N = 2 * N + 5 := rfl

theorem hintMap_lt_control (L : ZColLayout E N ell Ms ms β0 δ γ) :
    colHintMap γ + N < colControl γ N := colHintMap_lt_control γ N

theorem control_add_four (L : ZColLayout E N ell Ms ms β0 δ γ) :
    colControl γ N + 4 ≤ colListBase γ N := colControl_add_four γ N

theorem list_le (L : ZColLayout E N ell Ms ms β0 δ γ) :
    colListBase γ N + N ≤ γ + colWs N := (colWs_packed γ N).2.2.2

theorem wordsOf_le_ms (L : ZColLayout E N ell Ms ms β0 δ γ) : wordsOf E.W Ms ≤ ms :=
  le_of_lt L.hfitJ

/-- **Every payload window is disjoint from the workspace.** -/
theorem pay_disjoint (L : ZColLayout E N ell Ms ms β0 δ γ) {j : ℕ} (hj : j < ell) :
    colPayBase β0 ms j + ms ≤ γ := by
  rw [L.hγ]
  simp only [colPayBase, colGamma]
  have : j + 1 ≤ ell := hj
  nlinarith [Nat.mul_le_mul_right ms this]

/-- **The hint list of child `j` is outside the workspace.**  It sits at
`colPayBase β0 ms j + wordsOf E.W Ms`, which is strictly below `γ`. -/
theorem j_outside (L : ZColLayout E N ell Ms ms β0 δ γ) {j : ℕ} (hj : j < ell) :
    colPayBase β0 ms j + wordsOf E.W Ms < γ := by
  rw [L.hγ]
  simp only [colPayBase, colGamma]
  have h1 : j + 1 ≤ ell := hj
  have h2 : ms * (j + 1) ≤ ms * ell := Nat.mul_le_mul_left ms h1
  have h3 : (j + 1) * ms = ms * (j + 1) := Nat.mul_comm _ _
  nlinarith [L.hfitJ]

/-- The payload extent the contract wants: the window is at least the packed payload. -/
theorem hms_fit (L : ZColLayout E N ell Ms ms β0 δ γ) : wordsOf E.W Ms ≤ ms := L.wordsOf_le_ms

end ZColLayout

/-! ## 3. Non-vacuity of the allocation -/

/-- The reference `8`-bit machine for the column witnesses (the deterministic table is arbitrary;
the column stage never reads it in the witness because the child body is empty). -/
def colEnv : RAMEnv := detEnv 8 (fun _ => 0)

/-- **A non-degenerate allocation.**  `N = 4` coordinates, `ell = 3` children, `Ms = 8` stored bits
(`wordsOf 8 8 = 1`), `ms = 2` words per child — the strict `1 < 2` is what puts `J` outside the
workspace — payloads at `β0 = 100`, hence `γ = 106`, and `ws = 2·4 + 5 = 13`, so `γ + ws = 119 ≤ 256`.
-/
theorem zColLayout_nonvacuous : ZColLayout colEnv 4 3 8 2 100 0 106 := by
  have hW8 : colEnv.W = 8 := rfl
  have hW1 : 1 < 2 ^ colEnv.W := by rw [hW8]; norm_num
  refine ⟨by norm_num, by norm_num, by norm_num, hW1, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · show wordsOf colEnv.W 8 < 2
    rw [hW8]; decide
  · show 2 ≤ 2 ^ colEnv.W
    rw [hW8]; norm_num
  · show colWs 4 ≤ 2 ^ colEnv.W
    rw [hW8]; decide
  · show 106 + colWs 4 ≤ 2 ^ colEnv.W
    rw [hW8]; decide
  · show 0 + wordsOf colEnv.W 8 < 2 ^ colEnv.W
    rw [hW8]; decide

/-- The same allocation at a **non-zero** stored syndrome: `y ≠ 0` is a premise of the payload
clause, so the witness must not be the zero vector. -/
def colY : Fin 8 → ZMod 2 := fun _ => 1

theorem colY_ne_zero : colY ≠ 0 := by
  intro h
  have := congrFun h ⟨0, by norm_num⟩
  simp [colY] at this

/-- At the non-degenerate allocation, the three facts the column stage needs hold *numerically*:
payload disjointness, `J` outside the workspace, and the workspace fit. -/
theorem zColLayout_facts :
    (colPayBase 100 2 2 + 2 ≤ 106) ∧ (colPayBase 100 2 2 + wordsOf 8 8 < 106) ∧
      (106 + colWs 4 ≤ 256) ∧ colWs 4 = 13 := by
  refine ⟨by norm_num [colPayBase], ?_, by norm_num [colWs], by norm_num [colWs]⟩
  norm_num [colPayBase, wordsOf]

end W65
end LinearSetReconciliation327.Main


