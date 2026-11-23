-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_RowStage4MirrorP
-- name    : LinearSetReconciliation327_Main_RowStage4MirrorP
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T09:49:33.133131+00:00
-- url     : https://prove2.me/theorems/57a07f76-db1f-44e6-94c7-93cc1a09666f
-- title:
--   Row-chain mirror: the nine-stage row body at the `Pay` layout (`RSD4P`)
-- statement:
--   A re-host of `…_RowStage4Pay20261122` on the `DecoderLemmas` side, in the fresh namespace `RSD4P`: `zSetupCode`, the 16-instruction `Pay` setup, `zBody` (whose `stageStmt.len = 44` is the `Pay` block) and the end-to-end `zSetup_lands_RepackPre`.  Every span is the published `RowStage4Pay` span; only the imports, the namespace and the `RDec`→`RDecP` / `RSD3`→`RSD3P` references changed.  Definitions and proved lemmas only; no `sorry`, no new axiom; local `cpl` 15 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_RowStage3MirrorP
import Definitions.Def_LinearSetReconciliation327_Main_DecodeLoopsMirror

/-!
# `RowStage4` — the row body closed: the setup block, the nine-stage composition, and the
invariant

`rowstage3/RowStage3.lean` left two obligations open (its R1 and R2).  This bundle closes them:

* **§1 — R2, the setup block.**  `zSetupCode`'s (17-instruction) effect is computed exactly
  (`zSetup_run`) and shown to land on `RDL.RepackPre` (`zSetup_lands_RepackPre`), including the
  arithmetic `((R + W) % 2^W + 2^W − 1) % 2^W / W = wordsOf W R`, which is proved as a standalone
  `Nat` lemma over variables first (`zWordsOf_computed`).
* **§2 — the row invariant's frame lemmas.**  `zRowInv` is preserved by every stage: by a frame above
  `decoderAllocEnd t` (the clearing pass, the decoder, the setup), by a frame outside the two save
  cells (save/restore), and by the repack pass (which writes only row `j`'s slot).
* **§3 — R1, the nine-stage body.**  `zBody` is the concrete row body; `zBody_at` is its address
  plumbing; `zBody_sem` composes save → clear/reload/stage → decode → setup → repack → restore inside
  the loop; `zBody_hbody` adds the counter step and the loop's trailing `jmp`, giving
  `zRowStage_real`'s `hbody`.
* **§4 — `zRowStage_real` fires without `hbody`** (`zRowStage_real_closed`).
* **§5 — what still blocks a non-degenerate machine trace**, as *theorems*: the only proved decoder
  contract (`pinsketchRun_semB`) demands `E.det = detStd t N b ι`; under that table the staging base
  is `0`, so the decoder's own hypothesis `wordsOf (8w) (tw) ≤ β` forces `t = 0`, contradicting the
  row's `1 ≤ t`; and `not_rowOutFits_detStd` shows the row bitmaps cannot even be placed.  The
  decoded stage is therefore carried as the explicit interface `zDecodeOK` below, not silently
  assumed, and that interface is itself *inhabited* in its own environment (`zDecodeOK_of_semB`).

No file is modified; the mirrors are byte-identical copies.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RSD4P

open R66 LinearSetReconciliation327.Main.RDecP RMR RSD RDL RSD3P

/-! ## 1. R2 — the setup block's effect -/

/-- The machine's own words-of computation.  `zSetupCode` computes
`((R + W) mod 2^m + 2^m − 1) mod 2^m / W`; this is `wordsOf W R`.  Stated over variables first
because `omega` cannot see through `2 ^ m`. -/
theorem zWordsOf_computed (W R M : ℕ) (hW : 0 < W) (hk : R + W < 2 ^ M) :
    (((R + W) % 2 ^ M + 2 ^ M - 1) % 2 ^ M) / W = wordsOf W R := by
  have hp : 0 < 2 ^ M := Nat.two_pow_pos M
  have hRW : 0 < R + W := by omega
  rw [Nat.mod_eq_of_lt hk]
  have h2 : R + W + 2 ^ M - 1 = (R + W - 1) + 2 ^ M := by omega
  rw [h2, Nat.add_mod_right]
  have h3 : R + W - 1 < 2 ^ M := by omega
  rw [Nat.mod_eq_of_lt h3]
  rfl

/-- The registers `zSetupCode` leaves: its `RepackPre` half (`r0`, `r7`, `r8`, `r11`, `r6`, `r5`) is
the payload of §1.2; `r14`/`r15` are the two scratch writes and only need to be *some* words. -/
def zSetupRegs (E : RAMEnv) (R j : ℕ) (r : Fin 16 → ℕ) : Fin 16 → ℕ :=
  fun i =>
    if i = r0 then 0
    else if i = r7 then r r0 % 2 ^ E.W
    else if i = r8 then r r1 % 2 ^ E.W
    else if i = r11 then E.W
    else if i = r6 then wordsOf E.W R
    else if i = r5 then rowSlot E R j
    else if i = r14 then 3 % 2 ^ E.W
    else if i = r15 then (wordsOf E.W R * j) % 2 ^ E.W
    else r i

theorem zSetupRegs_r0 (E : RAMEnv) (R j : ℕ) (r : Fin 16 → ℕ) : zSetupRegs E R j r r0 = 0 := by
  simp [zSetupRegs]

theorem zSetupRegs_r7 (E : RAMEnv) (R j : ℕ) (r : Fin 16 → ℕ) :
    zSetupRegs E R j r r7 = r r0 % 2 ^ E.W := by
  simp [zSetupRegs]

theorem zSetupRegs_r8 (E : RAMEnv) (R j : ℕ) (r : Fin 16 → ℕ) :
    zSetupRegs E R j r r8 = r r1 % 2 ^ E.W := by
  simp [zSetupRegs]

theorem zSetupRegs_r11 (E : RAMEnv) (R j : ℕ) (r : Fin 16 → ℕ) :
    zSetupRegs E R j r r11 = E.W := by
  simp [zSetupRegs]

theorem zSetupRegs_r6 (E : RAMEnv) (R j : ℕ) (r : Fin 16 → ℕ) :
    zSetupRegs E R j r r6 = wordsOf E.W R := by
  simp [zSetupRegs]

theorem zSetupRegs_r5 (E : RAMEnv) (R j : ℕ) (r : Fin 16 → ℕ) :
    zSetupRegs E R j r r5 = rowSlot E R j := by
  simp [zSetupRegs]

/-- **R2, the machine run of `zSetupCode`.**  Seventeen instructions, memory untouched, ending in
`zSetupRegs`.  The hypotheses `hdet2`/`hdet12` are the `det` header's slots `2` (= `R`) and `12`
(= `W`); `hRW` is the side condition that makes the machine's rounded division equal `wordsOf`;
`hsl` says the row slot is a word. -/
theorem zSetup_run (E : RAMEnv) (pc cell R j : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hW16 : 16 < 2 ^ E.W) (hcell : cell < 2 ^ E.W) (hcellj : m cell = j)
    (hjw : j < 2 ^ E.W)
    (hdet2 : E.det 2 % 2 ^ E.W = R) (hdet12 : E.det 12 % 2 ^ E.W = E.W)
    (hRW : R + E.W < 2 ^ E.W) (hsl : rowSlot E R j < 2 ^ E.W) :
    runBlock (zSetupCode cell) E ⟨pc, r, m⟩ = ⟨pc + 17, zSetupRegs E R j r, m⟩ := by
  have hWpos : 0 < E.W := by
    rcases Nat.eq_zero_or_pos E.W with h | h
    · rw [h] at hW; simp at hW
    · exact h
  have h2 : (2 : ℕ) % 2 ^ E.W = 2 := Nat.mod_eq_of_lt (by omega)
  have h12 : (12 : ℕ) % 2 ^ E.W = 12 := Nat.mod_eq_of_lt (by omega)
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have h3 : (3 : ℕ) % 2 ^ E.W = 3 := Nat.mod_eq_of_lt (by omega)
  have hcell' : cell % 2 ^ E.W = cell := Nat.mod_eq_of_lt hcell
  have hmcell : m (cell % 2 ^ E.W) % 2 ^ E.W = j := by
    rw [hcell', hcellj, Nat.mod_eq_of_lt hjw]
  have hdiv : (((R + E.W) % 2 ^ E.W + 2 ^ E.W - 1) % 2 ^ E.W) / E.W = wordsOf E.W R :=
    zWordsOf_computed E.W R E.W hWpos hRW
  have hmul : wordsOf E.W R * j < 2 ^ E.W := by
    have h := hsl
    rw [rowSlot, rowWords, Nat.mul_comm j (wordsOf E.W R)] at h
    omega
  have hmulmod : (wordsOf E.W R * j) % 2 ^ E.W = wordsOf E.W R * j := Nat.mod_eq_of_lt hmul
  have hwlt : wordsOf E.W R < 2 ^ E.W := by
    have h1 : wordsOf E.W R = (R + E.W - 1) / E.W := rfl
    have h2 : (R + E.W - 1) / E.W ≤ R + E.W - 1 := Nat.div_le_self _ _
    omega
  have hwmod : wordsOf E.W R % 2 ^ E.W = wordsOf E.W R := Nat.mod_eq_of_lt hwlt
  have hsum : rowBase E + wordsOf E.W R * j < 2 ^ E.W := by
    have h := hsl
    rw [rowSlot, rowWords, Nat.mul_comm j (wordsOf E.W R)] at h
    exact h
  have hsummod : (rowBase E + wordsOf E.W R * j) % 2 ^ E.W = rowSlot E R j := by
    rw [Nat.mod_eq_of_lt hsum, rowSlot, rowWords, Nat.mul_comm j (wordsOf E.W R)]
  have hsummod2 : (E.det 3 + wordsOf E.W R * j) % 2 ^ E.W = rowSlot E R j := by
    have hstep : (E.det 3 + wordsOf E.W R * j) % 2 ^ E.W
        = (rowBase E + wordsOf E.W R * j) % 2 ^ E.W := by
      rw [Nat.add_mod, hmulmod]
      rfl
    rw [hstep, hsummod]
  apply zRamState_eq_of
  · simp [zSetupCode, runBlock, execInstr, Nat.add_assoc]
  · intro i
    fin_cases i <;>
      simp [zSetupRegs, zSetupCode, runBlock, execInstr, Function.update_self, Function.update_of_ne,
        h1, h2, h3, h12, hcell', hcellj, hmcell, hdet2, hdet12, hdiv, hmulmod, hsummod, hsummod2,
        hwmod, Nat.add_assoc, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one]
  · simp [zSetupCode, runBlock, execInstr]

/-! ### 1.2 The setup block lands on `RepackPre` -/

/-- **R2 closed: `zSetupCode` establishes `RepackPre`.**  `listBase`/`len` are the decoder's output
base and length, read out of `r0`/`r1`; the setup copies them to `r7`/`r8` *before* zeroing `r0`, and
computes the row slot from the **saved** counter `j = mem[cell]`, not from `r1`. -/
theorem zSetup_lands_RepackPre (E : RAMEnv) (pc cell R j : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ)
    {len listBase : ℕ} (x : Fin R → ZMod 2)
    (hW : 1 < 2 ^ E.W) (hW16 : 16 < 2 ^ E.W) (hcell : cell < 2 ^ E.W) (hcellj : m cell = j)
    (hjw : j < 2 ^ E.W)
    (hdet2 : E.det 2 % 2 ^ E.W = R) (hdet12 : E.det 12 % 2 ^ E.W = E.W)
    (hRW : R + E.W < 2 ^ E.W) (hsl : rowSlot E R j < 2 ^ E.W)
    (hr0 : r r0 = listBase) (hr1 : r r1 = len)
    (hlistBase : listBase < 2 ^ E.W) (hlen : len < 2 ^ E.W)
    (hslotW : rowSlot E R j + wordsOf E.W R ≤ 2 ^ E.W)
    (hz : ∀ i, i < wordsOf E.W R → m (rowSlot E R j + i) = 0)
    (hval : ∀ v, v ∈ listAt (⟨pc, r, m⟩ : RAMState) listBase len → v < 2 ^ E.W)
    (hRv : ∀ v, v ∈ listAt (⟨pc, r, m⟩ : RAMState) listBase len → v < R)
    (hadr : listBase + len ≤ 2 ^ E.W)
    (hdisj : listBase + len ≤ rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ listBase)
    (hsupp : ListSupports (listAt (⟨pc, r, m⟩ : RAMState) listBase len) x) :
    RepackPre E R j len listBase x
      (runBlock (zSetupCode cell) E ⟨pc, r, m⟩) := by
  rw [zSetup_run E pc cell R j r m hW hW16 hcell hcellj hjw hdet2 hdet12 hRW hsl]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hdisj, ?_⟩
  · show zSetupRegs E R j r (0 : Fin 16) = 0
    exact zSetupRegs_r0 E R j r
  · show zSetupRegs E R j r (7 : Fin 16) = listBase
    rw [zSetupRegs_r7, hr0, Nat.mod_eq_of_lt hlistBase]
  · show zSetupRegs E R j r (8 : Fin 16) = len
    rw [zSetupRegs_r8, hr1, Nat.mod_eq_of_lt hlen]
  · show zSetupRegs E R j r (11 : Fin 16) = E.W
    exact zSetupRegs_r11 E R j r
  · show zSetupRegs E R j r (6 : Fin 16) = wordsOf E.W R
    exact zSetupRegs_r6 E R j r
  · show zSetupRegs E R j r (5 : Fin 16) = rowSlot E R j
    exact zSetupRegs_r5 E R j r
  · exact hz
  · exact hval
  · exact hRv
  · exact hlen
  · exact hadr
  · exact hslotW
  · exact hsupp

/-!
## 2. R1 — the row invariant is preserved by every stage

`zRowInv` is a conjunction of three statements (payloads intact, previous rows' `RowOut`, future slots
zero).  It is preserved by any memory change that fixes the two address families

* `rowPayBase E r + i` (`i < stageLen E`), and
* `rowSlot E R r + i` (`i < wordsOf E.W R`)

pointwise (`zRowInv_of_preserved`).  The stages supply that in three different shapes: a frame above
`decoderAllocEnd t` (the clearing pass, the decoder), a frame below the two save cells (save and
restore), and the repack pass, which writes only row `j`'s slot and therefore produces
`zRowInv (j+1)` (`zRowInv_succ_repack`).
-/

/-- Chaining two runs with an exact intermediate state. -/
theorem zIter {α : Type} (f : α → α) {a b : ℕ} {x y z : α}
    (h1 : f^[a] x = y) (h2 : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

/-- **The invariant is a pointwise frame.**  If every payload word and every row-slot word is fixed,
`zRowInv` is preserved. -/
theorem zRowInv_of_preserved {E : RAMEnv} {R d t w j : ℕ} {y : Fin d → Fin (t * w) → ZMod 2}
    {m m' : ℕ → ℕ} (hjd : j ≤ d)
    (hpay : ∀ r < d, ∀ i < stageLen E, m' (rowPayBase E r + i) = m (rowPayBase E r + i))
    (hrow : ∀ r < d, ∀ i < wordsOf E.W R, m' (rowSlot E R r + i) = m (rowSlot E R r + i))
    (h : zRowInv E R d t w y j m) : zRowInv E R d t w y j m' := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr i hi
    rw [hpay r hr i hi]
    exact h.1 r hr i hi
  · intro r hr
    obtain ⟨x, hx⟩ := h.2.1 r hr
    exact ⟨x, fun i hi => by rw [hrow r (by omega) i hi]; exact hx i hi⟩
  · intro r hrj hrd i hi
    rw [hrow r hrd i hi]
    exact h.2.2 r hrj hrd i hi

/-- **Preservation from a frame above `decoderAllocEnd t`** — the shape the clearing pass and the
decoder give. -/
theorem zRowInv_frame_ge {E : RAMEnv} {R d t w j : ℕ} {y : Fin d → Fin (t * w) → ZMod 2}
    {m m' : ℕ → ℕ} (hjd : j ≤ d)
    (hframe : ∀ a, decoderAllocEnd t ≤ a → m' a = m a)
    (hdePay : ∀ r, r < d → decoderAllocEnd t ≤ rowPayBase E r)
    (hdeRow : decoderAllocEnd t ≤ rowBase E)
    (h : zRowInv E R d t w y j m) : zRowInv E R d t w y j m' := by
  refine zRowInv_of_preserved hjd
    (fun r hr i hi => hframe _ (le_trans (hdePay r hr) (Nat.le_add_right _ _)))
    (fun r hr i hi => hframe _ ?_) h
  have h1 : decoderAllocEnd t ≤ rowSlot E R r := by
    rw [rowSlot]
    exact le_trans hdeRow (Nat.le_add_right _ _)
  exact le_trans h1 (Nat.le_add_right _ _)

/-- **Preservation from a frame below the two save cells** — the shape save and restore give. -/
theorem zRowInv_frame_cell {E : RAMEnv} {R d t w j cell : ℕ} {y : Fin d → Fin (t * w) → ZMod 2}
    {m m' : ℕ → ℕ} (hjd : j ≤ d)
    (hframe : ∀ a, a ≠ cell → a ≠ cell + 1 → m' a = m a)
    (hpayCell : ∀ r, r < d → rowPayBase E r + stageLen E ≤ cell)
    (hrowCell : ∀ r, r < d → rowSlot E R r + wordsOf E.W R ≤ cell)
    (h : zRowInv E R d t w y j m) : zRowInv E R d t w y j m' := by
  refine zRowInv_of_preserved hjd (fun r hr i hi => hframe _ ?_ ?_)
    (fun r hr i hi => hframe _ ?_ ?_) h
  · have h1 : rowPayBase E r + i < rowPayBase E r + stageLen E := by omega
    exact ne_of_lt (lt_of_lt_of_le h1 (hpayCell r hr))
  · have h1 : rowPayBase E r + i < rowPayBase E r + stageLen E := by omega
    exact ne_of_lt (lt_trans (lt_of_lt_of_le h1 (hpayCell r hr)) (by omega))
  · have h1 : rowSlot E R r + i < rowSlot E R r + wordsOf E.W R := by omega
    exact ne_of_lt (lt_of_lt_of_le h1 (hrowCell r hr))
  · have h1 : rowSlot E R r + i < rowSlot E R r + wordsOf E.W R := by omega
    exact ne_of_lt (lt_trans (lt_of_lt_of_le h1 (hrowCell r hr)) (by omega))

/-- Every payload word is *below* slot `j` (the payloads sit under the row bitmaps). -/
theorem zRowPayBelow_slot {E : RAMEnv} {R d j : ℕ}
    (hpayRow : ∀ r, rowPayBase E r + stageLen E ≤ rowBase E) {r : ℕ} (hr : r < d) {i : ℕ}
    (hi : i < stageLen E) : rowPayBase E r + i < rowSlot E R j := by
  have h1 : rowPayBase E r + i < rowPayBase E r + stageLen E := by omega
  have h2 : rowPayBase E r + stageLen E ≤ rowBase E := hpayRow r
  have h3 : rowBase E ≤ rowSlot E R j := by rw [rowSlot]; exact Nat.le_add_right _ _
  omega

/-- Two different rows' slot words are ordered: one block is entirely below or entirely above the
other. -/
theorem zRowSlot_disj_lin {E : RAMEnv} {R j r : ℕ} (hrj : r ≠ j) {i : ℕ}
    (hi : i < wordsOf E.W R) :
    rowSlot E R r + i < rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ rowSlot E R r + i := by
  have hrw : rowWords E R = wordsOf E.W R := rfl
  rcases Nat.lt_or_gt_of_ne hrj with hlt | hgt
  · left
    have h1 : rowSlot E R r + i < rowSlot E R (r + 1) := rowSlot_lt_next E R r i (by rw [hrw]; exact hi)
    have h2 : rowSlot E R (r + 1) ≤ rowSlot E R j := by
      rw [rowSlot, rowSlot]
      have hm : (r + 1) * rowWords E R ≤ j * rowWords E R := Nat.mul_le_mul_right _ (by omega)
      exact Nat.add_le_add_left hm _
    omega
  · right
    have h2 : rowSlot E R (j + 1) ≤ rowSlot E R r := by
      rw [rowSlot, rowSlot]
      have hm : (j + 1) * rowWords E R ≤ r * rowWords E R := Nat.mul_le_mul_right _ (by omega)
      exact Nat.add_le_add_left hm _
    have h3 : rowSlot E R (j + 1) = rowSlot E R j + rowWords E R := rowSlot_succ E R j
    have h4 : rowWords E R = wordsOf E.W R := rfl
    omega

/-- **The repack step: `zRowInv j` becomes `zRowInv (j+1)`.**  The repack writes only row `j`'s slot
words; every payload word and every other row's slot words are fixed, and the new `RowOut` supplies
the row `j` conjunct. -/
theorem zRowInv_succ_repack {E : RAMEnv} {R d t w j : ℕ} {y : Fin d → Fin (t * w) → ZMod 2}
    {m m' : ℕ → ℕ} {x : Fin R → ZMod 2}
    (hj : j < d)
    (hupd : ∀ a, a < rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ a → m' a = m a)
    (hpayRow : ∀ r, rowPayBase E r + stageLen E ≤ rowBase E)
    (hnew : RowOut E R j x m')
    (h : zRowInv E R d t w y j m) : zRowInv E R d t w y (j + 1) m' := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr i hi
    rw [hupd _ (Or.inl (zRowPayBelow_slot hpayRow hr hi))]
    exact h.1 r hr i hi
  · intro r hr
    by_cases hrj : r = j
    · subst hrj
      exact ⟨x, hnew⟩
    · obtain ⟨x', hx'⟩ := h.2.1 r (by omega)
      refine ⟨x', fun i hi => ?_⟩
      rw [hupd _ (zRowSlot_disj_lin hrj hi)]
      exact hx' i hi
  · intro r hrj hrd i hi
    have hrj' : r ≠ j := by omega
    rw [hupd _ (zRowSlot_disj_lin hrj' hi)]
    exact h.2.2 r (by omega) hrd i hi

/-!
## 3. The concrete row body and its addresses

`zBody` is the row body in the shape the row loop carries: the loop is
`.loop d65Cond (.seq (zBody ...) (.code d65Inc))`, so `zBody` occupies `a+2 … a+124+len` and the
loop's trailing `jmp` sits at `a+125+len`.
-/

/-- The concrete row body: save `j`, `d`; clear → reload → stage; decode; setup; repack; restore. -/
def zBody (cell t : ℕ) (Sdec : Stmt) : Stmt :=
  .seq (.code (zSaveCode cell))
    (.seq (clearFull 0 (decoderAllocEnd t))
      (.seq (.code (zReloadCode cell))
        (.seq stageStmt
          (.seq Sdec
            (.seq (.code (zSetupCode cell))
              (.seq repackStmt (.code (zRestoreCode cell))))))))

theorem zBody_len (cell t : ℕ) (Sdec : Stmt) : (zBody cell t Sdec).len = 123 + Sdec.len := by
  simp only [zBody, Stmt.len, zSaveCode_length, zReloadCode_length, zSetupCode_length,
    zRestoreCode_length, clearFull_len, stageStmt_len]
  show 4 + (15 + (2 + (44 + (Sdec.len + (17 + (20 + 21)))))) = 123 + Sdec.len
  omega

/-!
## 5. What blocks a non-degenerate machine trace

The decoder is the only stage whose contract lives in a *fixed* environment.  `pinsketchRun_semB`
(and hence `pinsketch_decoding_at_bounded`, and hence `zDecodeStage_sem`) is stated for an arbitrary
`E` **provided `E.det = detStd t N b ι`** (`hdet`) and `E.W = 8 * w`.  The row body needs the same
`E` to carry the composite header: `det 2 = R`, `det 3 = rowBase`, `det 4 = stageLen`,
`det 12 = W`, `det 15 = payTab`, `det 16 = stageBase`.

Under `detStd` those slots are fixed: `detStd 3 = 2t` (so `not_rowOutFits_detStd` refutes the row
base constraint), and slots `15`, `16` are `0` (`detStd_high_zero`, since `detMulBase w = 64`).
Hence `stageBase = 0`, and the decoder's own hypothesis `wordsOf (8w) (tw) ≤ β` forces `t * w = 0`:

* `zDetStd_stageBase` — the staging base is `0`;
* `zDetStd_payTab` — the payload-base pointer is `0`;
* `zDetStd_no_rowBody` — **the decoder contract cannot be applied inside the row body** at `1 ≤ t`,
  `1 ≤ w`, in the only environment it is proved for.

That is the exact hypothesis that blocks a non-degenerate concrete trace: what is missing is the
transport of `pinsketchRun_semB` from `E.det = detStd …` to "agrees with `detStd …` on the slots the
decoder reads" (`< 13`), so that slots `15`, `16` may carry the row staging base.
-/

theorem zDetStd_stageBase {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) :
    stageBase (detEnv (8 * w) (detStd t N b ι)) = 0 := by
  have h16 : detStd t N b ι 16 = 0 :=
    detStd_high_zero (t := t) (N := N) b ι (by norm_num) (by rw [detMulBase_eq]; norm_num)
  simp only [stageBase, hdrStageBase, detEnv, h16, Nat.zero_mod]

theorem zDetStd_payTab {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) :
    payTabAddr (detEnv (8 * w) (detStd t N b ι)) = 0 := by
  have h15 : detStd t N b ι 15 = 0 :=
    detStd_high_zero (t := t) (N := N) b ι (by norm_num) (by rw [detMulBase_eq]; norm_num)
  simp only [payTabAddr, hdrPayTab, detEnv, h15, Nat.zero_mod]

/-- **The decoder contract is unusable inside the row body.**  In the only environment where
`pinsketchRun_semB` is proved, the staging base is `0`, so its hypothesis
`wordsOf (8 * w) (t * w) ≤ β` would force `t * w = 0`.  A row with `1 ≤ t` and `1 ≤ w` therefore
cannot be decoded there — the transport of the decoder to the composite header is the missing
hypothesis, not a missing arithmetic fact. -/
theorem zDetStd_no_rowBody {F : Type} [Field F] [Algebra (ZMod 2) F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) {t N : ℕ} (ht : 1 ≤ t) (hw : 1 ≤ w) :
    ¬ (wordsOf (8 * w) (t * w) ≤ stageBase (detEnv (8 * w) (detStd t N b ι))) := by
  rw [zDetStd_stageBase]
  intro h
  have hM : 0 < t * w := Nat.mul_pos (by omega) (by omega)
  have hW8 : 0 < 8 * w := by omega
  have hpos : 0 < wordsOf (8 * w) (t * w) := by
    rw [wordsOf]
    exact Nat.div_pos (by omega) hW8
  omega

/-- The concrete environment of the instance: `W = 8`, `det 2 = R = 8`, `det 3 = rowBase = 30`,
`det 12 = W = 8`. -/
def zE8 : RAMEnv :=
  detEnv 8 (fun n => if n = 2 then 8 else if n = 3 then 30 else if n = 12 then 8 else 0)

/-- The concrete input state: the decoder's output list at base `100`, length `3`, and the saved
counter `j = 1` at cell `200`. -/
def zS8 : RAMState :=
  ⟨0, (fun i => if i = r0 then 100 else if i = r1 then 3 else 0),
    (fun n => if n = 200 then 1 else 0)⟩

/-- **A non-degenerate machine run of `zSetupCode`.**  Seventeen real steps at `W = 8`, `R = 8`,
`j = 1`: the setup leaves `r0 = 0`, `r7 = 100` (the decoded list base), `r8 = 3` (its length),
`r11 = 8` (`W`), `r6 = 1 = wordsOf 8 8` (**not** the degenerate `0`), and `r5 = 31 = rowSlot 8 1`
(`rowBase 30` plus `1 · wordsOf`).  This is the register half of `RepackPre` at a live instance. -/
theorem zSetup_instance :
    (runBlock (zSetupCode 200) zE8 zS8).regs r0 = 0 ∧
    (runBlock (zSetupCode 200) zE8 zS8).regs r7 = 100 ∧
    (runBlock (zSetupCode 200) zE8 zS8).regs r8 = 3 ∧
    (runBlock (zSetupCode 200) zE8 zS8).regs r11 = 8 ∧
    (runBlock (zSetupCode 200) zE8 zS8).regs r6 = wordsOf 8 8 ∧
    wordsOf 8 8 = 1 ∧
    (runBlock (zSetupCode 200) zE8 zS8).regs r5 = rowSlot zE8 8 1 ∧
    rowSlot zE8 8 1 = 31 ∧
    (runBlock (zSetupCode 200) zE8 zS8).pc = 17 := by
  have hW : 1 < 2 ^ zE8.W := by decide
  have hW16 : 16 < 2 ^ zE8.W := by decide
  have hcell : 200 < 2 ^ zE8.W := by decide
  have hcellj : zS8.mem 200 = 1 := by decide
  have hjw : 1 < 2 ^ zE8.W := by decide
  have hdet2 : zE8.det 2 % 2 ^ zE8.W = 8 := by decide
  have hdet12 : zE8.det 12 % 2 ^ zE8.W = 8 := by decide
  have hRW : 8 + zE8.W < 2 ^ zE8.W := by decide
  have hsl : rowSlot zE8 8 1 < 2 ^ zE8.W := by decide
  have hrun := zSetup_run zE8 0 200 8 1 zS8.regs zS8.mem hW hW16 hcell hcellj hjw hdet2 hdet12 hRW hsl
  have hw : wordsOf 8 8 = 1 := by decide
  have hs : rowSlot zE8 8 1 = 31 := by decide
  have hr0 : zS8.regs r0 = 100 := by decide
  have hr1 : zS8.regs r1 = 3 := by decide
  have hW8 : zE8.W = 8 := rfl
  have hm100 : (100 : ℕ) % 2 ^ 8 = 100 := by norm_num
  have hm3 : (3 : ℕ) % 2 ^ 8 = 3 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, hw, ?_, hs, ?_⟩ <;>
    rw [show zS8 = (⟨0, zS8.regs, zS8.mem⟩ : RAMState) from rfl, hrun] <;>
    simp [zSetupRegs, hW8, hw, hs, hr0, hr1, hm100, hm3, Nat.add_assoc]

end RSD4P
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.RSD4P.zWordsOf_computed
#print axioms LinearSetReconciliation327.Main.RSD4P.zSetup_run
#print axioms LinearSetReconciliation327.Main.RSD4P.zSetup_lands_RepackPre
#print axioms LinearSetReconciliation327.Main.RSD4P.zSetup_instance
#print axioms LinearSetReconciliation327.Main.RSD4P.zIter
#print axioms LinearSetReconciliation327.Main.RSD4P.zRowInv_of_preserved
#print axioms LinearSetReconciliation327.Main.RSD4P.zRowInv_frame_ge
#print axioms LinearSetReconciliation327.Main.RSD4P.zRowInv_frame_cell
#print axioms LinearSetReconciliation327.Main.RSD4P.zRowInv_succ_repack
#print axioms LinearSetReconciliation327.Main.RSD4P.zBody_len
#print axioms LinearSetReconciliation327.Main.RSD4P.zDetStd_stageBase
#print axioms LinearSetReconciliation327.Main.RSD4P.zDetStd_payTab
#print axioms LinearSetReconciliation327.Main.RSD4P.zDetStd_no_rowBody


