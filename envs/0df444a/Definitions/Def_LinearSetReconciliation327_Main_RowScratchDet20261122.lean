-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_RowScratchDet20261122
-- name    : LinearSetReconciliation327_Main_RowScratchDet20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:14:07.037542+00:00
-- url     : https://prove2.me/theorems/8bc2f226-e1d2-45c3-9d12-3f04c63bb6c2
-- title:
--   Row-stage mirror: the row scratch / clearing pass, free of `DecoderLemmas`
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_RowScratchDet20261122` of the Theorem 6.5 development.  It is a re-hosted mirror of the project's published row-stage bundle with only the recorded edits (the import of the `DecoderLemmas` side replaced by the `P21DetBndComp` chain, and — for the `Pay` mirrors — the per-row payload base re-pointed to the arithmetic progression `payTabAddr + j * stageLen`); the statements of the row chain are byte-identical.  It contains definitions and fully proved lemmas only (no `sorry`, no new axiom) and exists so that the later nodes of the chain compile inside the platform's per-definition budget.  This is a supporting node, not a statement of independent mathematical interest.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder) and Proposition 2.1 (the base-relative decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Top65DecDet20261122
import Definitions.Def_LinearSetReconciliation327_Main_P21DetBndComp20261122
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Definitions.Def_LinearSetReconciliation327_Main_P21RunStmt
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoding_at
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_read
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_key_solver
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_verifier

/-!
# `_66_row_scratch` — the row loop's scratch region

Theorem 6.5's row loop runs Proposition 2.1's decoder `d` times in one memory.  The published
`pinsketch_decoding_at` is **one-shot**: it needs

```
hzero : ∀ a, (a < β ∨ β + L ≤ a) → s.mem a = 0          (L = wordsOf (8w) (tw))
```

because its layer copies the payload `[β, β+L)` down to `[0, L)` and then erases the source with
the *zero shadow block* `[β+L, β+2L)`.  Something must re-establish `hzero` between two calls.

This file does four things, with no `sorry` and independent of any `Solutions/*` file:

* **§1 — what must really be zero.**  The two copy passes only ever *read* `[β, β+L)` and
  `[β+L, β+2L)` and only ever *write* `[0, L)` and `[β, β+L)`.  Hence the destination window
  `[0, L)` is irrelevant, and the exact condition for the layer to land on the canonical decoder
  memory `hintMem W y []` is

  `payload on [β, β+L)` **and** `zero on [L, β)` **and** `zero on [β+L, ∞)`

  (`WeakZero`).  `layerMem_eq` proves that suffices; `weakZero_of_layerMem` proves the zero
  conditions are also *necessary*; `strong_to_weak` and `weakZero_strictly_weaker` show the
  published `hzero` is strictly stronger and that the gap is inhabited.
* **§2 — a write-only re-zeroing pass.**  `clearArray_spec` of `Sol_proposition_2_1.lean:5138`
  re-proved against the importable `Definitions` (its statement is byte-identical), together with
  `clearMem_get` / `clearMem_frame`, a `clearInit` register preamble, and the specialised
  `clearScratch` contract at `[0, decoderAllocEnd t)`.
* **§3 — per-iteration maintenance.**  `weakZero_restage`: after clearing `[0, K)` and re-staging
  the payload at `β` with `β + L ≤ K`, `WeakZero` holds again *provided memory at `≥ K` is zero*.
  `rowBody_sem` assembles one loop iteration out of its sub-stages with exact cost.
* **§4 — the idempotence escape is refuted at the prefix level.**  The key-solver stage's own
  published postcondition forces `m 79 = decoderSavedBase t = 128 + 3t ≠ 0`, i.e. a dirty word
  strictly inside the scratch `[0, decoderAllocEnd t)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 40000
set_option linter.unusedSimpArgs false

open Finset

namespace LinearSetReconciliation327.Main
namespace R66

/-! ## 1. The exact zero region of the copy-in / copy-out layer -/

/-- Memory is zero on the half-open interval `[lo, hi)`. -/
def ZeroOn (m : ℕ → ℕ) (lo hi : ℕ) : Prop := ∀ a, lo ≤ a → a < hi → m a = 0

/-- Memory is zero from `lo` upwards. -/
def ZeroFrom (m : ℕ → ℕ) (lo : ℕ) : Prop := ∀ a, lo ≤ a → m a = 0

/-- The payload of `y` is staged in the words `[β, β + wordsOf W M)`. -/
def PayloadOn (W M β : ℕ) (y : Fin M → ZMod 2) (m : ℕ → ℕ) : Prop :=
  ∀ j, j < wordsOf W M → m (β + j) = packMem W y j

/-- **The honest per-call hypothesis**: zero on `[L, β)` and above `β + L`, where
`L = wordsOf W M`.  This is the published `hzero` *without* the requirement that the
destination window `[0, L)` be clean. -/
def WeakZero (W M β : ℕ) (m : ℕ → ℕ) : Prop :=
  (∀ a, wordsOf W M ≤ a → a < β → m a = 0) ∧ (∀ a, β + wordsOf W M ≤ a → m a = 0)

/-- The published hypothesis of `pinsketch_decoding_at`. -/
def StrongZero (W M β : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ a, (a < β ∨ β + wordsOf W M ≤ a) → m a = 0

/-- The memory produced by the driver's two copy passes: copy `[β, β+L)` to `[0, L)`, then erase
the source by copying the shadow block `[β+L, β+2L)` over it. -/
def layerMem (W M β : ℕ) (y : Fin M → ZMod 2) (m : ℕ → ℕ) : ℕ → ℕ :=
  writeArray β (writeArray 0 m (fun i => m (β + i)) (wordsOf W M))
    (fun i => writeArray 0 m (fun j => m (β + j)) (wordsOf W M) (β + wordsOf W M + i))
    (wordsOf W M)

theorem writeArray_zero_base (m f : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    writeArray 0 m f n i = f i := by
  simpa using writeArray_get 0 m f n i hi

theorem packMem_zero (W M : ℕ) (a : ℕ) : packMem W (0 : Fin M → ZMod 2) a = 0 := by
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases h : p.val / W = a ∧ (0 : Fin M → ZMod 2) p = 1
  · exact absurd h.2 (by simp)
  · simp [h]

theorem hintMem_nil (W M : ℕ) (y : Fin M → ZMod 2) (a : ℕ) :
    hintMem W y ([] : List ℕ) a = if a < wordsOf W M then packMem W y a else 0 := by
  unfold hintMem
  rfl

/-- **The layer lands on the canonical decoder memory under the weak hypothesis.**  This is the
statement `pinsketch_decoding_at`'s proof consumes (`layerMem_eq` in `Sol_p21_decode_at.lean`),
with its `hzero` replaced by `WeakZero`: the destination window `[0, L)` is never inspected. -/
theorem layerMem_eq {W M β : ℕ} {y : Fin M → ZMod 2} {m : ℕ → ℕ}
    (hpay : PayloadOn W M β y m) (hweak : WeakZero W M β m) (hβL : wordsOf W M ≤ β) :
    layerMem W M β y m = hintMem W y ([] : List ℕ) := by
  funext a
  unfold layerMem
  by_cases h1 : a < wordsOf W M
  · rw [writeArray_frame β _ _ _ a (Or.inl (by omega)),
      writeArray_zero_base m (fun i => m (β + i)) _ a h1, hpay a h1]
    rw [hintMem_nil]
    simp [h1]
  · rw [hintMem_nil, if_neg h1]
    by_cases h2 : a < β
    · rw [writeArray_frame β _ _ _ a (Or.inl h2),
        writeArray_frame 0 m _ _ a (Or.inr (by omega))]
      exact hweak.1 a (by omega) h2
    · by_cases h3 : a < β + wordsOf W M
      · have hOut : writeArray β (writeArray 0 m (fun i => m (β + i)) (wordsOf W M))
            (fun i => writeArray 0 m (fun j => m (β + j)) (wordsOf W M)
              (β + wordsOf W M + i)) (wordsOf W M) a
            = writeArray 0 m (fun i => m (β + i)) (wordsOf W M) (a + wordsOf W M) := by
          rw [show a = β + (a - β) from by omega,
            writeArray_get β _ _ _ (a - β) (by omega)]
          congr 1
          omega
        rw [hOut, writeArray_frame 0 m _ _ _ (Or.inr (by omega))]
        exact hweak.2 (a + wordsOf W M) (by omega)
      · rw [writeArray_frame β _ _ _ a (Or.inr (by omega)),
          writeArray_frame 0 m _ _ a (Or.inr (by omega))]
        exact hweak.2 a (by omega)

/-- **The zero conditions are necessary**, not merely sufficient: if the layer lands on `hintMem`
then memory was already zero on `[L, β)` and above `β + L` (the two regions no pass writes). -/
theorem weakZero_of_layerMem {W M β : ℕ} {y : Fin M → ZMod 2} {m : ℕ → ℕ}
    (heq : layerMem W M β y m = hintMem W y ([] : List ℕ)) : WeakZero W M β m := by
  constructor
  · intro a hLa haβ
    have h := congrFun heq a
    unfold layerMem at h
    rw [writeArray_frame β _ _ _ a (Or.inl haβ),
      writeArray_frame 0 m _ _ a (Or.inr (by omega))] at h
    rw [hintMem_nil, if_neg (by omega)] at h
    exact h
  · intro a ha
    have h := congrFun heq a
    unfold layerMem at h
    rw [writeArray_frame β _ _ _ a (Or.inr (by omega)),
      writeArray_frame 0 m _ _ a (Or.inr (by omega))] at h
    rw [hintMem_nil, if_neg (by omega)] at h
    exact h

/-- The published `hzero` implies the weak one. -/
theorem strong_to_weak {W M β : ℕ} {m : ℕ → ℕ} (h : StrongZero W M β m) :
    WeakZero W M β m :=
  ⟨fun a _ ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩

/-- **The exact difference between the published hypothesis and the honest one is the destination
window `[0, L)`** — no more, no less. -/
theorem strongZero_iff {W M β : ℕ} {m : ℕ → ℕ} (hβL : wordsOf W M ≤ β) :
    StrongZero W M β m ↔ WeakZero W M β m ∧ ∀ a, a < wordsOf W M → m a = 0 := by
  constructor
  · intro h
    exact ⟨strong_to_weak h, fun a ha => h a (Or.inl (by omega))⟩
  · rintro ⟨hw, hlow⟩ a (ha | ha)
    · by_cases h : a < wordsOf W M
      · exact hlow a h
      · exact hw.1 a (by omega) ha
    · exact hw.2 a ha

/-- **The weakening is strict, and the relaxed hypothesis is inhabited.**  One word of junk in the
destination window `[0, L)` breaks the published `hzero`, yet the layer still produces the
canonical decoder memory — the junk is overwritten by the payload copy. -/
theorem weakZero_strictly_weaker :
    ∃ (W M β : ℕ) (y : Fin M → ZMod 2) (m : ℕ → ℕ),
      PayloadOn W M β y m ∧ WeakZero W M β m ∧ ¬ StrongZero W M β m ∧
        layerMem W M β y m = hintMem W y ([] : List ℕ) := by
  have hL : wordsOf 8 1 = 1 := by decide
  have h1 : (1 : ℕ) ≠ 0 := by omega
  refine ⟨8, 1, 1, (0 : Fin 1 → ZMod 2), (fun a => if a = 0 then 7 else 0), ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hL] at hj
    interval_cases j
    show (if 1 = 0 then 7 else 0) = packMem 8 (0 : Fin 1 → ZMod 2) 0
    rw [if_neg h1]
    exact (packMem_zero 8 1 0).symm
  · constructor
    · intro a hj1 hj2
      omega
    · intro a ha
      have h2 : a ≠ 0 := by omega
      simp [h2]
  · intro h
    have h0 : (0 : ℕ) < 1 := by omega
    have hbad := h 0 (Or.inl h0)
    simp at hbad
  · refine layerMem_eq (W := 8) (M := 1) (β := 1) (y := (0 : Fin 1 → ZMod 2))
      (m := (fun a => if a = 0 then 7 else 0)) ?_ ?_ (by rw [hL])
    · intro j hj
      rw [hL] at hj
      interval_cases j
      show (if 1 = 0 then 7 else 0) = packMem 8 (0 : Fin 1 → ZMod 2) 0
      rw [if_neg h1]
      exact (packMem_zero 8 1 0).symm
    · constructor
      · intro a hj1 hj2
        omega
      · intro a ha
        have h2 : a ≠ 0 := by omega
        simp [h2]

/-! ## 2. `clearArray_spec`, re-proved against the importable `Definitions`

`clearMem`/`clearState`/`clearCond`/`clearBody`/`clearStmt` live in
`Def_…_DecoderProgram`; the lemmas below are the spans of `Sol_proposition_2_1.lean:5038–5161`
(with the definitions deleted, since they are already declared). -/

theorem clearMem_get (B : ℕ) (m : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    clearMem B m n (B + i) = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : i = n
      · subst i
        simp [clearMem]
      · rw [clearMem, Function.update_of_ne (by omega : B + i ≠ B + n)]
        exact ih (by omega)

theorem clearMem_frame (B : ℕ) (m : ℕ → ℕ) (n a : ℕ)
    (ha : a < B ∨ B + n ≤ a) : clearMem B m n a = m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [clearMem, Function.update_of_ne (by omega : a ≠ B + n)]
      exact ih (by omega)

theorem clearCond_eval (pc B L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) :
    clearCond.eval (clearState pc B L m r j) ↔ j < L := by
  simp [clearCond, Cond.eval, clearState]

theorem clearBody_spec (E : RAMEnv) (pc B L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (j : ℕ) (hj : j < L) (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hB : B + L ≤ 2 ^ E.W) :
    runBlock clearBody E
      { runBlock clearCond.code E (clearState pc B L m r j) with pc := pc + 2 } =
      { clearState pc B L m r (j + 1) with pc := pc + 7 } := by
  have haddr : (B + j) % 2 ^ E.W = B + j := Nat.mod_eq_of_lt (by omega)
  have hnext : (j + 1) % 2 ^ E.W = j + 1 := Nat.mod_eq_of_lt (by omega)
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  apply ramState_eq_of
  · simp only [clearBody, Fin.isValue, Cond.code, clearCond, clearState, runBlock_cons, execInstr,
      ↓reduceIte, one_ne_zero, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
      Function.update_of_ne, Function.update_self, Nat.zero_mod, Nat.add_right_cancel_iff,
      Nat.add_left_cancel_iff] <;> omega
  · simp only [clearBody, Fin.isValue, Cond.code, clearCond, clearState, runBlock_cons, execInstr,
      ↓reduceIte, one_ne_zero, hj, h1, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
      Function.update_of_ne, haddr, Function.update_self, hnext, Nat.zero_mod, clearMem]
  · intro d
    fin_cases d <;>
      simp only [clearBody, Fin.isValue, Cond.code, clearCond, clearState, runBlock_cons, execInstr,
        ↓reduceIte, one_ne_zero, hj, h1, runBlock_nil, ne_eq, Fin.reduceEq, not_false_eq_true,
        Function.update_of_ne, haddr, Function.update_self, hnext, Nat.zero_mod, Fin.zero_eta,
        Nat.add_left_cancel_iff, Fin.mk_one, Fin.reduceFinMk]

theorem clearBodyIter (P : Program) (E : RAMEnv) (pc B L : ℕ)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ) (j : ℕ) (hj : j < L)
    (hAt : At P pc (Stmt.compile clearStmt pc))
    (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W) (hB : B + L ≤ 2 ^ E.W) :
    Sem P E (pc + clearCond.code.length + 1) pc
      { runBlock clearCond.code E (clearState pc B L m r j) with
        pc := pc + clearCond.code.length + 1 }
      (fun k s' => k = 6 ∧ s' = clearState pc B L m r (j + 1)) := by
  obtain ⟨-, -, hbody, hjmp⟩ := at_loop (c := clearCond) (b := .code clearBody) hAt
  have hbodyAt : At P (pc + 2) clearBody := by
    have h := hbody
    rw [show clearCond.code.length = 1 from rfl] at h
    simpa only [Stmt.compile] using h
  have hjmpAt : P[pc + 7]? = some (iJmp pc) := by
    have h := hjmp
    rw [show clearCond.code.length = 1 from rfl, show (Stmt.code clearBody).len = 5 from rfl] at h
    simpa using h
  have hrun : Sem P E (pc + 2) (pc + 7)
      { runBlock clearCond.code E (clearState pc B L m r j) with pc := pc + 2 }
      (fun k s' => k = 5 ∧ s' = { clearState pc B L m r (j + 1) with pc := pc + 7 }) := by
    refine Sem.mono (Sem.block P E (pc + 2) clearBody _ hbodyAt
      (by simp [clearBody]) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    refine ⟨hk, ?_⟩
    rw [hs]
    exact clearBody_spec E pc B L m r j hj hW hL hB
  refine Sem.jmp_append (hAt := hjmpAt) (Sem.mono hrun ?_)
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  refine ⟨by omega, ?_⟩
  rw [hs]
  rfl

theorem clearCond_exit (E : RAMEnv) (pc B L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ) :
    ({ runBlock clearCond.code E (clearState pc B L m r L) with pc := pc + 8 } : RAMState) =
      { clearState pc B L m r L with pc := pc + 8 } := by
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;> simp [clearCond, Cond.code, runBlock_cons, runBlock_nil, execInstr, clearState]

/-- **An actual counted RAM loop clears the array and preserves all memory outside it**, with at
most `8L + 2` steps.  Verbatim `clearArray_spec` of `Sol_proposition_2_1.lean:5138`. -/
theorem clearArray_spec (P : Program) (E : RAMEnv) (pc B L : ℕ)
    (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (hAt : At P pc (Stmt.compile clearStmt pc))
    (hW : 1 < 2 ^ E.W) (hL : L < 2 ^ E.W) (hB : B + L ≤ 2 ^ E.W) :
    Sem P E pc (pc + 8) (clearState pc B L m r 0)
      (fun k s' => k ≤ 8 * L + 2 ∧ s' = { clearState pc B L m r L with pc := pc + 8 }) := by
  have h := Sem.loop P E pc clearCond (.code clearBody) hAt hW L
    (fun j => clearState pc B L m r j) (fun _ => 6)
    (fun _ => rfl)
    (fun j hj => (clearCond_eval pc B L m r j).mpr hj)
    (fun hf => (Nat.lt_irrefl L) ((clearCond_eval pc B L m r L).mp hf))
    (fun j hj => clearBodyIter P E pc B L m r j hj hAt hW hL hB)
  refine Sem.mono h ?_
  intro k s' hQ
  obtain ⟨hcost, hs⟩ := hQ
  refine ⟨?_, ?_⟩
  · have hsum : (∑ j ∈ Finset.range L, (clearCond.code.length + 1 + 6)) = 8 * L := by
      change (∑ j ∈ Finset.range L, (8 : ℕ)) = 8 * L
      exact sum_range_const_mul L 8
    rw [hsum] at hcost
    change k ≤ 2 + 8 * L at hcost
    omega
  · rw [hs]
    exact clearCond_exit E pc B L m r

/-! ### 2.1 A register preamble, and the composed clearing stage -/

/-- The canonical entry registers of `clearStmt`: `r0 = 0`, `r1 = L`, `r2 = B`, `r3 = 1`,
`r4 = 0`, `r14 = 0`, `r15 = 0`. -/
def clearInit (B L : ℕ) : List Instr :=
  [iImm r0 0, iImm r1 L, iImm r2 B, iImm r3 1, iImm r4 0, iImm r14 0, iImm r15 0]

theorem clearInit_length (B L : ℕ) : (clearInit B L).length = 7 := rfl

theorem clearInit_noBranch (B L : ℕ) : NoBranch (clearInit B L) := by
  simp [clearInit, NoBranch, Instr.NoBranchI]

theorem clearInit_run (E : RAMEnv) (pc B L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (hW : 1 < 2 ^ E.W) (hB : B < 2 ^ E.W) (hL : L < 2 ^ E.W) :
    runBlock (clearInit B L) E ⟨pc, r, m⟩ = clearState (pc + 7) B L m r 0 := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  have hB' : B % 2 ^ E.W = B := Nat.mod_eq_of_lt hB
  have hL' : L % 2 ^ E.W = L := Nat.mod_eq_of_lt hL
  apply ramState_eq_of
  · simp only [clearInit, clearState, runBlock_cons, runBlock_nil, execInstr,
      Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
      Fin.isValue] <;> omega
  · rfl
  · intro d
    fin_cases d <;>
      simp only [clearInit, clearState, runBlock_cons, runBlock_nil, execInstr, h1, hB', hL',
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero,
        Nat.zero_mod, ↓reduceIte]

/-- The clearing stage as a `Stmt`: the preamble, then the counted clear loop. -/
def clearFull (B L : ℕ) : Stmt := .seq (.code (clearInit B L)) clearStmt

theorem clearFull_len (B L : ℕ) : (clearFull B L).len = 15 := by
  simp only [clearFull, Stmt.len, clearInit_length, clearStmt, clearCond, clearBody, Cond.code,
    List.length_cons, List.length_nil]

/-- Two runs with bounded costs glue, and the bounds add. -/
theorem Sem.trans_le {P : Program} {E : RAMEnv} {a b c : ℕ} {s : RAMState} {n₁ n₂ : ℕ}
    {s₁ s₂ : RAMState}
    (h₁ : Sem P E a b s (fun k s' => k ≤ n₁ ∧ s' = s₁))
    (h₂ : Sem P E b c s₁ (fun k s' => k ≤ n₂ ∧ s' = s₂)) :
    Sem P E a c s (fun k s' => k ≤ n₁ + n₂ ∧ s' = s₂) := by
  obtain ⟨hpc, k₁, t₁, hs₁, -, hk₁, ht₁⟩ := h₁
  obtain ⟨-, k₂, t₂, hs₂, hc, hk₂, ht₂⟩ := h₂
  refine ⟨hpc, k₁ + k₂, s₂, ?_, ?_, by omega, rfl⟩
  · rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hs₁, ht₁, hs₂, ht₂]
  · rw [← ht₂]
    exact hc

/-- **The clearing stage, from the canonical entry state**: it zeroes `[B, B+L)`, leaves
everything else alone, and costs `8L + 9` steps. -/
theorem clearFull_sem (P : Program) (E : RAMEnv) (pc B L : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (hAt : At P pc (Stmt.compile (clearFull B L) pc))
    (hW : 1 < 2 ^ E.W) (hBs : B < 2 ^ E.W) (hB : B + L ≤ 2 ^ E.W) (hL : L < 2 ^ E.W) :
    Sem P E pc (pc + 15) (⟨pc, r, m⟩ : RAMState)
      (fun k s' => k ≤ 15 + 8 * L ∧
        s' = { clearState (pc + 7) B L m r L with pc := pc + 15 }) := by
  have hseq : At P pc (clearInit B L ++ Stmt.compile clearStmt (pc + (clearInit B L).length)) := by
    simpa only [clearFull, Stmt.compile, Stmt.len] using hAt
  have hsplit := At.append.mp hseq
  rw [clearInit_length] at hsplit
  have hinit : Sem P E pc (pc + 7) (⟨pc, r, m⟩ : RAMState)
      (fun k s' => k ≤ 7 ∧ s' = clearState (pc + 7) B L m r 0) := by
    refine Sem.mono (Sem.block P E pc (clearInit B L) _ hsplit.1
      (clearInit_noBranch B L) rfl) ?_
    intro k s' h
    obtain ⟨hk, hs⟩ := h
    exact ⟨by rw [hk, clearInit_length], hs.trans (clearInit_run E pc B L m r hW hBs hL)⟩
  have hclear : Sem P E (pc + 7) (pc + 7 + 8)
      (clearState (pc + 7) B L m r 0)
      (fun k s' => k ≤ 8 * L + 2 ∧
        s' = { clearState (pc + 7) B L m r L with pc := pc + 7 + 8 }) :=
    clearArray_spec P E (pc + 7) B L m r hsplit.2 hW hL hB
  refine Sem.mono (Sem.trans_le hinit hclear) ?_
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  exact ⟨by omega, hs⟩

/-- **The clearing stage, from any state**: it zeroes `[B, B+L)`, leaves everything else alone,
and costs `8L + 9` steps. -/
theorem clearFull_sem_of {P : Program} {E : RAMEnv} {pc B L : ℕ} {s : RAMState}
    (hAt : At P pc (Stmt.compile (clearFull B L) pc))
    (hW : 1 < 2 ^ E.W) (hBs : B < 2 ^ E.W) (hB : B + L ≤ 2 ^ E.W) (hL : L < 2 ^ E.W)
    (hpc : s.pc = pc) :
    Sem P E pc (pc + 15) s
      (fun k s' => k ≤ 15 + 8 * L ∧
        s' = { clearState (pc + 7) B L s.mem s.regs L with pc := pc + 15 }) := by
  rw [← hpc] at hAt ⊢
  exact clearFull_sem P E s.pc B L s.mem s.regs hAt hW hBs hB hL

/-- **The row loop's clearing pass** at the decoder's own footprint `[0, decoderAllocEnd t)`. -/
theorem clearScratch_sem {P : Program} {E : RAMEnv} {pc t : ℕ} {s : RAMState}
    (hAt : At P pc (Stmt.compile (clearFull 0 (decoderAllocEnd t)) pc))
    (hW : 1 < 2 ^ E.W) (hK : decoderAllocEnd t < 2 ^ E.W) (hpc : s.pc = pc) :
    ∃ k s', k ≤ 15 + 8 * decoderAllocEnd t ∧ (step P E)^[k] s = s' ∧
      (∀ a, a < decoderAllocEnd t → s'.mem a = 0) ∧
      (∀ a, decoderAllocEnd t ≤ a → s'.mem a = s.mem a) ∧ s'.pc = pc + 15 := by
  obtain ⟨-, k, s', hstep, -, hk, hs⟩ :=
    clearFull_sem_of (L := decoderAllocEnd t) hAt hW (Nat.two_pow_pos E.W) (by omega) hK hpc
  refine ⟨k, s', hk, hstep, ?_, ?_, ?_⟩
  · intro a ha
    rw [hs]
    show clearMem 0 s.mem (decoderAllocEnd t) a = 0
    simpa using clearMem_get 0 s.mem (decoderAllocEnd t) a ha
  · intro a ha
    rw [hs]
    show clearMem 0 s.mem (decoderAllocEnd t) a = s.mem a
    simpa using clearMem_frame 0 s.mem (decoderAllocEnd t) a (Or.inr (by omega))
  · rw [hs]

/-- The clearing loop alone costs `8·decoderAllocEnd t + 2 = 64t² + 352t + 1154` steps. -/
theorem clearStmt_cost (t : ℕ) :
    8 * decoderAllocEnd t + 2 = 64 * t * t + 352 * t + 1154 := by
  rw [decoderAllocEnd_eq]
  ring

/-- With its 7-instruction register preamble the pass costs `64t² + 352t + 1167`. -/
theorem clearFull_cost (t : ℕ) :
    15 + 8 * decoderAllocEnd t = 64 * t * t + 352 * t + 1167 := by
  rw [decoderAllocEnd_eq]
  ring

/-! ## 3. Per-iteration maintenance of the weak hypothesis -/

/-- Clearing `[0, K)` and then staging the payload at `β` (with `β + L ≤ K`) re-establishes
`PayloadOn` and `WeakZero`, provided memory at `≥ K` is zero.  Nothing outside `[0, K)` and
`[β, β+L)` is read, so this is the whole precondition maintenance of one iteration. -/
theorem weakZero_restage {W M β K : ℕ} (y : Fin M → ZMod 2) (m : ℕ → ℕ)
    (habove : ∀ a, K ≤ a → m a = 0) (hβK : β + wordsOf W M ≤ K) :
    PayloadOn W M β y (fun a => writeArray β (clearMem 0 m K) (fun j => packMem W y j)
        (wordsOf W M) a) ∧
      WeakZero W M β (fun a => writeArray β (clearMem 0 m K) (fun j => packMem W y j)
        (wordsOf W M) a) := by
  have hpay : PayloadOn W M β y (fun a => writeArray β (clearMem 0 m K)
      (fun j => packMem W y j) (wordsOf W M) a) := by
    intro j hj
    show writeArray β (clearMem 0 m K) (fun j => packMem W y j) (wordsOf W M) (β + j)
      = packMem W y j
    exact writeArray_get β _ _ _ j hj
  refine ⟨hpay, ?_, ?_⟩
  · intro a hLa haβ
    show writeArray β (clearMem 0 m K) (fun j => packMem W y j) (wordsOf W M) a = 0
    rw [writeArray_frame β _ _ _ a (Or.inl haβ)]
    simpa using clearMem_get 0 m K a (by omega)
  · intro a ha
    show writeArray β (clearMem 0 m K) (fun j => packMem W y j) (wordsOf W M) a = 0
    by_cases haK : a < K
    · rw [writeArray_frame β _ _ _ a (Or.inr ha)]
      simpa using clearMem_get 0 m K a haK
    · rw [writeArray_frame β _ _ _ a (Or.inr ha)]
      rw [clearMem_frame 0 m K a (Or.inr (by omega))]
      exact habove a (by omega)

/-- Rows are decoded with the payload staged at `β` and the rest of the scratch cleared, so the
decoder's own canonical start state is reproduced: `layerMem` lands on `hintMem`. -/
theorem layerMem_restage {W M β K : ℕ} (y : Fin M → ZMod 2) (m : ℕ → ℕ)
    (habove : ∀ a, K ≤ a → m a = 0) (hβL : wordsOf W M ≤ β)
    (hβK : β + wordsOf W M ≤ K) :
    layerMem W M β y (fun a => writeArray β (clearMem 0 m K) (fun j => packMem W y j)
        (wordsOf W M) a) = hintMem W y ([] : List ℕ) := by
  obtain ⟨hpay, hweak⟩ := weakZero_restage y m habove hβK
  exact layerMem_eq hpay hweak hβL

/-! ### 3.1 One loop iteration out of its stages

The compiled row body is `setup → clear → decode → repack → inc → jmp`.  `Sem.trans` adds exact
costs, and `Sem.jmp_append` folds in the closing jump back to the loop head. -/

/-- **One iteration of the row loop**, from the body entry `a + 2` back to the head `a`, from its
four sub-stages (setup, clear, decode, repack), the two-instruction counter increment, and the
loop's trailing `jmp`. -/
theorem rowBody_sem {P : Program} {E : RAMEnv} {a : ℕ}
    {s0 s1 s2 s3 s4 s5 : RAMState} {su cl dc rp : ℕ}
    (hjmp : P[a + 2 + su + cl + dc + rp + 2]? = some (iJmp a))
    (h1 : Sem P E (a + 2) (a + 2 + su) s0 (fun k z => k = su ∧ z = s1))
    (h2 : Sem P E (a + 2 + su) (a + 2 + su + cl) s1 (fun k z => k = cl ∧ z = s2))
    (h3 : Sem P E (a + 2 + su + cl) (a + 2 + su + cl + dc) s2 (fun k z => k = dc ∧ z = s3))
    (h4 : Sem P E (a + 2 + su + cl + dc) (a + 2 + su + cl + dc + rp) s3
      (fun k z => k = rp ∧ z = s4))
    (h5 : Sem P E (a + 2 + su + cl + dc + rp) (a + 2 + su + cl + dc + rp + 2) s4
      (fun k z => k = 2 ∧ z = s5)) :
    Sem P E (a + 2) a s0
      (fun k z => k = su + cl + dc + rp + 3 ∧ z = { s5 with pc := a }) := by
  have hchain : Sem P E (a + 2) (a + 2 + su + cl + dc + rp + 2) s0
      (fun k z => k = ((su + cl + dc + rp) + 2) ∧ z = s5) :=
    Sem.trans (Sem.trans (Sem.trans (Sem.trans h1 h2) h3) h4) h5
  refine Sem.jmp_append (Q := fun k z => k = su + cl + dc + rp + 3 ∧ z = { s5 with pc := a })
    hjmp ?_
  refine Sem.mono hchain ?_
  intro k z hz
  obtain ⟨hk, hz'⟩ := hz
  subst hk
  subst hz'
  exact ⟨by omega, rfl⟩

/-- **The `d`-fold row loop closes** as soon as the per-iteration body is a `Sem` from the loop
head back to itself — which is exactly what `rowBody_sem` produces.  This is
`haltsWithin_rowLoop_shape` at `pr = 0`, `Kr = cost`: `d` iterations of a constant-cost body cost
`(cost + 5)·d·lg n`. -/
theorem rowLoop_closes {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {n d : ℕ}
    {s : ℕ → RAMState} {cost : ℕ}
    (hW : 1 < 2 ^ E.W)
    (hpc : ∀ j, (s j).pc = dRowBase Sinit)
    (hgo : ∀ j < d, d65Cond.eval (s j)) (hstop : ¬ d65Cond.eval (s d))
    (hbody : ∀ j < d, Sem (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dRowBase Sinit + d65Cond.code.length + 1) (dRowBase Sinit)
      { runBlock d65Cond.code E (s j) with pc := dRowBase Sinit + d65Cond.code.length + 1 }
      (fun k s' => k = cost ∧ s' = s (j + 1)))
    (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ ((cost : ℝ) + 5) * (d : ℝ) * lg (n : ℝ) ∧
      (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E)^[k] (s 0) = s' ∧
      s'.pc = dColBase Sinit Srow := by
  have hcost : ∀ j < d, (((fun _ => cost) j : ℕ) : ℝ) ≤ (cost : ℝ) * lg (n : ℝ) ^ 0 := by
    intro j hj
    rw [pow_zero, mul_one]
  have h := haltsWithin_rowLoop_shape (cost := fun _ => cost) (Kr := (cost : ℝ)) (pr := 0)
    hW hpc hgo hstop hbody hcost (by positivity) hn hd
  simpa using h

/-! ### 3.2 The frame above the scratch: the one fact the published interface drops

The accepted `verifierProcedure_spec` (`Sol_proposition_2_1.lean:15341–15359`) concludes
`MemoryFrame (verifierWritable V (2*t)) m m'`.  The published `pinsketch_decoder_verifier` (C5)
kept only `decoderPost` and **dropped that conjunct**.  Since
`verifierWritable (decoderVerifyBase t) (2*t)` is contained in `[0, decoderAllocEnd t)`, the frame
is exactly "the verifier leaves memory at `≥ decoderAllocEnd t` alone".  These two lemmas make
that reduction, and the generic preservation step, explicit. -/

/-- The verifier frame implies invariance of everything above the decoder's scratch. -/
theorem verifierFrame_above {m m' : ℕ → ℕ} {t : ℕ}
    (h : MemoryFrame (verifierWritable (decoderVerifyBase t) (2 * t)) m m') :
    ∀ a, decoderAllocEnd t ≤ a → m' a = m a := by
  have hK : (121 : ℕ) < decoderAllocEnd t := by
    rw [decoderAllocEnd_eq]
    have h0 : 8 * t * t + 44 * t ≥ 0 := Nat.zero_le _
    omega
  intro a ha
  refine h a (fun hw => ?_)
  unfold verifierWritable verifierCoreWritable at hw
  have hE : decoderVerifyBase t + 2 * t = decoderAllocEnd t := rfl
  omega

/-- **A frame whose writable set stays inside `[0, K)` preserves zero above `K`.**  This is the
step that turns the three stage frames (`solverInitWritable`, `rootSearchWritable`,
`verifierWritable`, all inside the scratch) into "the decoder never dirties `[K, ∞)`". -/
theorem zero_above_of_frame {K : ℕ} {A : ℕ → Prop} {m m' : ℕ → ℕ}
    (hA : ∀ a, A a → a < K) (hframe : MemoryFrame A m m')
    (hzero : ∀ a, K ≤ a → m a = 0) :
    ∀ a, K ≤ a → m' a = 0 := by
  intro a ha
  have hnot : ¬ A a := fun hc => absurd (hA a hc) (by omega)
  rw [hframe a hnot]
  exact hzero a ha

/-! ## 4. The scratch is provably dirty after the key-solver stage

`pinsketch_decoder_key_solver`'s own postcondition contains `KeyReady`, whose `savedBase` field
reads `m 79 = decoderSavedBase t = 128 + 3t`.  Slot `79` is strictly inside the decoder's scratch
`[0, decoderAllocEnd t)`.  So "the decoder is idempotent on its scratch" is false at the
read + key-solver prefix: at least one word of the scratch is nonzero, for *every* input.  (The
published postcondition of the last stage, `pinsketch_decoder_verifier`, constrains memory only
through `outList`, i.e. the `regs 1` output words at `regs 0`; it says nothing about the rest of
the scratch, so no zero-after-run statement is derivable from the platform interface.) -/

theorem keySolver_scratch_dirty {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {w : ℕ} {b : Module.Basis (Fin w) (ZMod 2) F} {E : RAMEnv} {t N : ℕ} {e : ℕ → F}
    {m : ℕ → ℕ} (h : KeyReady b E t N e m) :
    ∃ a, a < decoderAllocEnd t ∧ m a ≠ 0 := by
  refine ⟨79, ?_, ?_⟩
  · rw [decoderAllocEnd_eq]; omega
  · rw [h.savedBase]
    unfold decoderSavedBase
    omega

/-- The same, directly from the published stage theorem: *every* run of the key-solver stage ends
with a nonzero word strictly inside the scratch. -/
theorem keySolver_post_dirty {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ)
    (P : Program) (E : RAMEnv) (pc : ℕ) (e : ℕ → F) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile keySolverProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : E.det = detStd t N b ι) (ht : 1 ≤ t)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (h0 : ι 0 ≠ 0)
    (hh0 : E.det 0 % 2 ^ E.W = t) (hh1 : E.det 1 % 2 ^ E.W = w)
    (hh2 : E.det 2 % 2 ^ E.W = N)
    (hSaved : FieldArrayStored b m (decoderSavedBase t) (2 * t) e)
    (hTail : ∀ addr, decoderSavedBase t + 2 * t ≤ addr → m addr = 0) :
    ∃ (k : ℕ) (m' : ℕ → ℕ), k ≤ (34 * decoderCapacity t +
        (48 * decoderLength t + 187) * decoderLength t + 289) * decoderLength t +
        12 * decoderCapacity t + 385 ∧
      KeyReady b E t N e m' ∧ ∃ a, a < decoderAllocEnd t ∧ m' a ≠ 0 := by
  obtain ⟨-, k, z, hstep, -, hQ⟩ :=
    pinsketch_decoder_key_solver b ι t N P E pc e m hAt hw hW hdet ht hEnd h0 hh0 hh1 hh2 hSaved hTail
  obtain ⟨hk, m', -, hready, -⟩ := hQ
  exact ⟨k, m', hk, hready, keySolver_scratch_dirty hready⟩

/-- **The slot-79 obstruction bites the *weakened* hypothesis too**, whenever the payload base `β`
lies above the decoder's saved-syndrome block.  For `L = wordsOf W (t*w) ≤ 79` the cell `79` is in
the required-zero region `[L, β)` and is nonzero. -/
theorem keySolver_blocks_weakZero {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {w : ℕ} {b : Module.Basis (Fin w) (ZMod 2) F} {E : RAMEnv} {t N : ℕ} {e : ℕ → F}
    {m : ℕ → ℕ} {β W : ℕ} (h : KeyReady b E t N e m)
    (hL : wordsOf W (t * w) ≤ 79) (hβ : 79 < β) :
    ¬ WeakZero W (t * w) β m := by
  intro hw
  have h0 : m 79 = 0 := hw.1 79 hL hβ
  rw [h.savedBase] at h0
  unfold decoderSavedBase at h0
  omega

end R66
end LinearSetReconciliation327.Main


