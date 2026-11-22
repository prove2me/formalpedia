-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrStageDet20261122
-- name    : LinearSetReconciliation327_Main_CrStageDet20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:27:29.411902+00:00
-- url     : https://prove2.me/theorems/8d49ff5a-61ea-47b7-8806-85e0b23ecd18
-- title:
--   Row-stage mirror: the `CR` stage, free of `DecoderLemmas`
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_CrStageDet20261122` of the Theorem 6.5 development.  It is a re-hosted mirror of the project's published row-stage bundle with only the recorded edits (the import of the `DecoderLemmas` side replaced by the `P21DetBndComp` chain, and — for the `Pay` mirrors — the per-row payload base re-pointed to the arithmetic progression `payTabAddr + j * stageLen`); the statements of the row chain are byte-identical.  It contains definitions and fully proved lemmas only (no `sorry`, no new axiom) and exists so that the later nodes of the chain compile inside the platform's per-definition budget.  This is a supporting node, not a statement of independent mathematical interest.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder) and Proposition 2.1 (the base-relative decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Top65DecDet20261122
import Definitions.Def_LinearSetReconciliation327_Main_CR23Dec

/-!
# `CrStage` — Theorem 6.5's `cr` stage: Proposition 2.3's decoder, then the merge

This bundle assembles the `cr` stage of the top-level decoder of §9.2 *inside* `progDecOfTop`:

```
Scr = .seq (2.3's decoder as a Stmt) mrgStmtFull
```

and proves

* **the placement** — `Scr` occupies `[dCrBase, dCrBase + Scr.len)` and the merge program occupies
  exactly `[dCrBase + Sdec.len, dCrBase + Sdec.len + 86)` (`at_scrStage`, `at_scrStage_dec`,
  `at_scrStage_mrg`), with the address arithmetic `dEnd = dCrBase + Sdec.len + 86`
  (`dEnd_scrStage`);
* **the composed `StageRun`** from `dCrBase` to `dEnd`, on the named intermediate state
  `CrMergeIn` (2.3's decoded residual in the decoder's output window, the estimate `x̂` at
  `[ab, ab+al)`, and the merge's five arguments in `r10 … r14`), with cost
  `Tdec + mrgCost al bl` (`stageRun_crMerge`, and `stageRun_cr23Merge` at 2.3's own `Stmt`);
* **the residual identity** `x̂ △ ê = x`, both as pure set algebra (`residual_identity`) and as the
  reading of `Node.residual … = some x` (`residual_eq_of_node_residual`);
* **the corrected `cr` field** of `TopDecRuns`, in a *new* structure `TopDecRunsCR`
  (the published `TopDecRuns` is untouched), together with the proof that weakening it back gives
  the published structure and hence conjunct 7 (`TopDecRunsCR.toTopDecRuns`,
  `haltsWithin_topDec_of_runsCR`);
* **non-vacuity**: `CrMergeIn` is inhabited at the merge witnesses (`crMergeIn_witness`), the
  composed `StageRun` *applies* there and outputs `{5} △ {7} = {5,7}` (`stageRun_crMerge_witness`),
  and the degenerate `A = B = []` instance is inhabited (`crMergeIn_degenerate`).

The relocation layer of `Solutions/_65_reloc_block.lean` (§1–4 and §6.3, lines 37–415 and 589–611) is
copied **byte-identically** below; `crs/gen.py` asserts the two spans and their boundary markers.
Nothing from `Solutions.*` is imported: the bundle's imports are `Mathlib`, the published
`Definitions.Def_…_Top65Dec`, `Definitions.Def_…_MergeStep20261121` and
`Definitions.Def_…_CR23Dec` (which supplies 2.3's `decStmt`/`progDec`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace CRS

/-! ## 0. A `StageRun` weakening rule (the two `StageRun` combinators live in `Top65Dec`) -/

/-- Weakening a stage's postcondition. -/
theorem stageRun_post {P : Program} {E : RAMEnv} {a b : ℕ} {T : ℝ} {I Q Q' : RAMState → Prop}
    (h : StageRun P E a b T I Q) (hQ : ∀ s, Q s → Q' s) : StageRun P E a b T I Q' := by
  intro s hpc hI
  obtain ⟨k, s', hk, hstep, hb, hQ'⟩ := h s hpc hI
  exact ⟨k, s', hk, hstep, hb, hQ s' hQ'⟩

/-! ## 1. Relocating a program counter -/

/-- Set the program counter, leaving registers and memory untouched. -/
def withPc (k : ℕ) (s : RAMState) : RAMState := { s with pc := k }

theorem withPc_def (k : ℕ) (s : RAMState) : withPc k s = ⟨k, s.regs, s.mem⟩ := rfl

@[simp] theorem withPc_pc (k : ℕ) (s : RAMState) : (withPc k s).pc = k := rfl

@[simp] theorem withPc_regs (k : ℕ) (s : RAMState) : (withPc k s).regs = s.regs := rfl

@[simp] theorem withPc_mem (k : ℕ) (s : RAMState) : (withPc k s).mem = s.mem := rfl

theorem withPc_congr {k : ℕ} {s : RAMState} (h : s.pc = k) : withPc k s = s := by
  rw [withPc_def, ← h]

theorem withPc_withPc_of {k l : ℕ} {s : RAMState} (h : s.pc = k) :
    withPc k (withPc l s) = s := by
  rw [withPc_def, withPc_def, ← h]

/-- Relocate one instruction: its absolute jump targets move by `d`.  Everything else is unchanged
(and `halt` is unchanged, which is why a `halt` cannot be relocated *past*). -/
def iShift (d : ℕ) : Instr → Instr
  | .jz r t => .jz r (t + d)
  | .jmp t => .jmp (t + d)
  | i => i

@[simp] theorem iShift_jz (d : ℕ) (r : Fin 16) (t : ℕ) : iShift d (.jz r t) = .jz r (t + d) := rfl

@[simp] theorem iShift_jmp (d : ℕ) (t : ℕ) : iShift d (.jmp t) = .jmp (t + d) := rfl

/-- Does the instruction jump (absolutely)? -/
def iHasJump : Instr → Bool
  | .jz _ _ => true
  | .jmp _ => true
  | _ => false

/-- Is the instruction the terminal `halt`? -/
def iIsHalt : Instr → Bool
  | .halt => true
  | _ => false

/-- Every straight-line chunk of the statement is jump-free, so `compile` is a pure relocation. -/
def sNoJumpB : Stmt → Bool
  | .code l => l.all (fun i => !iHasJump i)
  | .seq a b => sNoJumpB a && sNoJumpB b
  | .ite _ a b => sNoJumpB a && sNoJumpB b
  | .loop _ b => sNoJumpB b

/-- The statement's compiled form contains no `halt`, so the appended `halt` is its only one. -/
def sHaltFreeB : Stmt → Bool
  | .code l => l.all (fun i => !iIsHalt i)
  | .seq a b => sHaltFreeB a && sHaltFreeB b
  | .ite _ a b => sHaltFreeB a && sHaltFreeB b
  | .loop _ b => sHaltFreeB b

theorem iShift_eq_self {d : ℕ} {i : Instr} (h : iHasJump i = false) : iShift d i = i := by
  cases i <;> simp_all [iHasJump, iShift]

theorem list_map_iShift_eq_self {l : List Instr} (h : l.all (fun i => !iHasJump i) = true) (d : ℕ) :
    l.map (iShift d) = l := by
  induction l with
  | nil => rfl
  | cons i t ih =>
      rw [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rw [List.map_cons, ih h2, iShift_eq_self (by simpa using h1)]

theorem Cond_code_noJump (c : Cond) : c.code.all (fun i => !iHasJump i) = true := by
  cases c <;> rfl

theorem Cond_code_noHalt (c : Cond) : c.code.all (fun i => !iIsHalt i) = true := by
  cases c <;> rfl

theorem Cond_code_map (c : Cond) (d : ℕ) : c.code.map (iShift d) = c.code := by
  cases c <;> rfl

/-! ### 1.1 `compile` is a relocation -/

/-- **A compiled block at `a + b` is the block at `a` with every jump target moved by `b`.**  The
induction is the compiler's own recursion; the straight-line chunks being jump-free (`sNoJumpB`) is the
only side condition. -/
theorem Stmt_compile_shift (S : Stmt) (h : sNoJumpB S = true) (a b : ℕ) :
    S.compile (a + b) = (S.compile a).map (iShift b) := by
  induction S generalizing a b with
  | code l => exact (list_map_iShift_eq_self h b).symm
  | seq x y ihx ihy =>
      change (sNoJumpB x && sNoJumpB y) = true at h
      rw [Bool.and_eq_true] at h
      obtain ⟨hx, hy⟩ := h
      rw [Stmt.compile, Stmt.compile]
      simp only [List.map_append]
      rw [← ihx hx a b, ← ihy hy (a + x.len) b,
        show a + b + x.len = (a + x.len) + b from by omega]
  | ite c x y ihx ihy =>
      change (sNoJumpB x && sNoJumpB y) = true at h
      rw [Bool.and_eq_true] at h
      obtain ⟨hx, hy⟩ := h
      rw [Stmt.compile, Stmt.compile]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [Cond_code_map, iShift_jz, iShift_jmp,
        ← ihx hx (a + c.code.length + 1) b,
        ← ihy hy (a + c.code.length + x.len + 2) b,
        show a + b + c.code.length + 1 = (a + c.code.length + 1) + b from by omega,
        show a + b + c.code.length + x.len + 2 = (a + c.code.length + x.len + 2) + b from by omega,
        show a + b + c.code.length + x.len + y.len + 3 =
          (a + c.code.length + x.len + y.len + 3) + b from by omega]
  | loop c x ihx =>
      have hx : sNoJumpB x = true := h
      rw [Stmt.compile, Stmt.compile]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [Cond_code_map, iShift_jz, iShift_jmp,
        ← ihx hx (a + c.code.length + 1) b,
        show a + b + c.code.length + 1 = (a + c.code.length + 1) + b from by omega,
        show a + b + c.code.length + x.len + 2 = (a + c.code.length + x.len + 2) + b from by omega]

/-- The relocation in the form the transport uses: the block at `base` is the block at `0` shifted. -/
theorem Stmt_compile_eq_shift (S : Stmt) (h : sNoJumpB S = true) (base : ℕ) :
    S.compile base = (S.compile 0).map (iShift base) := by
  simpa using Stmt_compile_shift S h 0 base

/-- **The lookup form of the relocation**, read off an `At` fact for the block inside `G`. -/
theorem At_lookup_shift {G : Program} {S : Stmt} {base : ℕ} (hAt : At G base (S.compile base))
    (h : sNoJumpB S = true) :
    ∀ n, n < S.len → G[n + base]? = ((S.compile 0)[n]?).map (iShift base) := by
  intro n hn
  have hn' : n < (S.compile base).length := by rw [Stmt.length_compile]; exact hn
  rw [Nat.add_comm n base, hAt n hn', Stmt_compile_eq_shift S h base]
  simp

/-! ## 2. One step, and `k` steps, inside the window -/

theorem state_eq_of {a b : RAMState} (h1 : a.pc = b.pc) (h2 : a.regs = b.regs) (h3 : a.mem = b.mem) :
    a = b := by
  cases a with
  | mk pa ra ma =>
    cases b with
    | mk pb rb mb =>
      simp only [RAMState.mk.injEq] at h1 h2 h3 ⊢
      exact ⟨h1, h2, h3⟩

/-- **One instruction at a relocated address.**  `iShift` is exactly what makes this hold: the jump
targets move with the program counter, everything else is untouched. -/
theorem execInstr_shift (i : Instr) (d : ℕ) (E : RAMEnv) (p : ℕ) (r : Fin 16 → ℕ)
    (m : ℕ → ℕ) :
    execInstr (iShift d i) E ⟨p + d, r, m⟩
      = withPc ((execInstr i E ⟨p, r, m⟩).pc + d) (execInstr i E ⟨p, r, m⟩) := by
  cases i <;> refine state_eq_of ?_ ?_ ?_ <;>
    simp only [iShift, execInstr, withPc] <;>
    (try split_ifs) <;>
    (first | rfl | omega)

/-- **One step at a relocated address.**  Below `P.length` the composite `G` agrees with `P` up to the
address offset `base`, so a step of `G` is a step of `P` with `base` added to the program counter. -/
theorem step_window {G P : Program} {base : ℕ} {E : RAMEnv}
    (hAt : ∀ n, n < P.length → G[n + base]? = (P[n]?).map (iShift base))
    {s : RAMState} (hpc : s.pc < P.length) :
    step G E (withPc (s.pc + base) s) = withPc ((step P E s).pc + base) (step P E s) := by
  have hg : G[s.pc + base]? = (P[s.pc]?).map (iShift base) := hAt s.pc hpc
  cases h : P[s.pc]? with
  | none =>
      have hgn : G[s.pc + base]? = none := by rw [hg, h]; rfl
      simp only [step, h, hgn, withPc]
  | some i =>
      have hgs : G[s.pc + base]? = some (iShift base i) := by rw [hg, h]; rfl
      rw [step_eq_execInstr G E _ _ hgs, step_eq_execInstr P E s i h]
      exact execInstr_shift i base E s.pc s.regs s.mem

/-- **`k` steps at a relocated address**, as long as every intermediate state is still inside the
window.  The last step is covered too: the state it leaves is `P`'s own, with `base` added. -/
theorem iterate_window {G P : Program} {base : ℕ} {E : RAMEnv}
    (hAt : ∀ n, n < P.length → G[n + base]? = (P[n]?).map (iShift base)) :
    ∀ (k : ℕ) (s : RAMState), s.pc < P.length →
      (∀ i < k, ((step P E)^[i] s).pc < P.length) →
      (step G E)^[k] (withPc (s.pc + base) s)
        = withPc (((step P E)^[k] s).pc + base) ((step P E)^[k] s) := by
  intro k
  induction k with
  | zero => intro s hpc hwin; rfl
  | succ k ih =>
      intro s hpc hwin
      have hv : ((step P E)^[k] s).pc < P.length := hwin k (Nat.lt_succ_self k)
      rw [Function.iterate_succ_apply', ih s hpc (fun i hi => hwin i (Nat.lt_succ_of_lt hi)),
        step_window hAt hv, Function.iterate_succ_apply']

/-! ## 3. Where the appended `halt` is -/

theorem step_agree_below {P : Program} {E : RAMEnv} {s : RAMState} (h : s.pc < P.length) :
    step (P ++ [Instr.halt]) E s = step P E s := by
  have hg : (P ++ [Instr.halt])[s.pc]? = P[s.pc]? := List.getElem?_append_left h
  simp only [step, hg]

theorem step_append_halt_of_le {P : Program} {E : RAMEnv} {s : RAMState} (h : P.length ≤ s.pc) :
    step (P ++ [Instr.halt]) E s = s := by
  rcases eq_or_lt_of_le h with he | hlt
  · have h1 : (P ++ [Instr.halt])[s.pc]? = some Instr.halt := by
      rw [← he]; simp
    simp only [step, h1]
  · have h1 : (P ++ [Instr.halt])[s.pc]? = none := by
      rw [List.getElem?_append_right (le_of_lt hlt)]
      rw [show s.pc - P.length = (s.pc - P.length - 1) + 1 from by omega]
      simp
    simp only [step, h1]

theorem halted_lookup {P : Program} {s : RAMState} (h : Halted P s) :
    P[s.pc]? = some Instr.halt := by
  unfold Halted at h
  cases hp : P[s.pc]? with
  | none => simp [hp] at h
  | some i => cases i <;> simp_all

/-- A halt-free block's compiled form has no `halt`. -/
theorem all_noHalt_compile (S : Stmt) (h : sHaltFreeB S = true) (base : ℕ) :
    (S.compile base).all (fun i => !iIsHalt i) = true := by
  induction S generalizing base with
  | code l => exact h
  | seq x y ihx ihy =>
      change (sHaltFreeB x && sHaltFreeB y) = true at h
      rw [Bool.and_eq_true] at h
      obtain ⟨hx, hy⟩ := h
      rw [Stmt.compile, List.all_append, ihx hx base, ihy hy (base + x.len), Bool.and_self]
  | ite c x y ihx ihy =>
      change (sHaltFreeB x && sHaltFreeB y) = true at h
      rw [Bool.and_eq_true] at h
      obtain ⟨hx, hy⟩ := h
      rw [Stmt.compile, List.all_append, List.all_append, List.all_append, List.all_append,
        List.all_append, ihx hx (base + c.code.length + 1),
        ihy hy (base + c.code.length + x.len + 2), Cond_code_noHalt]
      simp [iIsHalt]
  | loop c x ihx =>
      have hx : sHaltFreeB x = true := h
      rw [Stmt.compile, List.all_append, List.all_append, List.all_append,
        ihx hx (base + c.code.length + 1), Cond_code_noHalt]
      simp [iIsHalt]

theorem lookup_ne_halt_of_all {l : List Instr} (h : l.all (fun i => !iIsHalt i) = true) (n : ℕ) :
    l[n]? ≠ some Instr.halt := by
  rw [List.all_eq_true] at h
  intro hc
  have hmem : Instr.halt ∈ l := List.mem_of_getElem? hc
  have := h Instr.halt hmem
  simp [iIsHalt] at this

/-- **The appended `halt` sits at `S.len`.**  So a halted state of `programOfStatement S` has program
counter exactly `S.len`, which is the address at which `compile` puts the halt. -/
theorem haltPc_of_haltFree {S : Stmt} (h : sHaltFreeB S = true) {s : RAMState}
    (hh : Halted (programOfStatement S) s) : s.pc = S.len := by
  have hp : (S.compile 0 ++ [Instr.halt])[s.pc]? = some Instr.halt := halted_lookup hh
  have hlen : (S.compile 0).length = S.len := Stmt.length_compile S 0
  rcases lt_trichotomy s.pc S.len with h1 | h2 | h3
  · have hl : (S.compile 0)[s.pc]? = some Instr.halt := by
      rw [← List.getElem?_append_left (show s.pc < (S.compile 0).length by rw [hlen]; exact h1)]
      exact hp
    exact absurd hl (lookup_ne_halt_of_all (all_noHalt_compile S h 0) s.pc)
  · exact h2
  · have hn : (S.compile 0 ++ [Instr.halt])[s.pc]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      rw [List.length_append, hlen]
      simp only [List.length_singleton]
      omega
    rw [hn] at hp
    exact absurd hp (by simp)

/-- **The arrival index of a halted run.**  From a `HaltsWithin` of `P ++ [halt]` whose halted state has
program counter `P.length`, the run of `P` alone reaches the same state, and every *earlier* state is
strictly inside `P` — which is what lets `iterate_window` be applied. -/
theorem exists_arrival {P : Program} {E : RAMEnv} {T : ℝ} {s s' : RAMState}
    (h : HaltsWithin (P ++ [Instr.halt]) E T s s') :
    ∃ k : ℕ, (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧
      ∀ i < k, ((step P E)^[i] s).pc < P.length := by
  classical
  obtain ⟨k₀, hk₀, hrun, -⟩ := h
  let u : ℕ → RAMState := fun i => (step (P ++ [Instr.halt]) E)^[i] s
  have hu : ∀ i, u i = (step (P ++ [Instr.halt]) E)^[i] s := fun i => rfl
  have hus : ∀ i, u (i + 1) = step (P ++ [Instr.halt]) E (u i) := by
    intro i; rw [hu, Function.iterate_succ_apply', hu]
  have hex : ∃ i, u i = s' := ⟨k₀, hrun⟩
  have huk : u (Nat.find hex) = s' := Nat.find_spec hex
  have hmin : ∀ i < Nat.find hex, u i ≠ s' := fun i hi => Nat.find_min hex hi
  have hkle : Nat.find hex ≤ k₀ := Nat.find_min' hex hrun
  have hfreeze : ∀ j, P.length ≤ (u j).pc → u (j + 1) = u j := by
    intro j hj
    rw [hus j]
    exact step_append_halt_of_le hj
  have hconst : ∀ j i, i ≤ j → P.length ≤ (u i).pc → u j = u i := by
    intro j i hji hge
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hji
    have hmono : ∀ m, u (i + m) = u i ∧ P.length ≤ (u (i + m)).pc := by
      intro m
      induction m with
      | zero => exact ⟨by rw [Nat.add_zero], hge⟩
      | succ m ih =>
          obtain ⟨h1, h2⟩ := ih
          have h3 : u (i + (m + 1)) = u ((i + m) + 1) := by
            rw [show i + (m + 1) = (i + m) + 1 from by omega]
          refine ⟨?_, ?_⟩
          · rw [h3, hfreeze (i + m) h2, h1]
          · rw [h3, hfreeze (i + m) h2]; exact h2
    rw [hm]
    exact (hmono m).1
  have hwin : ∀ i < Nat.find hex, (u i).pc < P.length := by
    intro i hi
    by_contra hge
    have hge : P.length ≤ (u i).pc := not_lt.mp hge
    exact hmin i hi (by rw [← hconst (Nat.find hex) i (le_of_lt hi) hge]; exact huk)
  have hagree : ∀ i ≤ Nat.find hex, u i = (step P E)^[i] s := by
    intro i hik
    induction i with
    | zero => rw [hu]; rfl
    | succ j ihj =>
        have hj : j < Nat.find hex := by omega
        have h1 : (u j).pc < P.length := hwin j hj
        have h1' : ((step P E)^[j] s).pc < P.length := by rw [← ihj (by omega)]; exact h1
        have h2 : u (j + 1) = step (P ++ [Instr.halt]) E ((step P E)^[j] s) := by
          rw [hus j, ihj (by omega)]
        rw [h2, step_agree_below (s := (step P E)^[j] s) h1']
        exact (Function.iterate_succ_apply' (step P E) j s).symm
  refine ⟨Nat.find hex, (Nat.cast_le.mpr hkle).trans hk₀, ?_, ?_⟩
  · rw [← hagree (Nat.find hex) le_rfl, huk]
  · intro i hi
    rw [← hagree i (le_of_lt hi)]
    exact hwin i hi

/-! ## 4. The relocation lemma -/

/-- **The program-counter relocation, pointwise.**  A run of `S.compile 0 ++ [halt]` from `pc = 0` that
halts at `pc = S.len` is a run of `S.compile base` inside `G` from `pc = base`, at the same cost, with
the same registers and memory, and with `base` added to the program counter. -/
theorem run_transport {G : Program} {S : Stmt} {base : ℕ} {E : RAMEnv} {T : ℝ} {s s' : RAMState}
    (hAt : At G base (S.compile base)) (hno : sNoJumpB S = true)
    (h : HaltsWithin (programOfStatement S) E T s s') (hpc : s.pc = 0) (hhalt : s'.pc = S.len) :
    ∃ k : ℕ, (k : ℝ) ≤ T ∧ (step G E)^[k] (withPc base s) = withPc (base + S.len) s' := by
  have hlen : (S.compile 0).length = S.len := Stmt.length_compile S 0
  have hAt' : ∀ n, n < (S.compile 0).length →
      G[n + base]? = ((S.compile 0)[n]?).map (iShift base) := by
    intro n hn
    exact At_lookup_shift (S := S) hAt hno n (by rwa [← hlen])
  obtain ⟨k, hk, hrun, hwin⟩ := exists_arrival (P := S.compile 0) h
  have hbase : s.pc + base = base := by rw [hpc, Nat.zero_add]
  rcases k with _ | k
  · have hs' : s' = s := by rw [← hrun, Function.iterate_zero_apply]
    have hlen0 : S.len = 0 := by rw [← hhalt, hs', hpc]
    refine ⟨0, hk, ?_⟩
    simp only [Function.iterate_zero_apply]
    rw [withPc_def, withPc_def, hlen0, hs']
    simp
  · have hpc0 : s.pc < (S.compile 0).length := by
      have := hwin 0 (Nat.succ_pos k)
      simpa using this
    have htr := iterate_window hAt' (k + 1) s hpc0 hwin
    rw [hbase] at htr
    refine ⟨k + 1, hk, ?_⟩
    rw [htr, hrun, hhalt, withPc_def, withPc_def]
    simp [Nat.add_comm]

/-- **The relocation lemma.**  If every state at `pc = 0` satisfying `Pre` — read after the address
offset is put back, which is how a pc-blind platform precondition is transported — has a run of
`programOfStatement S` inside `T` steps whose relocation satisfies `Post`, then `S.compile base` inside
`G` is a `StageRun` from `base` to `base + S.len` with the same bound.

This is the `∀`-closure of the pointwise statement: `StageRun` quantifies over the entry state, and the
platform theorems' hypotheses are pc-blind, so `Pre (withPc base s)` is exactly the platform statement's
own precondition at `pc = 0`. -/
theorem stageRun_of_haltsWithin_shift
    {G : Program} {S : Stmt} {base : ℕ} {E : RAMEnv} {T : ℝ} {Pre Post : RAMState → Prop}
    (hAt : At G base (S.compile base)) (hno : sNoJumpB S = true) (hhf : sHaltFreeB S = true)
    (h : ∀ s : RAMState, s.pc = 0 → Pre (withPc base s) →
      ∃ s' : RAMState, HaltsWithin (programOfStatement S) E T s s' ∧
        Post (withPc (base + S.len) s')) :
    StageRun G E base (base + S.len) T Pre Post := by
  intro t htpc hPre
  have ht : withPc base (withPc 0 t) = t := withPc_withPc_of htpc
  have hpre : Pre (withPc base (withPc 0 t)) := by rw [ht]; exact hPre
  obtain ⟨s', ⟨k', hk', hrun', hhalted⟩, hPost⟩ := h (withPc 0 t) rfl hpre
  have hH : HaltsWithin (programOfStatement S) E T (withPc 0 t) s' := ⟨k', hk', hrun', hhalted⟩
  have hhalt : s'.pc = S.len := haltPc_of_haltFree hhf hhalted
  obtain ⟨k, hk, hrun⟩ := run_transport hAt hno hH rfl hhalt
  refine ⟨k, withPc (base + S.len) s', hk, ?_, by simp, hPost⟩
  rw [← hrun, ht]

/-! ### 6.3 — what the pipeline needs from 2.3: a compiled block

The merge glues as soon as the child is a `Stmt` (`ScrBlock`), because then `compile` relocates it. -/

/-- **The composable `Scr`**: 2.3's decoder as a compiled *block* plus the merge. -/
def ScrBlock (Sdec Smerge : Stmt) : Stmt := .seq Sdec Smerge

theorem ScrBlock_len (Sdec Smerge : Stmt) :
    (ScrBlock Sdec Smerge).len = Sdec.len + Smerge.len := rfl

/-- **The two halves glue once the child is a compiled block.**  `hdec` is 2.3's statement in the
pc-blind form the relocation lemma consumes; `hmerge` is the merge's `StageRun` at the address
`compile` gives it. -/
theorem stageRun_scrBlock {G : Program} {Sdec Smerge : Stmt} {base : ℕ} {E : RAMEnv}
    {Tdec Tmg : ℝ} {Pre Mid Post : RAMState → Prop}
    (hAt : At G base (Sdec.compile base)) (hno : sNoJumpB Sdec = true)
    (hhf : sHaltFreeB Sdec = true)
    (hdec : ∀ s : RAMState, s.pc = 0 → Pre (withPc base s) →
      ∃ s', HaltsWithin (programOfStatement Sdec) E Tdec s s' ∧ Mid (withPc (base + Sdec.len) s'))
    (hmerge : StageRun G E (base + Sdec.len) (base + Sdec.len + Smerge.len) Tmg Mid Post) :
    StageRun G E base (base + (ScrBlock Sdec Smerge).len) (Tdec + Tmg) Pre Post := by
  have h1 := stageRun_of_haltsWithin_shift hAt hno hhf hdec
  simpa [ScrBlock_len, Nat.add_assoc] using h1.trans hmerge
end CRS
end LinearSetReconciliation327.Main


