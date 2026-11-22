-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrStage20261122
-- name    : LinearSetReconciliation327_Main_CrStage20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T07:03:20.529066+00:00
-- url     : https://prove2.me/theorems/7297bbf9-443b-4137-96b8-f9efe87f426f
-- title:
--   Theorem 6.5's CR stage: 2.3's decoder, then the merge
-- statement:
--   This bundle assembles the `cr` stage of Theorem 6.5 inside `progDecOfTop` as the composite statement $S_{cr} = \mathrm{seq}\;S_{\mathrm{dec}}\;S_{\mathrm{merge}}$, proves that it occupies the interval $[d_{cr}, d_{cr}+282+86)$ exactly (2.3's decoder plus the merge's 86 instructions land on the trailing `halt`), and proves the composed `StageRun` from $d_{cr}$ to the end, with cost $T_{\mathrm{dec}} + \mathrm{mrgCost}\,a_l\,b_l$, on a named intermediate state `CrMergeIn` that carries 2.3's decoded residual in the decoder's output window and the estimate as an explicit coordinate list.  It also proves the residual identity $\hat x \triangle \hat e = x$, states the corrected `cr` field of a new structure `TopDecRunsCR`, and records the non-vacuity witnesses of `CrMergeIn` at $A=[5]$, $B=[7]$ (output $\{5,7\}$) and at $A=B=\varnothing$.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's `cr` stage and \u00a72.3.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Top65Dec
import Definitions.Def_LinearSetReconciliation327_Main_MergeStep20261121
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

/-! ## 5. The `cr` stage of §9.2: 2.3's decoder at `dCrBase`, the merge at `dCrBase + Sdec.len`

`_65_reloc_block` §6.3 (`ScrBlock`/`stageRun_scrBlock`, copied above byte-identically) is the
composition rule: once 2.3's decoder is a compiled `Stmt`, its base-`0` `HaltsWithin` relocates to
`dCrBase` and the merge's `StageRun` glues on.  The two missing pieces — the merge program and its
`StageRun` — are the published `mergeStageRun` (`Definitions.Def_…_MergeStep20261121`); what this
section adds is the *interface between them* as a named state predicate (`CrMergeIn`) and the
address arithmetic of the composite `Scr = .seq Sdec23 mrgStmtFull`. -/

/-- A list that enumerates a `Finset`: duplicate-free, and with exactly its members.  This is the
`OutListIs` vocabulary of the six-stage structure (`_65_correct_block` §1), restated locally. -/
def Lists (L : List ℕ) (S : Finset ℕ) : Prop := L.Nodup ∧ ∀ v : ℕ, v ∈ L ↔ v ∈ S

/-- The halted state's explicit output list (`outList`) enumerates `S`. -/
def OutListIs (s : RAMState) (S : Finset ℕ) : Prop := Lists (outList s) S

theorem lists_of_nodup_toFinset {L : List ℕ} {S : Finset ℕ} (h : L.Nodup)
    (hs : L.toFinset = S) : Lists L S :=
  ⟨h, fun v => by rw [← List.mem_toFinset, hs]⟩

/-! ### 5.1 The composite `Scr`, its address, and the merge's `At` fact -/

/-- **The CR stage of §9.2**: 2.3's decoder, then the merge. -/
def ScrStage (Sdec23 : Stmt) : Stmt := ScrBlock Sdec23 RMR.mrgStmtFull

theorem ScrStage_len (Sdec23 : Stmt) :
    (ScrStage Sdec23).len = Sdec23.len + RMR.mrgStmtFull.len := rfl

/-- **The address arithmetic.**  `dEnd` is `dCrBase` plus the *composite* `Scr`'s length, i.e. 2.3's
decoder's length plus the merge's 86 instructions land exactly on the trailing `halt`. -/
theorem dEnd_scrStage (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) :
    dEnd Sinit Srow Sdec Sassem Sres (ScrStage Sdec23)
      = dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len + RMR.mrgStmtFull.len := by
  show dCrBase Sinit Srow Sdec Sassem Sres + (Sdec23.len + RMR.mrgStmtFull.len)
    = dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len + RMR.mrgStmtFull.len
  omega

theorem dEnd_scrStage_eq (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) :
    dEnd Sinit Srow Sdec Sassem Sres (ScrStage Sdec23)
      = (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len) + RMR.mrgStmtFull.len := by
  show dCrBase Sinit Srow Sdec Sassem Sres + (Sdec23.len + RMR.mrgStmtFull.len)
    = (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len) + RMR.mrgStmtFull.len
  omega

/-- The suffix of `progDecOfTop` that starts at the prefix assembly. -/
theorem at_as_seq (Sinit Srow Sdec Sassem Sres Scr : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (dAsBase Sinit Srow Sdec)
      (Stmt.compile (Stmt.seq Sassem (Stmt.seq Sres Scr)) (dAsBase Sinit Srow Sdec)) :=
  at_seq_right (a := topLoop Sdec) (at_col_seq Sinit Srow Sdec Sassem Sres Scr)

/-- The suffix that starts at the residual syndrome. -/
theorem at_res_seq (Sinit Srow Sdec Sassem Sres Scr : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (dResBase Sinit Srow Sdec Sassem)
      (Stmt.compile (Stmt.seq Sres Scr) (dResBase Sinit Srow Sdec Sassem)) :=
  at_seq_right (a := Sassem) (at_as_seq Sinit Srow Sdec Sassem Sres Scr)

/-- **`Scr` starts at `dCrBase`.**  This is the `At` fact the CR stage is placed by; it is the
`Stmt.compile` splitting of `topDecStmt`, with no address hypothesis beyond `dCrBase`'s definition. -/
theorem at_cr_seq (Sinit Srow Sdec Sassem Sres Scr : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (dCrBase Sinit Srow Sdec Sassem Sres)
      (Stmt.compile Scr (dCrBase Sinit Srow Sdec Sassem Sres)) :=
  at_seq_right (a := Sres) (at_res_seq Sinit Srow Sdec Sassem Sres Scr)

/-- The composite CR block at `dCrBase`. -/
theorem at_scrStage (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (ScrStage Sdec23))
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (Stmt.compile (ScrStage Sdec23) (dCrBase Sinit Srow Sdec Sassem Sres)) :=
  at_cr_seq Sinit Srow Sdec Sassem Sres (ScrStage Sdec23)

/-- 2.3's decoder, placed at `dCrBase`. -/
theorem at_scrStage_dec (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (ScrStage Sdec23))
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (Sdec23.compile (dCrBase Sinit Srow Sdec Sassem Sres)) :=
  at_seq_left (at_scrStage Sinit Srow Sdec Sassem Sres Sdec23)

/-- **The merge program, placed exactly where `compile` puts it**: `dCrBase + Sdec23.len`. -/
theorem at_scrStage_mrg (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (ScrStage Sdec23))
      (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len)
      (RMR.mrgStmtFull.compile (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len)) :=
  at_seq_right (a := Sdec23) (at_scrStage Sinit Srow Sdec Sassem Sres Sdec23)

/-- The merge's `At` fact at `dCrBase` read through `dEnd`'s arithmetic: the block starting at
`dCrBase + Sdec23.len` ends at `dEnd`. -/
theorem at_scrStage_mrg_end (Sinit Srow Sdec Sassem Sres Sdec23 : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres (ScrStage Sdec23))
      (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len)
      (RMR.mrgStmtFull.compile (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len)) :=
  at_scrStage_mrg Sinit Srow Sdec Sassem Sres Sdec23

/-! ### 5.2 The two syntactic side conditions of the relocation lemma -/

theorem decStmt_noJump : sNoJumpB decStmt = true := by
  decide

theorem decStmt_haltFree : sHaltFreeB decStmt = true := by
  decide

theorem mrgStmtFull_noJump : sNoJumpB RMR.mrgStmtFull = true := by
  decide

theorem mrgStmtFull_haltFree : sHaltFreeB RMR.mrgStmtFull = true := by
  decide

theorem code_nil_noJump : sNoJumpB (.code [] : Stmt) = true := rfl

theorem code_nil_haltFree : sHaltFreeB (.code [] : Stmt) = true := rfl

/-! ### 5.3 The intermediate state: the merge's entry predicate -/

/-- **The merge's entry state**, named.  It is exactly `RMR.mergeStageRun`'s precondition, except
that the residual list is pinned to the *decoder's own output window* (`regs 0`, `regs 1`), which is
how 2.3 hands its decoded support over:

* `r10 … r14` are the merge's five arguments `(ab, al, bb, bl, ob)`;
* the decoder's output window `(regs 0, regs 1)` is the merge's `B` window `(bb, bl)`, so
  `outList` *is* `mList mem bb bl` (definitionally, both are `range bl |>.map fun i => mem (bb+i)`);
* `Lx` at `[ab, ab+al)` is the estimate `x̂` (as an explicit coordinate list), `outList` is the
  decoded residual `ê` (`S` its value set);
* the remaining conjuncts are `mergeStageRun`'s word bounds and block-disjointness hypotheses. -/
def CrMergeIn (E : RAMEnv) (ab al bb bl ob : ℕ) (Lx : List ℕ) (S : Finset ℕ)
    (t : RAMState) : Prop :=
  t.regs r10 = ab ∧ t.regs r11 = al ∧ t.regs r12 = bb ∧ t.regs r13 = bl ∧ t.regs r14 = ob ∧
    t.regs 0 = bb ∧ t.regs 1 = bl ∧
    RMR.mList t.mem ab al = Lx ∧
    (outList t).Nodup ∧ (outList t).toFinset = S ∧ Lx.Nodup ∧
    (∀ p, p < al → t.mem (ab + p) < 2 ^ E.W) ∧
    (∀ p, p < bl → t.mem (bb + p) < 2 ^ E.W) ∧
    al < 2 ^ E.W ∧ bl < 2 ^ E.W ∧
    ab + al ≤ 2 ^ E.W ∧ bb + bl ≤ 2 ^ E.W ∧ ob + (al + bl) + 1 < 2 ^ E.W ∧
    (ab + al ≤ ob ∨ ob + (al + bl) ≤ ab) ∧ (bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb)

/-- **The merge as a `StageRun` with the named entry predicate.**  This is the published
`mergeStageRun` with `B` instantiated at the state's own output window: no fixed `B` is needed,
because `CrMergeIn` pins `(regs 0, regs 1) = (bb, bl)`. -/
theorem stageRun_mergeAt {G : Program} {E : RAMEnv} {base ab al bb bl ob : ℕ}
    {Lx : List ℕ} {S xhat : Finset ℕ}
    (hAt : At G base (RMR.mrgStmtFull.compile base)) (hW : 1 < 2 ^ E.W)
    (hLx : Lx.toFinset = xhat) :
    StageRun G E base (base + RMR.mrgStmtFull.len) (RMR.mrgCost al bl)
      (CrMergeIn E ab al bb bl ob Lx S)
      (fun s' => OutListIs s' (symmDiff xhat S)) := by
  intro t htpc htI
  obtain ⟨h10, h11, h12, h13, h14, h0, h1, hL, hnd, hset, hndL, hvA, hvB, hal, hbl,
    hab, hbb, hob, hdA, hdB⟩ := htI
  have hndB : (RMR.mList t.mem bb bl).Nodup := by
    simpa [outList, RMR.mList, h0, h1] using hnd
  have hsetB : (RMR.mList t.mem bb bl).toFinset = S := by
    simpa [outList, RMR.mList, h0, h1] using hset
  obtain ⟨k, s', hk, hstep, hpc, hQ⟩ :=
    RMR.mergeStageRun (P := G) (E := E) (base := base) (ab := ab) (al := al) (bb := bb)
      (bl := bl) (ob := ob) (A := Lx) (B := RMR.mList t.mem bb bl) hAt hW t htpc
      ⟨h10, h11, h12, h13, h14, hL, rfl, hndL, hndB, hvA, hvB, hal, hbl, hab, hbb, hob, hdA, hdB⟩
  exact ⟨k, s', hk, hstep, hpc, lists_of_nodup_toFinset hQ.1 (by rw [hQ.2, hsetB, hLx])⟩

/-! ### 5.4 The composed `cr` stage -/

/-- **The composed `cr` stage** with the published `mergeStageRun`, on the named intermediate state.

`hdec` is 2.3's published contract in the pc-blind form the relocation lemma consumes: from the
relocated start state it produces a state whose *whole* merge entry predicate `CrMergeIn` holds at
`dCrBase + Sdec.len`.  The merge half is the published `mergeStageRun`; the composition is
`stageRun_scrBlock` (relocation + `StageRun.trans`).

The bound is `Tdec + mrgCost al bl` — 2.3's own bound plus the merge's. -/
theorem stageRun_crMerge {G : Program} {E : RAMEnv} {base : ℕ} {Sdec : Stmt} {Tdec : ℝ}
    {Pre : RAMState → Prop} {ab al bb bl ob : ℕ} {Lx : List ℕ} {S xhat : Finset ℕ}
    (hAt : At G base (Sdec.compile base))
    (hno : sNoJumpB Sdec = true) (hhf : sHaltFreeB Sdec = true)
    (hdec : ∀ s : RAMState, s.pc = 0 → Pre (withPc base s) →
      ∃ s', HaltsWithin (programOfStatement Sdec) E Tdec s s' ∧
        CrMergeIn E ab al bb bl ob Lx S (withPc (base + Sdec.len) s'))
    (hLx : Lx.toFinset = xhat)
    (hAtM : At G (base + Sdec.len) (RMR.mrgStmtFull.compile (base + Sdec.len)))
    (hW : 1 < 2 ^ E.W) :
    StageRun G E base (base + (ScrStage Sdec).len) (Tdec + RMR.mrgCost al bl) Pre
      (fun s' => OutListIs s' (symmDiff xhat S)) := by
  have hmg : StageRun G E (base + Sdec.len) (base + Sdec.len + RMR.mrgStmtFull.len)
      (RMR.mrgCost al bl) (CrMergeIn E ab al bb bl ob Lx S)
      (fun s' => OutListIs s' (symmDiff xhat S)) :=
    stageRun_mergeAt (G := G) (E := E) (base := base + Sdec.len) (xhat := xhat) hAtM hW hLx
  exact stageRun_scrBlock (G := G) (E := E) (Sdec := Sdec) (Smerge := RMR.mrgStmtFull)
    (base := base) (Tdec := Tdec) (Tmg := RMR.mrgCost al bl) hAt hno hhf hdec hmg

/-- **The composed `cr` stage of `progDecOfTop`, from `dCrBase` to `dEnd`.**  This is the headline:
the run really is inside the one fixed programme `progDecOfTop … (ScrStage Sdec23)`, starts at the
address `compile` puts `Scr` (i.e. `dCrBase`), ends at the address of the trailing `halt` (`dEnd`),
and its bound is `Tdec + mrgCost al bl`. -/
theorem stageRun_crMerge_top {Sinit Srow Sdec Sassem Sres Sdec23 : Stmt} {E : RAMEnv} {Tdec : ℝ}
    {Pre : RAMState → Prop} {ab al bb bl ob : ℕ} {Lx : List ℕ} {S xhat : Finset ℕ}
    (hno : sNoJumpB Sdec23 = true) (hhf : sHaltFreeB Sdec23 = true)
    (hdec : ∀ s : RAMState,
      s.pc = 0 → Pre (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement Sdec23) E Tdec s s' ∧
        CrMergeIn E ab al bb bl ob Lx S
          (withPc (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len) s'))
    (hLx : Lx.toFinset = xhat) (hW : 1 < 2 ^ E.W) :
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres (ScrStage Sdec23)) E
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres (ScrStage Sdec23))
      (Tdec + RMR.mrgCost al bl) Pre
      (fun s' => OutListIs s' (symmDiff xhat S)) :=
  stageRun_crMerge (G := progDecOfTop Sinit Srow Sdec Sassem Sres (ScrStage Sdec23))
    (base := dCrBase Sinit Srow Sdec Sassem Sres)
    (at_scrStage_dec Sinit Srow Sdec Sassem Sres Sdec23) hno hhf hdec hLx
    (at_scrStage_mrg Sinit Srow Sdec Sassem Sres Sdec23) hW


/-- **The composed CR stage with 2.3's own `Stmt`.**  `hSdec` is exactly the published
`cr23_progDec_stmt` (`∃ Sdec, Sdec.compile 0 ++ [iHalt] = progDec`), at its witness; the decoder's
run is `proposition_2_3`'s `OutputsSupport` conjunct, transported to `decStmt` by that equation. -/
theorem stageRun_cr23Merge {G : Program} {E : RAMEnv} {base : ℕ} {Tdec : ℝ}
    {Pre : RAMState → Prop} {ab al bb bl ob : ℕ} {Lx : List ℕ} {S xhat : Finset ℕ}
    (hSdec : decStmt.compile 0 ++ [iHalt] = progDec)
    (hAt : At G base (decStmt.compile base))
    (hdec : ∀ s : RAMState, s.pc = 0 → Pre (withPc base s) →
      ∃ s', HaltsWithin progDec E Tdec s s' ∧
        CrMergeIn E ab al bb bl ob Lx S (withPc (base + decStmt.len) s'))
    (hLx : Lx.toFinset = xhat)
    (hAtM : At G (base + decStmt.len) (RMR.mrgStmtFull.compile (base + decStmt.len)))
    (hW : 1 < 2 ^ E.W) :
    StageRun G E base (base + (ScrStage decStmt).len) (Tdec + RMR.mrgCost al bl) Pre
      (fun s' => OutListIs s' (symmDiff xhat S)) := by
  refine stageRun_crMerge (Sdec := decStmt) (ab := ab) (al := al) (bb := bb) (bl := bl) (ob := ob)
    hAt decStmt_noJump decStmt_haltFree ?_ hLx hAtM hW
  intro s hpc hpre
  have h := hdec s hpc hpre
  simpa [programOfStatement, hSdec] using h

/-! ## 6. The residual identity `x̂ △ ê = x` -/

/-- `x̂ △ (x △ x̂) = x`. -/
theorem symmDiff_self_cancel (a b : Finset ℕ) : symmDiff a (symmDiff b a) = b := by
  ext v
  simp only [Finset.mem_symmDiff]
  tauto

/-- **The residual identity.**  With `ê := x △ x̂` the residual, `x̂ △ ê = x`. -/
theorem residual_identity (x xhat : Finset ℕ) :
    symmDiff xhat (symmDiff x xhat) = x :=
  symmDiff_self_cancel xhat x

/-- **The residual, read off `Node.residual`.**  `Node.residual` is *defined* as
`(CR.dec N t (a △ CR x̂)).map (fun e => x̂ △ e)`, so the statement `Node.residual … = some x` is
already "the decoded residual `ê` satisfies `x̂ △ ê = x`" — no additivity of the sketch is needed.
This is the route taken here (the `residual_sketch` statement, `_65_correct_block` §3, is the other
one: it *derives* `Node.residual … = some x` from `CR.Recovers` plus `sketch_symmDiff`). -/
theorem residual_eq_of_node_residual {CR : CRFamily} {N t : ℕ} {a xhat x : Finset ℕ}
    (h : Node.residual CR N t a xhat = some x) :
    ∃ e : Finset ℕ, CR.dec N t (symmDiff a (CR.sketch N t xhat)) = some e ∧
      symmDiff xhat e = x := by
  unfold Node.residual at h
  cases hd : CR.dec N t (symmDiff a (CR.sketch N t xhat)) with
  | none => rw [hd] at h; simp at h
  | some e =>
      rw [hd] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨e, rfl, h⟩

/-- `CR.Recovers` at the residual set `x △ x̂`: 2.3's decoder returns exactly the residual. -/
theorem residual_dec_is_err {CR : CRFamily} (hRec : CR.Recovers) {N t : ℕ} {x xhat : Finset ℕ}
    (hsub : symmDiff x xhat ⊆ Finset.range N) (hcard : (symmDiff x xhat).card ≤ t) (ht : t ≤ N) :
    CR.dec N t (CR.sketch N t (symmDiff x xhat)) = some (symmDiff x xhat) :=
  hRec N t ht _ hsub hcard

/-- **The CR stage's output is the true `x`.**  Composing the stage's post with the residual
identity: the state's output list enumerates `x̂ △ (x △ x̂) = x`. -/
theorem outListIs_of_crMerge {s : RAMState} {x xhat : Finset ℕ}
    (h : OutListIs s (symmDiff xhat (symmDiff x xhat))) : OutListIs s x := by
  rwa [residual_identity] at h

/-! ## 7. The corrected `cr` field of `TopDecRuns`

The published `TopDecRuns.cr` is

```lean
cr : ∀ y : Fin M → ZMod 2,
  StageRun (progDecOfTop …) E (dCrBase …) (dEnd …) Tcr (fun _ => True) (fun _ => True)
```

i.e. it carries no data and composes to conjunct 7 only.  The corrected field below carries the
merge's postcondition.  Its *precondition* cannot stay `fun _ => True`: with a data-carrying post
the field would be false (a state with arbitrary memory at `dCrBase` cannot be forced to output a
given set).  It is therefore replaced by `CrMergeIn`, the intermediate state the residual stage hands
over — the same kind of strengthening every other field of the structure already has
(`RowIn`/`ColIn`, `ColOutAsZ`, …).  The other five fields are copied verbatim. -/

structure TopDecRunsCR (Sinit Srow Sdec Sassem Sres Scr : Stmt) (E : RAMEnv) (W M n d ℓ : ℕ)
    (Tini Trow Tdec Tas Tres Tcr : ℝ) (ab al bb bl ob : ℕ) (Lx : List ℕ) (S xhat : Finset ℕ) :
    Prop where
  /-- The prologue: read `d`, `ℓ` and `wordsOf W M` from `det`'s header. -/
  init : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0 (dRowBase Sinit) Tini
      (fun s => s = decoderStart W y []) (RowIn d)
  /-- Row decoding: `d` iterations of `proposition_2_1`. -/
  row : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dRowBase Sinit) (dColBase Sinit Srow)
      Trow (RowIn d) (ColIn ℓ)
  /-- The `ℓ` child decoders of `theorem_5_1`. -/
  col : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dColBase Sinit Srow)
      (dAsBase Sinit Srow Sdec) Tdec (ColIn ℓ) (fun _ => True)
  /-- Prefix assembly. -/
  as : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dAsBase Sinit Srow Sdec)
      (dResBase Sinit Srow Sdec Sassem) Tas (fun _ => True) (fun _ => True)
  /-- Residual syndrome. -/
  res : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dResBase Sinit Srow Sdec Sassem)
      (dCrBase Sinit Srow Sdec Sassem Sres) Tres (fun _ => True) (fun _ => True)
  /-- **The corrected `cr` field**: 2.3's decoder plus the merge, carrying `x̂ △ ê`. -/
  cr : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dCrBase Sinit Srow Sdec Sassem Sres) (dEnd Sinit Srow Sdec Sassem Sres Scr) Tcr
      (CrMergeIn E ab al bb bl ob Lx S)
      (fun s' => OutListIs s' (symmDiff xhat S))

/-- **The correction does not break conjunct 7.**  The five published fields plus the corrected `cr`
field still compose into one run from `decoderStart` to the trailing `halt`, at the same budget —
provided the residual stage's post is strengthened to the `CrMergeIn` state the corrected `cr` field
consumes.  (With the published `res : … (fun _ => True)`, which says nothing about the state it hands
over, the corrected `cr` field could not be applied; that is why the interface predicate has to be
named.  The proof below is `haltsWithin_topDec_of_runs`'s, with `hres` carrying `CrMergeIn`.) -/
theorem haltsWithin_topDec_of_runsCR {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ} {ab al bb bl ob : ℕ} {Lx : List ℕ}
    {S xhat : Finset ℕ}
    (h : TopDecRunsCR Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ Tini Trow Tdec Tas Tres Tcr
      ab al bb bl ob Lx S xhat)
    (hres : ∀ y : Fin M → ZMod 2,
      StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (dResBase Sinit Srow Sdec Sassem) (dCrBase Sinit Srow Sdec Sassem Sres) Tres
        (fun _ => True) (CrMergeIn E ab al bb bl ob Lx S))
    (y : Fin M → ZMod 2) :
    ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (Tini + Trow + Tdec + Tas + Tres + Tcr) (decoderStart W y []) s' := by
  have hstep : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0
      (dEnd Sinit Srow Sdec Sassem Sres Scr) (Tini + Trow + Tdec + Tas + Tres + Tcr)
      (fun s => s = decoderStart W y []) (fun _ => True) :=
    ((((h.init y).trans (h.row y)).trans (h.col y)).trans (h.as y)).trans (hres y)
      |>.trans (stageRun_post (h.cr y) (fun _ _ => trivial))
  obtain ⟨k, s', hk, hrun, hpc, -⟩ := hstep (decoderStart W y []) rfl rfl
  have hlen : dEnd Sinit Srow Sdec Sassem Sres Scr =
      ((topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0).length := by
    rw [Stmt.length_compile]
    simp only [dEnd, dCrBase, dResBase, dAsBase, dColBase, dRowBase, topDecStmt, topLoop, Stmt.len]
    omega
  have hhalt :
      (progDecOfTop Sinit Srow Sdec Sassem Sres Scr)[dEnd Sinit Srow Sdec Sassem Sres Scr]? =
        some Instr.halt := by
    rw [hlen]
    rw [show progDecOfTop Sinit Srow Sdec Sassem Sres Scr =
      (topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0 ++ [Instr.halt] from rfl,
      List.getElem?_append_right (le_refl _)]
    simp
  exact ⟨s', k, hk, hrun, by simp only [Halted, hpc, hhalt]⟩

/-! ## 8. Non-vacuity

The merge's own witnesses (`RMR.smergeRunsM_witness_5_7`, `…_5_57`) are `∃ k s'` statements about
`mrgProg`; the structure above is a `StageRun`, so the non-vacuity check here is *applying* the
composed stage (not evaluating the merge again) at a state that satisfies `CrMergeIn`.

The instance: `A = [5]` at `[10, 11)`, `B = [7]` at `[20, 21)` (the decoder's output window), output
block at `40`, an 8-bit machine.  The stage then outputs `[5] △ [7] = {5, 7}`, i.e. the *symmetric
difference*, not the union. -/

/-- The entry state of the merge witness `A = [5]`, `B = [7]`: the merge's five arguments in
`r10 … r14`, the decoder's output window `(r0, r1) = (20, 1)`, and the two lists in memory. -/
def crW1 : RAMState where
  pc := 0
  regs := fun d =>
    if d = r0 then 20 else if d = r1 then 1 else RMR.mrgIn 10 1 20 1 40 d
  mem := RMR.mrgW1mem

theorem crW1_pc : crW1.pc = 0 := rfl

theorem crW1_r0 : crW1.regs r0 = 20 := by decide
theorem crW1_r1 : crW1.regs r1 = 1 := by decide
theorem crW1_r10 : crW1.regs r10 = 10 := by decide
theorem crW1_r11 : crW1.regs r11 = 1 := by decide
theorem crW1_r12 : crW1.regs r12 = 20 := by decide
theorem crW1_r13 : crW1.regs r13 = 1 := by decide
theorem crW1_r14 : crW1.regs r14 = 40 := by decide

theorem crW1_memA : RMR.mList crW1.mem 10 1 = [5] := by decide

theorem crW1_memB : RMR.mList crW1.mem 20 1 = [7] := by decide

theorem crW1_out : outList crW1 = [7] := by decide

/-- **`CrMergeIn` is inhabited** at `A = [5]`, `B = [7]`, `x̂ = {5}`, `S = {7}`. -/
theorem crMergeIn_witness : CrMergeIn RMR.mrgEnv8 10 1 20 1 40 [5] {7} crW1 := by
  refine ⟨crW1_r10, crW1_r11, crW1_r12, crW1_r13, crW1_r14, crW1_r0, crW1_r1, crW1_memA,
    ?_, ?_, by decide, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩
  · rw [crW1_out]; decide
  · rw [crW1_out]; decide
  · intro p hp
    have hp0 : p = 0 := by omega
    subst hp0
    decide
  · intro p hp
    have hp0 : p = 0 := by omega
    subst hp0
    decide

/-- **The composed stage applies at the witness**: from `crW1` it reaches the end of the CR block
(`s'.pc = 86`, i.e. `0 + (ScrStage (.code [])).len`) within `mrgCost 1 1` steps, and its output list
enumerates `{5} △ {7} = {5, 7}`.  `Sdec = .code []` makes the decoder half the empty run, so this is
the merge half of the composed `StageRun` — the part the task's witnesses exercise — running inside
the composition. -/
theorem stageRun_crMerge_witness :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ (0 : ℝ) + RMR.mrgCost 1 1 ∧
      (step RMR.mrgProg RMR.mrgEnv8)^[k] crW1 = s' ∧
      s'.pc = 0 + (ScrStage (.code [] : Stmt)).len ∧
      OutListIs s' ({5, 7} : Finset ℕ) := by
  have hSt := stageRun_crMerge (G := RMR.mrgProg) (E := RMR.mrgEnv8) (base := 0)
    (Sdec := (.code [] : Stmt)) (Tdec := 0) (Pre := fun t => t = crW1)
    (ab := 10) (al := 1) (bb := 20) (bl := 1) (ob := 40) (Lx := [5]) (S := {7}) (xhat := {5})
    (by intro r hr; exact absurd hr (Nat.not_lt_zero r)) code_nil_noJump code_nil_haltFree
    ?_ (by decide) (by simpa [Stmt.len] using RMR.mrgProg_at) (by decide)
  · obtain ⟨k, s', hk, hstep, hpc, hpost⟩ := hSt crW1 rfl rfl
    refine ⟨k, s', by simpa using hk, hstep, by simpa using hpc, ?_⟩
    rw [show symmDiff ({5} : Finset ℕ) {7} = {5, 7} from by decide] at hpost
    exact hpost
  · intro s hpc hpre
    have hs : s = crW1 := by
      rw [← withPc_congr hpc]
      exact hpre
    subst hs
    refine ⟨crW1, ⟨0, by norm_num, rfl, ?_⟩, ?_⟩
    · have hlook : (programOfStatement (.code [] : Stmt))[crW1.pc]? = some Instr.halt := by
        rw [crW1_pc]
        rfl
      unfold Halted
      rw [hlook]
      trivial
    · simpa [Stmt.len, withPc, crW1] using crMergeIn_witness

/-- **The degenerate value.**  With `A = B = []` (both blocks empty, `al = bl = 0`) `CrMergeIn` is
inhabited too — so the corrected `cr` field is not vacuously true at the empty instance, and the
contract's hypotheses are satisfiable there.  (`mrgCost 0 0 = 30`.) -/
def crW0 : RAMState where
  pc := 0
  regs := fun d => if d = r10 then 0 else if d = r11 then 0 else if d = r12 then 0 else
    if d = r13 then 0 else if d = r14 then 64 else 0
  mem := fun _ => 0

theorem crMergeIn_degenerate : CrMergeIn RMR.mrgEnv8 0 0 0 0 64 [] ∅ crW0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_,
    ?_, by decide, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩
  · simp [RMR.mList]
  · simp [outList, crW0]
  · simp [outList, crW0]
  · intro p hp
    exact absurd hp (Nat.not_lt_zero p)
  · intro p hp
    exact absurd hp (Nat.not_lt_zero p)

/-! ## 9. Bridging 2.3's `OutputsSupport` to the merge's `B` half, and the concrete arithmetic -/

/-- **2.3's `OutputsSupport` gives the `B` half of `CrMergeIn`**: the decoder's output window is
duplicate-free and enumerates exactly the decoded set.  (The `A` half — the estimate `x̂` as an
explicit coordinate list at `[ab, ab+al)` — is *not* supplied by 2.3: it is what `Sassem`/`Sres`
leave in the packed `asmVec` form and what a repack still has to turn into a list; see the report.) -/
theorem outList_toFinset_of_outputsSupport {t : RAMState} {M : ℕ} {v : Fin M → ZMod 2}
    (h : OutputsSupport t v) :
    (outList t).Nodup ∧
      (outList t).toFinset = (Finset.univ.filter fun i : Fin M => v i = 1).image Fin.val := by
  refine ⟨h.1, ?_⟩
  ext a
  rw [List.mem_toFinset, h.2]
  constructor
  · rintro ⟨i, rfl, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  · intro ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨i, rfl, (Finset.mem_filter.mp hi).2⟩

theorem decStmt_len : decStmt.len = 282 := by decide

/-- The merge's cost at `A = B = [5]` (the witness): `16 + 34 + 44 = 94`. -/
theorem mrgCost_one_one : RMR.mrgCost 1 1 = 94 := by decide

/-- The merge's cost at the degenerate `A = B = []`: `16 + 2 + 12 = 30`. -/
theorem mrgCost_zero_zero : RMR.mrgCost 0 0 = 30 := by decide

/-- **The concrete address arithmetic at 2.3's own decoder**: `dEnd = dCrBase + 282 + 86 = dCrBase + 368`. -/
theorem dEnd_decStmt (Sinit Srow Sdec Sassem Sres : Stmt) :
    dEnd Sinit Srow Sdec Sassem Sres (ScrStage decStmt)
      = dCrBase Sinit Srow Sdec Sassem Sres + 368 := by
  rw [dEnd_scrStage, decStmt_len, RMR.mrgStmtFull_len]

end CRS
end LinearSetReconciliation327.Main


