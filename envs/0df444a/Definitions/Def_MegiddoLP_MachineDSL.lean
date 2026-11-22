-- Prove2me | Definitions.Def_MegiddoLP_MachineDSL
-- name    : MegiddoLP_MachineDSL
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T21:10:24.88412+00:00
-- url     : https://prove2.me/theorems/41d01139-a104-4d04-82cf-f55a65fb889e
-- title:
--   Structured programs for the real pointer machine
-- statement:
--   A compiler for sequential statements, conditional branches, and loops on the real pointer machine, with compositional proofs of execution and instruction bounds.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, Implementation infrastructure for the fixed-dimension LP algorithm. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_SmaleNinth_RealRAM
import Mathlib.Tactic.Set
import Lean.Elab.Tactic.Omega

/-!
# Structured Imperative DSL and Compositional Verification for `SmaleNinth.RAMProgram`

Compiles structured pointer-RAM statements (`Stmt`) into relocatable `RAMProgram` slices
and provides big-step execution, step-counting, and register/pointer/memory frame
preservation lemmas.
-/

namespace MegiddoLP.MachineDSL

open SmaleNinth

/-- Non-branching primitive instructions of `SmaleNinth.RAMInstr`. -/
inductive Prim : Type
  | const (dst : ℕ) (c : ℝ)
  | add (dst i j : ℕ)
  | sub (dst i j : ℕ)
  | mul (dst i j : ℕ)
  | div (dst i j : ℕ)
  | load (dst q : ℕ)
  | store (q i : ℕ)
  | pset (q : ℕ) (c : ℤ)
  | pcopy (q q' : ℕ)
  | pinc (q : ℕ)
  | pdec (q : ℕ)

/-- Convert a primitive instruction to `RAMInstr`. -/
def Prim.toRAM : Prim → RAMInstr
  | .const dst c => .const dst c
  | .add dst i j => .add dst i j
  | .sub dst i j => .sub dst i j
  | .mul dst i j => .mul dst i j
  | .div dst i j => .div dst i j
  | .load dst q => .load dst q
  | .store q i => .store q i
  | .pset q c => .pset q c
  | .pcopy q q' => .pcopy q q'
  | .pinc q => .pinc q
  | .pdec q => .pdec q

/-- Machine state without program counter (`regs`, `ptrs`, `mem`). -/
structure MState where
  regs : ℕ → ℝ
  ptrs : ℕ → ℤ
  mem : ℤ → ℝ

/-- Effect of one `Prim` on `MState`. -/
noncomputable def Prim.step (p : Prim) (s : MState) : MState :=
  match p with
  | .const dst c => ⟨Function.update s.regs dst c, s.ptrs, s.mem⟩
  | .add dst i j => ⟨Function.update s.regs dst (s.regs i + s.regs j), s.ptrs, s.mem⟩
  | .sub dst i j => ⟨Function.update s.regs dst (s.regs i - s.regs j), s.ptrs, s.mem⟩
  | .mul dst i j => ⟨Function.update s.regs dst (s.regs i * s.regs j), s.ptrs, s.mem⟩
  | .div dst i j => ⟨Function.update s.regs dst (s.regs i / s.regs j), s.ptrs, s.mem⟩
  | .load dst q => ⟨Function.update s.regs dst (s.mem (s.ptrs q)), s.ptrs, s.mem⟩
  | .store q i => ⟨s.regs, s.ptrs, Function.update s.mem (s.ptrs q) (s.regs i)⟩
  | .pset q c => ⟨s.regs, Function.update s.ptrs q c, s.mem⟩
  | .pcopy q q' => ⟨s.regs, Function.update s.ptrs q (s.ptrs q'), s.mem⟩
  | .pinc q => ⟨s.regs, Function.update s.ptrs q (s.ptrs q + 1), s.mem⟩
  | .pdec q => ⟨s.regs, Function.update s.ptrs q (s.ptrs q - 1), s.mem⟩

/-- Structured imperative statements over `MState`. -/
inductive Stmt : Type
  | skip
  | prim (p : Prim)
  | seq (s₁ s₂ : Stmt)
  | ifLeZero (r : ℕ) (t e : Stmt)
  | ifPtrLe (q₁ q₂ : ℕ) (t e : Stmt)
  | whilePos (r : ℕ) (body : Stmt)
  | whilePtrLt (q₁ q₂ : ℕ) (body : Stmt)

/-- Static instruction count of a compiled `Stmt`. -/
def Stmt.codeLen : Stmt → ℕ
  | .skip => 0
  | .prim _ => 1
  | .seq s₁ s₂ => s₁.codeLen + s₂.codeLen
  | .ifLeZero _ t e => 1 + e.codeLen + 1 + t.codeLen
  | .ifPtrLe _ _ t e => 1 + e.codeLen + 1 + t.codeLen
  | .whilePos _ body => 1 + body.codeLen + 1
  | .whilePtrLt _ _ body => 1 + body.codeLen + 1

/-- Compile `Stmt` starting at instruction index `off`.
Unconditional jumps use `.pjle 0 0 target` (`ptrs 0 ≤ ptrs 0` always holds). -/
noncomputable def Stmt.compile : ℕ → Stmt → RAMProgram
  | _, .skip => []
  | _, .prim p => [p.toRAM]
  | off, .seq s₁ s₂ =>
    let c₁ := s₁.compile off
    c₁ ++ s₂.compile (off + c₁.length)
  | off, .ifLeZero r t e =>
    let ce := e.compile (off + 1)
    let elsePc := off + 1 + ce.length + 1
    let ct := t.compile elsePc
    let endPc := elsePc + ct.length
    [.jle r elsePc] ++ ce ++ [.pjle 0 0 endPc] ++ ct
  | off, .ifPtrLe q₁ q₂ t e =>
    let ce := e.compile (off + 1)
    let elsePc := off + 1 + ce.length + 1
    let ct := t.compile elsePc
    let endPc := elsePc + ct.length
    [.pjle q₁ q₂ elsePc] ++ ce ++ [.pjle 0 0 endPc] ++ ct
  | off, .whilePos r body =>
    let cb := body.compile (off + 1)
    let endPc := off + 1 + cb.length + 1
    [.jle r endPc] ++ cb ++ [.pjle 0 0 off]
  | off, .whilePtrLt q₁ q₂ body =>
    let cb := body.compile (off + 1)
    let endPc := off + 1 + cb.length + 1
    [.pjle q₂ q₁ endPc] ++ cb ++ [.pjle 0 0 off]

@[simp] theorem Stmt.length_compile (off : ℕ) (s : Stmt) :
    (s.compile off).length = s.codeLen := by
  induction s generalizing off with
  | skip => rfl
  | prim _ => rfl
  | seq s₁ s₂ ih₁ ih₂ =>
    simp only [compile, codeLen, List.length_append, ih₁, ih₂]
  | ifLeZero r t e iht ihe =>
    simp only [compile, codeLen, List.length_append, List.length_singleton, iht, ihe]
  | ifPtrLe q₁ q₂ t e iht ihe =>
    simp only [compile, codeLen, List.length_append, List.length_singleton, iht, ihe]
  | whilePos r body ih =>
    simp only [compile, codeLen, List.length_append, List.length_singleton, ih]
  | whilePtrLt q₁ q₂ body ih =>
    simp only [compile, codeLen, List.length_append, List.length_singleton, ih]

/-- `R` contains `P` starting at offset `off`. -/
def SubprogramAt (R : RAMProgram) (off : ℕ) (P : RAMProgram) : Prop :=
  ∀ k (hk : k < P.length), R[off + k]? = some P[k]

theorem SubprogramAt.self (P : RAMProgram) : SubprogramAt P 0 P := by
  intro k hk
  simp [hk]

theorem SubprogramAt.append_left {R : RAMProgram} {off : ℕ} {P₁ P₂ : RAMProgram}
    (h : SubprogramAt R off (P₁ ++ P₂)) : SubprogramAt R off P₁ := by
  intro k hk
  have hk' : k < (P₁ ++ P₂).length := by simp; omega
  have h1 := h k hk'
  rwa [List.getElem_append_left hk] at h1

theorem SubprogramAt.append_right {R : RAMProgram} {off : ℕ} {P₁ P₂ : RAMProgram}
    (h : SubprogramAt R off (P₁ ++ P₂)) : SubprogramAt R (off + P₁.length) P₂ := by
  intro k hk
  have hk' : P₁.length + k < (P₁ ++ P₂).length := by simp; omega
  have h1 := h (P₁.length + k) hk'
  have heq : off + (P₁.length + k) = off + P₁.length + k := by omega
  rw [heq] at h1
  rw [List.getElem_append_right (Nat.le_add_right _ _)] at h1
  simpa using h1

theorem SubprogramAt.singleton {R : RAMProgram} {off : ℕ} {ins : RAMInstr}
    (h : SubprogramAt R off [ins]) : R[off]? = some ins := by
  simpa using h 0 (by simp)

/-- Reachability on `RAMConfig` within `T` steps. -/
def RReaches (R : RAMProgram) (c₁ c₂ : RAMConfig) (T : ℕ) : Prop :=
  ∃ t ≤ T, (RAMStep R)^[t] c₁ = c₂

theorem RReaches.refl (R : RAMProgram) (c : RAMConfig) : RReaches R c c 0 :=
  ⟨0, le_rfl, rfl⟩

theorem RReaches.single {R : RAMProgram} {c₁ c₂ : RAMConfig} (h : RAMStep R c₁ = c₂) :
    RReaches R c₁ c₂ 1 :=
  ⟨1, le_rfl, by simpa using h⟩

theorem RReaches.trans {R : RAMProgram} {c₁ c₂ c₃ : RAMConfig} {T₁ T₂ : ℕ}
    (h₁ : RReaches R c₁ c₂ T₁) (h₂ : RReaches R c₂ c₃ T₂) :
    RReaches R c₁ c₃ (T₁ + T₂) := by
  obtain ⟨t₁, ht₁, rfl⟩ := h₁
  obtain ⟨t₂, ht₂, rfl⟩ := h₂
  exact ⟨t₂ + t₁, by omega, by rw [Function.iterate_add_apply]⟩

theorem RReaches.mono {R : RAMProgram} {c₁ c₂ : RAMConfig} {T T' : ℕ}
    (h : RReaches R c₁ c₂ T) (hT : T ≤ T') : RReaches R c₁ c₂ T' := by
  obtain ⟨t, ht, heq⟩ := h
  exact ⟨t, le_trans ht hT, heq⟩

/-- Convert `(pc, MState)` to `RAMConfig`. -/
def MState.toCfg (s : MState) (pc : ℕ) : RAMConfig :=
  ⟨pc, s.regs, s.ptrs, s.mem⟩

/-- `s : Stmt` executes from `st₁` to `st₂` in at most `T` steps inside ANY ambient
program `R` containing `s.compile off` at `off`. -/
def Runs (st : Stmt) (s₁ s₂ : MState) (T : ℕ) : Prop :=
  ∀ (R : RAMProgram) (off : ℕ), SubprogramAt R off (st.compile off) →
    RReaches R (s₁.toCfg off) (s₂.toCfg (off + st.codeLen)) T

theorem Runs.mono {st : Stmt} {s₁ s₂ : MState} {T T' : ℕ}
    (h : Runs st s₁ s₂ T) (hT : T ≤ T') : Runs st s₁ s₂ T' :=
  fun R off hsub => (h R off hsub).mono hT

theorem Runs.skip (s : MState) : Runs .skip s s 0 := by
  intro R off _
  simpa [Stmt.codeLen] using RReaches.refl R (s.toCfg off)

theorem Runs.prim (p : Prim) (s : MState) : Runs (.prim p) s (p.step s) 1 := by
  intro R off hsub
  have hins : R[off]? = some p.toRAM := hsub.singleton
  apply RReaches.single
  cases p <;> simp [MState.toCfg, Prim.toRAM, Prim.step, Stmt.codeLen, RAMStep, hins]

theorem Runs.seq {s₁ s₂ : Stmt} {st₁ st₂ st₃ : MState} {T₁ T₂ : ℕ}
    (h₁ : Runs s₁ st₁ st₂ T₁) (h₂ : Runs s₂ st₂ st₃ T₂) :
    Runs (.seq s₁ s₂) st₁ st₃ (T₁ + T₂) := by
  intro R off hsub
  simp only [Stmt.compile] at hsub
  have hsub₁ := hsub.append_left
  have hsub₂ := hsub.append_right
  rw [Stmt.length_compile] at hsub₂
  have r₁ := h₁ R off hsub₁
  have r₂ := h₂ R (off + s₁.codeLen) hsub₂
  have heq : off + s₁.codeLen + s₂.codeLen = off + (Stmt.seq s₁ s₂).codeLen := by
    simp [Stmt.codeLen]; omega
  rw [heq] at r₂
  exact r₁.trans r₂

theorem Runs.ifLeZero_true {r : ℕ} {t e : Stmt} {s₁ s₂ : MState} {T : ℕ}
    (hcond : s₁.regs r ≤ 0) (ht : Runs t s₁ s₂ T) :
    Runs (.ifLeZero r t e) s₁ s₂ (T + 1) := by
  intro R off hsub
  simp only [Stmt.compile, List.append_assoc] at hsub
  set elsePc := off + 1 + (e.compile (off + 1)).length + 1
  have hjle : R[off]? = some (.jle r elsePc) := hsub.append_left.singleton
  have hrest := hsub.append_right
  simp only [List.length_singleton] at hrest
  have hrest2 := hrest.append_right.append_right
  simp only [List.length_singleton] at hrest2
  have hpc : off + 1 + (e.compile (off + 1)).length + 1 = elsePc := rfl
  rw [hpc] at hrest2
  have step1 : RReaches R (s₁.toCfg off) (s₁.toCfg elsePc) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hjle, hcond])
  have step2 := ht R elsePc hrest2
  have hend : elsePc + t.codeLen = off + (Stmt.ifLeZero r t e).codeLen := by
    simp [elsePc, Stmt.length_compile, Stmt.codeLen]; omega
  rw [hend] at step2
  exact (step1.trans step2).mono (by omega)

theorem Runs.ifLeZero_false {r : ℕ} {t e : Stmt} {s₁ s₂ : MState} {T : ℕ}
    (hcond : ¬ s₁.regs r ≤ 0) (he : Runs e s₁ s₂ T) :
    Runs (.ifLeZero r t e) s₁ s₂ (T + 2) := by
  intro R off hsub
  simp only [Stmt.compile, List.append_assoc] at hsub
  set ce := e.compile (off + 1)
  set elsePc := off + 1 + ce.length + 1
  set ct := t.compile elsePc
  set endPc := elsePc + ct.length
  have hjle : R[off]? = some (.jle r elsePc) := hsub.append_left.singleton
  have hrest := hsub.append_right
  simp only [List.length_singleton] at hrest
  have hce : SubprogramAt R (off + 1) ce := hrest.append_left
  have hjmpSub := hrest.append_right.append_left
  have hjmp : R[off + 1 + ce.length]? = some (.pjle 0 0 endPc) := hjmpSub.singleton
  have step1 : RReaches R (s₁.toCfg off) (s₁.toCfg (off + 1)) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hjle, hcond])
  have step2 := he R (off + 1) hce
  have hceLen : off + 1 + e.codeLen = off + 1 + ce.length := by
    simp [ce, Stmt.length_compile]
  rw [← hceLen] at hjmp
  have step3 : RReaches R (s₂.toCfg (off + 1 + e.codeLen)) (s₂.toCfg endPc) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hjmp])
  have hend : endPc = off + (Stmt.ifLeZero r t e).codeLen := by
    simp [endPc, elsePc, ce, ct, Stmt.length_compile, Stmt.codeLen]; omega
  rw [hend] at step3
  exact ((step1.trans step2).trans step3).mono (by omega)

theorem Runs.ifPtrLe_true {q₁ q₂ : ℕ} {t e : Stmt} {s₁ s₂ : MState} {T : ℕ}
    (hcond : s₁.ptrs q₁ ≤ s₁.ptrs q₂) (ht : Runs t s₁ s₂ T) :
    Runs (.ifPtrLe q₁ q₂ t e) s₁ s₂ (T + 1) := by
  intro R off hsub
  simp only [Stmt.compile, List.append_assoc] at hsub
  set elsePc := off + 1 + (e.compile (off + 1)).length + 1
  have hpjle : R[off]? = some (.pjle q₁ q₂ elsePc) := hsub.append_left.singleton
  have hrest := hsub.append_right
  simp only [List.length_singleton] at hrest
  have hrest2 := hrest.append_right.append_right
  simp only [List.length_singleton] at hrest2
  have step1 : RReaches R (s₁.toCfg off) (s₁.toCfg elsePc) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hpjle, hcond])
  have step2 := ht R elsePc hrest2
  have hend : elsePc + t.codeLen = off + (Stmt.ifPtrLe q₁ q₂ t e).codeLen := by
    simp [elsePc, Stmt.length_compile, Stmt.codeLen]; omega
  rw [hend] at step2
  exact (step1.trans step2).mono (by omega)

theorem Runs.ifPtrLe_false {q₁ q₂ : ℕ} {t e : Stmt} {s₁ s₂ : MState} {T : ℕ}
    (hcond : ¬ s₁.ptrs q₁ ≤ s₁.ptrs q₂) (he : Runs e s₁ s₂ T) :
    Runs (.ifPtrLe q₁ q₂ t e) s₁ s₂ (T + 2) := by
  intro R off hsub
  simp only [Stmt.compile, List.append_assoc] at hsub
  set ce := e.compile (off + 1)
  set elsePc := off + 1 + ce.length + 1
  set ct := t.compile elsePc
  set endPc := elsePc + ct.length
  have hpjle : R[off]? = some (.pjle q₁ q₂ elsePc) := hsub.append_left.singleton
  have hrest := hsub.append_right
  simp only [List.length_singleton] at hrest
  have hce : SubprogramAt R (off + 1) ce := hrest.append_left
  have hjmp : R[off + 1 + ce.length]? = some (.pjle 0 0 endPc) :=
    hrest.append_right.append_left.singleton
  have step1 : RReaches R (s₁.toCfg off) (s₁.toCfg (off + 1)) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hpjle, hcond])
  have step2 := he R (off + 1) hce
  have hceLen : off + 1 + e.codeLen = off + 1 + ce.length := by
    simp [ce, Stmt.length_compile]
  rw [← hceLen] at hjmp
  have step3 : RReaches R (s₂.toCfg (off + 1 + e.codeLen)) (s₂.toCfg endPc) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hjmp])
  have hend : endPc = off + (Stmt.ifPtrLe q₁ q₂ t e).codeLen := by
    simp [endPc, elsePc, ce, ct, Stmt.length_compile, Stmt.codeLen]; omega
  rw [hend] at step3
  exact ((step1.trans step2).trans step3).mono (by omega)

theorem Runs.whilePtrLt_exit {q₁ q₂ : ℕ} {body : Stmt} {s : MState}
    (hcond : s.ptrs q₂ ≤ s.ptrs q₁) :
    Runs (.whilePtrLt q₁ q₂ body) s s 1 := by
  intro R off hsub
  simp only [Stmt.compile, List.append_assoc] at hsub
  set cb := body.compile (off + 1)
  set endPc := off + 1 + cb.length + 1
  have hpjle : R[off]? = some (.pjle q₂ q₁ endPc) := hsub.append_left.singleton
  have step1 : RReaches R (s.toCfg off) (s.toCfg endPc) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hpjle, hcond])
  have hend : endPc = off + (Stmt.whilePtrLt q₁ q₂ body).codeLen := by
    simp [endPc, cb, Stmt.length_compile, Stmt.codeLen, Nat.add_assoc]
  rwa [hend] at step1

theorem Runs.whilePtrLt_step {q₁ q₂ : ℕ} {body : Stmt} {s₁ s₂ s₃ : MState} {T₁ T₂ : ℕ}
    (hcond : s₁.ptrs q₁ < s₁.ptrs q₂)
    (hbody : Runs body s₁ s₂ T₁)
    (hrest : Runs (.whilePtrLt q₁ q₂ body) s₂ s₃ T₂) :
    Runs (.whilePtrLt q₁ q₂ body) s₁ s₃ (T₁ + T₂ + 2) := by
  intro R off hsub
  have hsubOrig := hsub
  simp only [Stmt.compile, List.append_assoc] at hsub
  set cb := body.compile (off + 1)
  set endPc := off + 1 + cb.length + 1
  have hpjle : R[off]? = some (.pjle q₂ q₁ endPc) := hsub.append_left.singleton
  have htail := hsub.append_right
  simp only [List.length_singleton] at htail
  have hcb : SubprogramAt R (off + 1) cb := htail.append_left
  have hjmp : R[off + 1 + cb.length]? = some (.pjle 0 0 off) := htail.append_right.singleton
  have hnotle : ¬ s₁.ptrs q₂ ≤ s₁.ptrs q₁ := not_le.mpr hcond
  have step1 : RReaches R (s₁.toCfg off) (s₁.toCfg (off + 1)) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hpjle, hnotle])
  have step2 := hbody R (off + 1) hcb
  have hcbLen : off + 1 + body.codeLen = off + 1 + cb.length := by
    simp [cb, Stmt.length_compile]
  rw [← hcbLen] at hjmp
  have step3 : RReaches R (s₂.toCfg (off + 1 + body.codeLen)) (s₂.toCfg off) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hjmp])
  have step4 := hrest R off hsubOrig
  exact (((step1.trans step2).trans step3).trans step4).mono (by omega)

theorem Runs.whilePos_exit {r : ℕ} {body : Stmt} {s : MState}
    (hcond : s.regs r ≤ 0) :
    Runs (.whilePos r body) s s 1 := by
  intro R off hsub
  simp only [Stmt.compile, List.append_assoc] at hsub
  set cb := body.compile (off + 1)
  set endPc := off + 1 + cb.length + 1
  have hjle : R[off]? = some (.jle r endPc) := hsub.append_left.singleton
  have step1 : RReaches R (s.toCfg off) (s.toCfg endPc) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hjle, hcond])
  have hend : endPc = off + (Stmt.whilePos r body).codeLen := by
    simp [endPc, cb, Stmt.length_compile, Stmt.codeLen, Nat.add_assoc]
  rwa [hend] at step1

theorem Runs.whilePos_step {r : ℕ} {body : Stmt} {s₁ s₂ s₃ : MState} {T₁ T₂ : ℕ}
    (hcond : 0 < s₁.regs r)
    (hbody : Runs body s₁ s₂ T₁)
    (hrest : Runs (.whilePos r body) s₂ s₃ T₂) :
    Runs (.whilePos r body) s₁ s₃ (T₁ + T₂ + 2) := by
  intro R off hsub
  have hsubOrig := hsub
  simp only [Stmt.compile, List.append_assoc] at hsub
  set cb := body.compile (off + 1)
  set endPc := off + 1 + cb.length + 1
  have hjle : R[off]? = some (.jle r endPc) := hsub.append_left.singleton
  have htail := hsub.append_right
  simp only [List.length_singleton] at htail
  have hcb : SubprogramAt R (off + 1) cb := htail.append_left
  have hjmp : R[off + 1 + cb.length]? = some (.pjle 0 0 off) := htail.append_right.singleton
  have hnotle : ¬ s₁.regs r ≤ 0 := not_le.mpr hcond
  have step1 : RReaches R (s₁.toCfg off) (s₁.toCfg (off + 1)) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hjle, hnotle])
  have step2 := hbody R (off + 1) hcb
  have hcbLen : off + 1 + body.codeLen = off + 1 + cb.length := by
    simp [cb, Stmt.length_compile]
  rw [← hcbLen] at hjmp
  have step3 : RReaches R (s₂.toCfg (off + 1 + body.codeLen)) (s₂.toCfg off) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hjmp])
  have step4 := hrest R off hsubOrig
  exact (((step1.trans step2).trans step3).trans step4).mono (by omega)

/-! ## Syntactic Register / Pointer Frame Protection -/

/-- `Prim` writes only to real registers `≥ rMin` and pointer registers `≥ pMin`. -/
def Prim.WritesAbove (rMin pMin : ℕ) : Prim → Prop
  | .const dst _ => rMin ≤ dst
  | .add dst _ _ => rMin ≤ dst
  | .sub dst _ _ => rMin ≤ dst
  | .mul dst _ _ => rMin ≤ dst
  | .div dst _ _ => rMin ≤ dst
  | .load dst _ => rMin ≤ dst
  | .store _ _ => True
  | .pset q _ => pMin ≤ q
  | .pcopy q _ => pMin ≤ q
  | .pinc q => pMin ≤ q
  | .pdec q => pMin ≤ q

/-- `Stmt` writes only to real registers `≥ rMin` and pointer registers `≥ pMin`. -/
def Stmt.WritesAbove (rMin pMin : ℕ) : Stmt → Prop
  | .skip => True
  | .prim p => p.WritesAbove rMin pMin
  | .seq s₁ s₂ => s₁.WritesAbove rMin pMin ∧ s₂.WritesAbove rMin pMin
  | .ifLeZero _ t e => t.WritesAbove rMin pMin ∧ e.WritesAbove rMin pMin
  | .ifPtrLe _ _ t e => t.WritesAbove rMin pMin ∧ e.WritesAbove rMin pMin
  | .whilePos _ body => body.WritesAbove rMin pMin
  | .whilePtrLt _ _ body => body.WritesAbove rMin pMin

theorem Prim.step_preserves_below {rMin pMin : ℕ} {p : Prim} {s : MState}
    (hw : p.WritesAbove rMin pMin) :
    (∀ r < rMin, (p.step s).regs r = s.regs r) ∧
    (∀ q < pMin, (p.step s).ptrs q = s.ptrs q) := by
  cases p <;> simp only [Prim.WritesAbove] at hw <;> refine ⟨fun r hr => ?_, fun q hq => ?_⟩ <;>
    simp [Prim.step, Function.update_apply] <;> omega

/-- Memory preservation below address `bound`. -/
def MemPreservedBelow (bound : ℤ) (m₁ m₂ : ℤ → ℝ) : Prop :=
  ∀ a < bound, m₂ a = m₁ a

theorem MemPreservedBelow.refl (bound : ℤ) (m : ℤ → ℝ) : MemPreservedBelow bound m m :=
  fun _ _ => rfl

theorem MemPreservedBelow.trans {bound : ℤ} {m₁ m₂ m₃ : ℤ → ℝ}
    (h₁ : MemPreservedBelow bound m₁ m₂) (h₂ : MemPreservedBelow bound m₂ m₃) :
    MemPreservedBelow bound m₁ m₃ :=
  fun a ha => (h₂ a ha).trans (h₁ a ha)

theorem MemPreservedBelow.mono {b₁ b₂ : ℤ} {m₁ m₂ : ℤ → ℝ}
    (h : MemPreservedBelow b₂ m₁ m₂) (hb : b₁ ≤ b₂) : MemPreservedBelow b₁ m₁ m₂ :=
  fun a ha => h a (lt_of_lt_of_le ha hb)

theorem MemPreservedBelow.update {bound addr : ℤ} {v : ℝ} (m : ℤ → ℝ) (h : bound ≤ addr) :
    MemPreservedBelow bound m (Function.update m addr v) := by
  intro a ha
  exact Function.update_of_ne (ne_of_lt (lt_of_lt_of_le ha h)) v m

/-! ## Top-Level Program Wrapper (`accept` iff `regs rAns ≤ 0`) -/

/-- Wrap `s : Stmt` into a decision `RAMProgram` that accepts iff `regs rAns ≤ 0`. -/
noncomputable def buildDecider (s : Stmt) (rAns : ℕ) : RAMProgram :=
  let code := s.compile 0
  code ++ [.jle rAns (code.length + 2), .reject, .accept]

theorem buildDecider_decides {s : Stmt} {rAns : ℕ} {x : ℤ → ℝ} {st : MState} {T : ℕ}
    (hrun : Runs s ⟨fun _ => 0, fun _ => 0, x⟩ st T) :
    RAMDecidesInTime (buildDecider s rAns) x (T + 1) (decide (st.regs rAns ≤ 0)) := by
  set R := buildDecider s rAns
  have hsub : SubprogramAt R 0 (s.compile 0) :=
    (SubprogramAt.self R).append_left
  have reach1 := hrun R 0 hsub
  simp only [Nat.zero_add] at reach1
  have htail : SubprogramAt R s.codeLen [.jle rAns (s.codeLen + 2), .reject, .accept] := by
    have h := (SubprogramAt.self R).append_right
    simpa [Stmt.length_compile] using h
  have hjle : R[s.codeLen]? = some (.jle rAns (s.codeLen + 2)) := by
    simpa using htail 0 (by simp)
  have hrej : R[s.codeLen + 1]? = some .reject := by
    simpa using htail 1 (by simp)
  have hacc : R[s.codeLen + 2]? = some .accept := by
    simpa using htail 2 (by simp)
  by_cases hle : st.regs rAns ≤ 0
  · have step2 : RReaches R (st.toCfg s.codeLen) (st.toCfg (s.codeLen + 2)) 1 :=
      RReaches.single (by simp [MState.toCfg, RAMStep, hjle, hle])
    obtain ⟨t, ht, heq⟩ := reach1.trans step2
    refine ⟨t, ht, ?_⟩
    simp only [RAMHaltedWith, RAMRun, decide_eq_true hle]
    rw [show (⟨0, fun _ => 0, fun _ => 0, x⟩ : RAMConfig) =
        MState.toCfg ⟨fun _ => 0, fun _ => 0, x⟩ 0 from rfl, heq]
    exact hacc
  · have step2 : RReaches R (st.toCfg s.codeLen) (st.toCfg (s.codeLen + 1)) 1 :=
      RReaches.single (by simp [MState.toCfg, RAMStep, hjle, hle])
    obtain ⟨t, ht, heq⟩ := reach1.trans step2
    refine ⟨t, ht, ?_⟩
    simp only [RAMHaltedWith, RAMRun, decide_eq_false hle]
    rw [show (⟨0, fun _ => 0, fun _ => 0, x⟩ : RAMConfig) =
        MState.toCfg ⟨fun _ => 0, fun _ => 0, x⟩ 0 from rfl, heq]
    exact hrej

/-- Fold a list of statements sequentially. -/
def Stmt.block : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: ss => .seq s (Stmt.block ss)

/-- Repeat a statement `k` times statically (unrolled at compile time). -/
def Stmt.repeatN : ℕ → Stmt → Stmt
  | 0, _ => .skip
  | k + 1, s => .seq s (Stmt.repeatN k s)

end MegiddoLP.MachineDSL


