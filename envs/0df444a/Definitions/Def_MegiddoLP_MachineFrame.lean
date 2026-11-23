-- Prove2me | Definitions.Def_MegiddoLP_MachineFrame
-- name    : MegiddoLP_MachineFrame
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-23T06:34:11.701104+00:00
-- url     : https://prove2.me/theorems/1b0fb5df-52e1-4f0b-8827-3a127a63e65d
-- title:
--   Frame specifications for compositional real pointer machine runs
-- statement:
--   The execution relation records an instruction bound together with preservation of specified registers, pointers, and earlier memory addresses. The accompanying composition rules carry these guarantees through the machine control flow.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §2 and §5. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_MegiddoLP_MachineDSL

namespace MegiddoLP.MachineDSL

open SmaleNinth

/-! ## Bundled `SpecRun` (Execution + Step Bound + Register/Pointer/Arena Frames) -/

/-- `st` runs from `s₁` to `s₂` within `T` steps while preserving all real registers `< rMin`,
all pointer registers `< pMin`, and all memory addresses `< memBound`. -/
structure SpecRun (rMin pMin : ℕ) (memBound : ℤ)
    (st : Stmt) (s₁ s₂ : MState) (T : ℕ) : Prop where
  runs : Runs st s₁ s₂ T
  regs_pres : ∀ r < rMin, s₂.regs r = s₁.regs r
  ptrs_pres : ∀ q < pMin, s₂.ptrs q = s₁.ptrs q
  mem_pres : MemPreservedBelow memBound s₁.mem s₂.mem

theorem SpecRun.mono {rMin pMin : ℕ} {memBound : ℤ} {st : Stmt} {s₁ s₂ : MState} {T T' : ℕ}
    (h : SpecRun rMin pMin memBound st s₁ s₂ T) (hT : T ≤ T') :
    SpecRun rMin pMin memBound st s₁ s₂ T' :=
  ⟨h.runs.mono hT, h.regs_pres, h.ptrs_pres, h.mem_pres⟩

theorem SpecRun.weakenFrame {rMin rMin' pMin pMin' : ℕ} {memBound memBound' : ℤ}
    {st : Stmt} {s₁ s₂ : MState} {T : ℕ}
    (h : SpecRun rMin' pMin' memBound' st s₁ s₂ T)
    (hr : rMin ≤ rMin') (hp : pMin ≤ pMin') (hm : memBound ≤ memBound') :
    SpecRun rMin pMin memBound st s₁ s₂ T :=
  ⟨h.runs,
   fun r hlt => h.regs_pres r (lt_of_lt_of_le hlt hr),
   fun q hlt => h.ptrs_pres q (lt_of_lt_of_le hlt hp),
   h.mem_pres.mono hm⟩

theorem SpecRun.skip (rMin pMin : ℕ) (memBound : ℤ) (s : MState) :
    SpecRun rMin pMin memBound .skip s s 0 :=
  ⟨Runs.skip s, fun _ _ => rfl, fun _ _ => rfl, MemPreservedBelow.refl memBound s.mem⟩

theorem SpecRun.prim {rMin pMin : ℕ} {memBound : ℤ} {p : Prim} {s : MState}
    (hw : p.WritesAbove rMin pMin)
    (hm : ∀ q i, p = .store q i → memBound ≤ s.ptrs q) :
    SpecRun rMin pMin memBound (.prim p) s (p.step s) 1 := by
  obtain ⟨hr, hp⟩ := Prim.step_preserves_below (s := s) hw
  refine ⟨Runs.prim p s, hr, hp, ?_⟩
  cases p with
  | store q i =>
    simpa [Prim.step] using MemPreservedBelow.update s.mem (hm q i rfl)
  | _ => exact MemPreservedBelow.refl memBound s.mem

theorem SpecRun.seq {rMin pMin : ℕ} {memBound : ℤ} {s₁ s₂ : Stmt}
    {st₁ st₂ st₃ : MState} {T₁ T₂ : ℕ}
    (h₁ : SpecRun rMin pMin memBound s₁ st₁ st₂ T₁)
    (h₂ : SpecRun rMin pMin memBound s₂ st₂ st₃ T₂) :
    SpecRun rMin pMin memBound (.seq s₁ s₂) st₁ st₃ (T₁ + T₂) :=
  ⟨h₁.runs.seq h₂.runs,
   fun r hr => (h₂.regs_pres r hr).trans (h₁.regs_pres r hr),
   fun q hq => (h₂.ptrs_pres q hq).trans (h₁.ptrs_pres q hq),
   h₁.mem_pres.trans h₂.mem_pres⟩

theorem SpecRun.ifLeZero_true {rMin pMin r : ℕ} {memBound : ℤ} {t e : Stmt}
    {s₁ s₂ : MState} {T : ℕ}
    (hcond : s₁.regs r ≤ 0)
    (ht : SpecRun rMin pMin memBound t s₁ s₂ T) :
    SpecRun rMin pMin memBound (.ifLeZero r t e) s₁ s₂ (T + 1) :=
  ⟨Runs.ifLeZero_true hcond ht.runs, ht.regs_pres, ht.ptrs_pres, ht.mem_pres⟩

theorem SpecRun.ifLeZero_false {rMin pMin r : ℕ} {memBound : ℤ} {t e : Stmt}
    {s₁ s₂ : MState} {T : ℕ}
    (hcond : ¬ s₁.regs r ≤ 0)
    (he : SpecRun rMin pMin memBound e s₁ s₂ T) :
    SpecRun rMin pMin memBound (.ifLeZero r t e) s₁ s₂ (T + 2) :=
  ⟨Runs.ifLeZero_false hcond he.runs, he.regs_pres, he.ptrs_pres, he.mem_pres⟩

theorem SpecRun.ifPtrLe_true {rMin pMin q₁ q₂ : ℕ} {memBound : ℤ} {t e : Stmt}
    {s₁ s₂ : MState} {T : ℕ}
    (hcond : s₁.ptrs q₁ ≤ s₁.ptrs q₂)
    (ht : SpecRun rMin pMin memBound t s₁ s₂ T) :
    SpecRun rMin pMin memBound (.ifPtrLe q₁ q₂ t e) s₁ s₂ (T + 1) :=
  ⟨Runs.ifPtrLe_true hcond ht.runs, ht.regs_pres, ht.ptrs_pres, ht.mem_pres⟩

theorem SpecRun.ifPtrLe_false {rMin pMin q₁ q₂ : ℕ} {memBound : ℤ} {t e : Stmt}
    {s₁ s₂ : MState} {T : ℕ}
    (hcond : ¬ s₁.ptrs q₁ ≤ s₁.ptrs q₂)
    (he : SpecRun rMin pMin memBound e s₁ s₂ T) :
    SpecRun rMin pMin memBound (.ifPtrLe q₁ q₂ t e) s₁ s₂ (T + 2) :=
  ⟨Runs.ifPtrLe_false hcond he.runs, he.regs_pres, he.ptrs_pres, he.mem_pres⟩

theorem SpecRun.whilePtrLt_exit {rMin pMin q₁ q₂ : ℕ} {memBound : ℤ} {body : Stmt} {s : MState}
    (hcond : s.ptrs q₂ ≤ s.ptrs q₁) :
    SpecRun rMin pMin memBound (.whilePtrLt q₁ q₂ body) s s 1 :=
  ⟨Runs.whilePtrLt_exit hcond, fun _ _ => rfl, fun _ _ => rfl,
   MemPreservedBelow.refl memBound s.mem⟩

theorem SpecRun.whilePtrLt_step {rMin pMin q₁ q₂ : ℕ} {memBound : ℤ} {body : Stmt}
    {s₁ s₂ s₃ : MState} {T₁ T₂ : ℕ}
    (hcond : s₁.ptrs q₁ < s₁.ptrs q₂)
    (hbody : SpecRun rMin pMin memBound body s₁ s₂ T₁)
    (hrest : SpecRun rMin pMin memBound (.whilePtrLt q₁ q₂ body) s₂ s₃ T₂) :
    SpecRun rMin pMin memBound (.whilePtrLt q₁ q₂ body) s₁ s₃ (T₁ + T₂ + 2) :=
  ⟨Runs.whilePtrLt_step hcond hbody.runs hrest.runs,
   fun r hr => (hrest.regs_pres r hr).trans (hbody.regs_pres r hr),
   fun q hq => (hrest.ptrs_pres q hq).trans (hbody.ptrs_pres q hq),
   hbody.mem_pres.trans hrest.mem_pres⟩

theorem SpecRun.whilePos_exit {rMin pMin r : ℕ} {memBound : ℤ} {body : Stmt} {s : MState}
    (hcond : s.regs r ≤ 0) :
    SpecRun rMin pMin memBound (.whilePos r body) s s 1 :=
  ⟨Runs.whilePos_exit hcond, fun _ _ => rfl, fun _ _ => rfl,
   MemPreservedBelow.refl memBound s.mem⟩

theorem SpecRun.whilePos_step {rMin pMin r : ℕ} {memBound : ℤ} {body : Stmt}
    {s₁ s₂ s₃ : MState} {T₁ T₂ : ℕ}
    (hcond : 0 < s₁.regs r)
    (hbody : SpecRun rMin pMin memBound body s₁ s₂ T₁)
    (hrest : SpecRun rMin pMin memBound (.whilePos r body) s₂ s₃ T₂) :
    SpecRun rMin pMin memBound (.whilePos r body) s₁ s₃ (T₁ + T₂ + 2) :=
  ⟨Runs.whilePos_step hcond hbody.runs hrest.runs,
   fun r' hr => (hrest.regs_pres r' hr).trans (hbody.regs_pres r' hr),
   fun q hq => (hrest.ptrs_pres q hq).trans (hbody.ptrs_pres q hq),
   hbody.mem_pres.trans hrest.mem_pres⟩

/-- Indexed bounded loop rule for `whilePtrLt`: runs exactly `N` iterations of `body`. -/
theorem SpecRun.forLoop {rMin pMin q₁ q₂ : ℕ} {memBound : ℤ} {body : Stmt}
    (N Tbody : ℕ) (Inv : ℕ → MState → Prop)
    (hStep : ∀ i < N, ∀ s, Inv i s →
      s.ptrs q₁ < s.ptrs q₂ ∧
      ∃ s', SpecRun rMin pMin memBound body s s' Tbody ∧ Inv (i + 1) s')
    (hExit : ∀ s, Inv N s → s.ptrs q₂ ≤ s.ptrs q₁) :
    ∀ k ≤ N, ∀ s, Inv (N - k) s →
      ∃ s', SpecRun rMin pMin memBound (.whilePtrLt q₁ q₂ body) s s'
        (k * (Tbody + 2) + 1) ∧ Inv N s' := by
  intro k
  induction k with
  | zero =>
    intro _ s hs
    simp only [Nat.sub_zero, Nat.zero_mul, Nat.zero_add] at hs ⊢
    exact ⟨s, SpecRun.whilePtrLt_exit (hExit s hs), hs⟩
  | succ k ih =>
    intro hk s hs
    have hlt : N - (k + 1) < N := by omega
    obtain ⟨hcond, s₁, hbody, hinv₁⟩ := hStep (N - (k + 1)) hlt s hs
    have heq : N - (k + 1) + 1 = N - k := by omega
    rw [heq] at hinv₁
    obtain ⟨s₂, hrest, hinv₂⟩ := ih (by omega) s₁ hinv₁
    refine ⟨s₂, (SpecRun.whilePtrLt_step hcond hbody hrest).mono ?_, hinv₂⟩
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Potential-based termination and linear runtime rule for `whilePos`:
if each active iteration takes `T₁` steps and reduces `Φ` by at least `T₁ + 2`,
the entire loop finishes within `Φ s₀ + 1` steps. -/
theorem SpecRun.whilePos_potential {rMin pMin r : ℕ} {memBound : ℤ} {body : Stmt}
    (Inv : MState → Prop) (Φ : MState → ℕ)
    (hStep : ∀ s, Inv s → 0 < s.regs r →
      ∃ s' T₁, SpecRun rMin pMin memBound body s s' T₁ ∧
        Inv s' ∧ T₁ + 2 + Φ s' ≤ Φ s) :
    ∀ B s, Inv s → Φ s ≤ B →
      ∃ s', SpecRun rMin pMin memBound (.whilePos r body) s s' (Φ s + 1) ∧
        Inv s' ∧ s'.regs r ≤ 0 := by
  intro B
  induction B using Nat.strong_induction_on with
  | h B ih =>
    intro s hs hB
    by_cases hle : s.regs r ≤ 0
    · exact ⟨s, (SpecRun.whilePos_exit hle).mono (by omega), hs, hle⟩
    · have hpos : 0 < s.regs r := not_le.mp hle
      obtain ⟨s₁, T₁, hbody, hs₁, hpot⟩ := hStep s hs hpos
      have hB' : Φ s₁ < B := by omega
      obtain ⟨s₂, hrest, hs₂, hexit⟩ := ih (Φ s₁) hB' s₁ hs₁ le_rfl
      refine ⟨s₂, (SpecRun.whilePos_step hpos hbody hrest).mono (by omega), hs₂, hexit⟩

/-- Compositional multi-iteration execution at the header of `Stmt.whilePos r body`:
transitions `(s₁.toCfg off)` back to `(s₂.toCfg off)` within `T` steps while preserving frames. -/
structure LoopStep (rMin pMin : ℕ) (memBound : ℤ)
    (r : ℕ) (body : Stmt) (s₁ s₂ : MState) (T : ℕ) : Prop where
  reaches : ∀ (R : RAMProgram) (off : ℕ),
    SubprogramAt R off ((Stmt.whilePos r body).compile off) →
    RReaches R (s₁.toCfg off) (s₂.toCfg off) T
  regs_pres : ∀ i < rMin, s₂.regs i = s₁.regs i
  ptrs_pres : ∀ q < pMin, s₂.ptrs q = s₁.ptrs q
  mem_pres : MemPreservedBelow memBound s₁.mem s₂.mem

theorem LoopStep.refl (rMin pMin : ℕ) (memBound : ℤ) (r : ℕ) (body : Stmt) (s : MState) :
    LoopStep rMin pMin memBound r body s s 0 :=
  ⟨fun R off _ => RReaches.refl R (s.toCfg off),
   fun _ _ => rfl, fun _ _ => rfl, MemPreservedBelow.refl memBound s.mem⟩

theorem LoopStep.mono {rMin pMin : ℕ} {memBound : ℤ} {r : ℕ} {body : Stmt}
    {s₁ s₂ : MState} {T T' : ℕ}
    (h : LoopStep rMin pMin memBound r body s₁ s₂ T) (hT : T ≤ T') :
    LoopStep rMin pMin memBound r body s₁ s₂ T' :=
  ⟨fun R off hsub => (h.reaches R off hsub).mono hT,
   h.regs_pres, h.ptrs_pres, h.mem_pres⟩

theorem LoopStep.weakenFrame {rMin rMin' pMin pMin' : ℕ} {memBound memBound' : ℤ}
    {r : ℕ} {body : Stmt} {s₁ s₂ : MState} {T : ℕ}
    (h : LoopStep rMin' pMin' memBound' r body s₁ s₂ T)
    (hr : rMin ≤ rMin') (hp : pMin ≤ pMin') (hm : memBound ≤ memBound') :
    LoopStep rMin pMin memBound r body s₁ s₂ T :=
  ⟨h.reaches,
   fun i hi => h.regs_pres i (lt_of_lt_of_le hi hr),
   fun q hq => h.ptrs_pres q (lt_of_lt_of_le hq hp),
   h.mem_pres.mono hm⟩

theorem LoopStep.trans {rMin pMin : ℕ} {memBound : ℤ} {r : ℕ} {body : Stmt}
    {s₁ s₂ s₃ : MState} {T₁ T₂ : ℕ}
    (h₁ : LoopStep rMin pMin memBound r body s₁ s₂ T₁)
    (h₂ : LoopStep rMin pMin memBound r body s₂ s₃ T₂) :
    LoopStep rMin pMin memBound r body s₁ s₃ (T₁ + T₂) :=
  ⟨fun R off hsub => (h₁.reaches R off hsub).trans (h₂.reaches R off hsub),
   fun i hi => (h₂.regs_pres i hi).trans (h₁.regs_pres i hi),
   fun q hq => (h₂.ptrs_pres q hq).trans (h₁.ptrs_pres q hq),
   h₁.mem_pres.trans h₂.mem_pres⟩

theorem LoopStep.single {rMin pMin : ℕ} {memBound : ℤ} {r : ℕ} {body : Stmt}
    {s₁ s₂ : MState} {T₁ : ℕ}
    (hcond : 0 < s₁.regs r)
    (hbody : SpecRun rMin pMin memBound body s₁ s₂ T₁) :
    LoopStep rMin pMin memBound r body s₁ s₂ (T₁ + 2) := by
  refine ⟨fun R off hsub => ?_, hbody.regs_pres, hbody.ptrs_pres, hbody.mem_pres⟩
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
  have step2 := hbody.runs R (off + 1) hcb
  have hcbLen : off + 1 + body.codeLen = off + 1 + cb.length := by
    simp [cb, Stmt.length_compile]
  rw [← hcbLen] at hjmp
  have step3 : RReaches R (s₂.toCfg (off + 1 + body.codeLen)) (s₂.toCfg off) 1 :=
    RReaches.single (by simp [MState.toCfg, RAMStep, hjmp])
  exact ((step1.trans step2).trans step3).mono (by omega)

theorem LoopStep.finish {rMin pMin : ℕ} {memBound : ℤ} {r : ℕ} {body : Stmt}
    {s₁ s₂ : MState} {T : ℕ}
    (hloop : LoopStep rMin pMin memBound r body s₁ s₂ T)
    (hexit : s₂.regs r ≤ 0) :
    SpecRun rMin pMin memBound (.whilePos r body) s₁ s₂ (T + 1) :=
  ⟨fun R off hsub => (hloop.reaches R off hsub).trans ((Runs.whilePos_exit hexit) R off hsub),
   hloop.regs_pres, hloop.ptrs_pres, hloop.mem_pres⟩

end MegiddoLP.MachineDSL


