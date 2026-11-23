-- Prove2me | Definitions.Def_MegiddoLP_VectorGadgets
-- name    : MegiddoLP_VectorGadgets
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-23T06:34:57.974082+00:00
-- url     : https://prove2.me/theorems/e96ff246-24b8-4bc3-949f-0738ef714bfe
-- title:
--   Vector and row operations for the real pointer machine
-- statement:
--   The structured machine programs load and store vectors and rows, compute dot products, and scan maximum constraint residuals. Their specifications record the output, frame conditions, and instruction bounds.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §2 and §5. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_MegiddoLP_MachineFrame
import Definitions.Def_MegiddoLP_Infeasibility
import Mathlib.Tactic

/-!
# Reusable Register, Pointer, Vector, and Row-Table Gadgets for `SmaleNinth.RAMProgram`

Provides verified building blocks (`SpecRun` specs) for:
- Exact zero comparison (`ifEqZero`) and register copying/maxing (`copyReg`, `maxIntoReg`).
- Pointer stepping (`advancePtrByConst`, `retreatPtrByConst`).
- Fixed-dimension vectors in registers (`VecRegs`) and memory (`VecAt`):
  `zeroRegs`, `copyRegs`, `loadVec`, `storeVec`, `dotRegs`.
- Interleaved LP row tables (`RowTableAt`):
  `loadRow`, `storeRow`, and `evalRowInfeasStmt` (computing `rInfeas` in `O_d(m)` steps).
-/

namespace MegiddoLP.VectorGadgets

open SmaleNinth Matrix MegiddoLP.MachineDSL MegiddoLP.Infeasibility

/-! ## Scalar Register Helpers -/

/-- Copy `s.regs rSrc` into `rDst` using scratch `rZero` (`rDst := rSrc + 0`). -/
noncomputable def copyReg (rDst rSrc rZero : ℕ) : Stmt :=
  .seq (.prim (.const rZero 0)) (.prim (.add rDst rSrc rZero))

theorem copyReg_spec {rMin pMin : ℕ} {memBound : ℤ} {rDst rSrc rZero : ℕ} {s : MState}
    (hDst : rMin ≤ rDst) (hZero : rMin ≤ rZero) (hneSrc : rSrc ≠ rZero) (hneDst : rDst ≠ rZero) :
    ∃ s', SpecRun rMin pMin memBound (copyReg rDst rSrc rZero) s s' 2 ∧
      s'.regs rDst = s.regs rSrc ∧
      s'.regs rZero = 0 ∧
      (∀ i, i ≠ rDst → i ≠ rZero → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have h1 : SpecRun rMin pMin memBound (.prim (.const rZero 0)) s
      ((Prim.const rZero 0).step s) 1 :=
    SpecRun.prim hZero (by intro _ _ h; cases h)
  set s₁ := (Prim.const rZero 0).step s
  have h2 : SpecRun rMin pMin memBound (.prim (.add rDst rSrc rZero)) s₁
      ((Prim.add rDst rSrc rZero).step s₁) 1 :=
    SpecRun.prim hDst (by intro _ _ h; cases h)
  refine ⟨_, h1.seq h2, ?_, ?_, ?_, rfl, rfl⟩
  · simp [s₁, Prim.step, Function.update_of_ne hneSrc]
  · simp [s₁, Prim.step, Function.update_of_ne hneDst.symm]
  · intro i hi1 hi2
    simp [s₁, Prim.step, Function.update_of_ne hi1, Function.update_of_ne hi2]

/-- Test `s.regs r = 0` via `s.regs r ≤ 0 ∧ -s.regs r ≤ 0`, using scratch `rZero`, `rNeg`. -/
noncomputable def ifEqZero (r rZero rNeg : ℕ) (t e : Stmt) : Stmt :=
  .seq (.prim (.const rZero 0))
    (.seq (.prim (.sub rNeg rZero r))
      (.ifLeZero r (.ifLeZero rNeg t e) e))

/-- State produced by the 2-instruction prefix of `ifEqZero`. -/
noncomputable def eqZeroPre (r rZero rNeg : ℕ) (s : MState) : MState :=
  (Prim.sub rNeg rZero r).step ((Prim.const rZero 0).step s)

@[simp] theorem eqZeroPre_ptrs (r rZero rNeg : ℕ) (s : MState) :
    (eqZeroPre r rZero rNeg s).ptrs = s.ptrs := rfl

@[simp] theorem eqZeroPre_mem (r rZero rNeg : ℕ) (s : MState) :
    (eqZeroPre r rZero rNeg s).mem = s.mem := rfl

theorem eqZeroPre_regs_other {r rZero rNeg i : ℕ} (s : MState)
    (h1 : i ≠ rZero) (h2 : i ≠ rNeg) :
    (eqZeroPre r rZero rNeg s).regs i = s.regs i := by
  simp [eqZeroPre, Prim.step, Function.update_of_ne h1, Function.update_of_ne h2]

theorem ifEqZero_true_spec {rMin pMin : ℕ} {memBound : ℤ}
    {r rZero rNeg : ℕ} {t e : Stmt} {s s' : MState} {T : ℕ}
    (hZero : rMin ≤ rZero) (hNeg : rMin ≤ rNeg)
    (hrZ : r ≠ rZero) (hrN : r ≠ rNeg) (_hZN : rZero ≠ rNeg)
    (heq : s.regs r = 0)
    (ht : SpecRun rMin pMin memBound t (eqZeroPre r rZero rNeg s) s' T) :
    SpecRun rMin pMin memBound (ifEqZero r rZero rNeg t e) s s' (T + 5) := by
  have p1 : SpecRun rMin pMin memBound (.prim (.const rZero 0)) s
      ((Prim.const rZero 0).step s) 1 :=
    SpecRun.prim hZero (by intro _ _ h; cases h)
  have p2 : SpecRun rMin pMin memBound (.prim (.sub rNeg rZero r))
      ((Prim.const rZero 0).step s) (eqZeroPre r rZero rNeg s) 1 :=
    SpecRun.prim hNeg (by intro _ _ h; cases h)
  have hr_le : (eqZeroPre r rZero rNeg s).regs r ≤ 0 := by
    rw [eqZeroPre_regs_other s hrZ hrN, heq]
  have hn_le : (eqZeroPre r rZero rNeg s).regs rNeg ≤ 0 := by
    simp [eqZeroPre, Prim.step, Function.update_of_ne hrZ, heq]
  have p3 : SpecRun rMin pMin memBound (.ifLeZero r (.ifLeZero rNeg t e) e)
      (eqZeroPre r rZero rNeg s) s' (T + 1 + 1) :=
    SpecRun.ifLeZero_true (e := e) hr_le (SpecRun.ifLeZero_true (e := e) hn_le ht)
  exact (p1.seq (p2.seq p3)).mono (by omega)

theorem ifEqZero_false_spec {rMin pMin : ℕ} {memBound : ℤ}
    {r rZero rNeg : ℕ} {t e : Stmt} {s s' : MState} {T : ℕ}
    (hZero : rMin ≤ rZero) (hNeg : rMin ≤ rNeg)
    (hrZ : r ≠ rZero) (hrN : r ≠ rNeg) (_hZN : rZero ≠ rNeg)
    (hne : s.regs r ≠ 0)
    (he : SpecRun rMin pMin memBound e (eqZeroPre r rZero rNeg s) s' T) :
    SpecRun rMin pMin memBound (ifEqZero r rZero rNeg t e) s s' (T + 5) := by
  have p1 : SpecRun rMin pMin memBound (.prim (.const rZero 0)) s
      ((Prim.const rZero 0).step s) 1 :=
    SpecRun.prim hZero (by intro _ _ h; cases h)
  have p2 : SpecRun rMin pMin memBound (.prim (.sub rNeg rZero r))
      ((Prim.const rZero 0).step s) (eqZeroPre r rZero rNeg s) 1 :=
    SpecRun.prim hNeg (by intro _ _ h; cases h)
  by_cases hle : s.regs r ≤ 0
  · have hlt : s.regs r < 0 := lt_of_le_of_ne hle hne
    have hr_le : (eqZeroPre r rZero rNeg s).regs r ≤ 0 := by
      rw [eqZeroPre_regs_other s hrZ hrN]; exact hle
    have hn_not_le : ¬ (eqZeroPre r rZero rNeg s).regs rNeg ≤ 0 := by
      simp only [eqZeroPre, Prim.step, Function.update_self, Function.update_of_ne hrZ]
      linarith
    have p3 : SpecRun rMin pMin memBound (.ifLeZero r (.ifLeZero rNeg t e) e)
        (eqZeroPre r rZero rNeg s) s' (T + 2 + 1) :=
      SpecRun.ifLeZero_true (e := e) hr_le (SpecRun.ifLeZero_false (t := t) hn_not_le he)
    exact (p1.seq (p2.seq p3)).mono (by omega)
  · have hr_not_le : ¬ (eqZeroPre r rZero rNeg s).regs r ≤ 0 := by
      rw [eqZeroPre_regs_other s hrZ hrN]; exact hle
    have p3 : SpecRun rMin pMin memBound (.ifLeZero r (.ifLeZero rNeg t e) e)
        (eqZeroPre r rZero rNeg s) s' (T + 2) :=
      SpecRun.ifLeZero_false (t := .ifLeZero rNeg t e) hr_not_le he
    exact (p1.seq (p2.seq p3)).mono (by omega)

/-- Update `rAcc := max (rAcc) (rVal)` using scratch `rDiff` and `rZero`. -/
noncomputable def maxIntoReg (rAcc rVal rDiff rZero : ℕ) : Stmt :=
  .seq (.prim (.sub rDiff rAcc rVal))
    (.ifLeZero rDiff (copyReg rAcc rVal rZero) .skip)

theorem maxIntoReg_spec {rMin pMin : ℕ} {memBound : ℤ}
    {rAcc rVal rDiff rZero : ℕ} {s : MState}
    (hAcc : rMin ≤ rAcc) (hDiff : rMin ≤ rDiff) (hZero : rMin ≤ rZero)
    (hAD : rAcc ≠ rDiff) (hVD : rVal ≠ rDiff)
    (hVZ : rVal ≠ rZero) (hAZ : rAcc ≠ rZero) :
    ∃ s', SpecRun rMin pMin memBound (maxIntoReg rAcc rVal rDiff rZero) s s' 5 ∧
      s'.regs rAcc = max (s.regs rAcc) (s.regs rVal) ∧
      (∀ i, i ≠ rAcc → i ≠ rDiff → i ≠ rZero → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have p1 : SpecRun rMin pMin memBound (.prim (.sub rDiff rAcc rVal)) s
      ((Prim.sub rDiff rAcc rVal).step s) 1 :=
    SpecRun.prim hDiff (by intro _ _ h; cases h)
  set s₁ := (Prim.sub rDiff rAcc rVal).step s
  by_cases hle : s.regs rAcc ≤ s.regs rVal
  · have hcond : s₁.regs rDiff ≤ 0 := by
      simp only [s₁, Prim.step, Function.update_self]; linarith
    obtain ⟨s₂, hc, hdst, _, hother, hptrs, hmem⟩ :=
      copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
        (s := s₁) hAcc hZero hVZ hAZ
    refine ⟨s₂, (p1.seq (SpecRun.ifLeZero_true (e := .skip) hcond hc)).mono (by omega),
      ?_, ?_, hptrs, hmem⟩
    · rw [hdst, max_eq_right hle]
      simp [s₁, Prim.step, Function.update_of_ne hVD]
    · intro i hiA hiD hiZ
      rw [hother i hiA hiZ]
      simp [s₁, Prim.step, Function.update_of_ne hiD]
  · have hcond : ¬ s₁.regs rDiff ≤ 0 := by
      simp only [s₁, Prim.step, Function.update_self]; linarith
    have p2 := SpecRun.ifLeZero_false (t := copyReg rAcc rVal rZero) hcond
      (SpecRun.skip rMin pMin memBound s₁)
    refine ⟨s₁, (p1.seq p2).mono (by omega), ?_, ?_, rfl, rfl⟩
    · rw [max_eq_left (le_of_not_ge hle)]
      simp [s₁, Prim.step, Function.update_of_ne hAD]
    · intro i _ hiD _
      simp [s₁, Prim.step, Function.update_of_ne hiD]

/-! ## Pointer Gadgets -/

/-- Advance pointer `q` by a compile-time constant `k`. -/
def advancePtrByConst (k q : ℕ) : Stmt :=
  Stmt.repeatN k (.prim (.pinc q))

theorem advancePtrByConst_spec {rMin pMin : ℕ} {memBound : ℤ} (k : ℕ) {q : ℕ}
    (hq : pMin ≤ q) (s : MState) :
    SpecRun rMin pMin memBound (advancePtrByConst k q) s
      ⟨s.regs, Function.update s.ptrs q (s.ptrs q + (k : ℤ)), s.mem⟩ k := by
  induction k generalizing s with
  | zero =>
    have heq : Function.update s.ptrs q (s.ptrs q + ((0 : ℕ) : ℤ)) = s.ptrs := by simp
    rw [heq]
    exact SpecRun.skip rMin pMin memBound s
  | succ k ih =>
    have p1 : SpecRun rMin pMin memBound (.prim (.pinc q)) s ((Prim.pinc q).step s) 1 :=
      SpecRun.prim hq (by intro _ _ h; cases h)
    have p2 := ih ((Prim.pinc q).step s)
    have hst : (⟨((Prim.pinc q).step s).regs,
        Function.update ((Prim.pinc q).step s).ptrs q
          (((Prim.pinc q).step s).ptrs q + (k : ℤ)),
        ((Prim.pinc q).step s).mem⟩ : MState) =
        ⟨s.regs, Function.update s.ptrs q (s.ptrs q + ((k + 1 : ℕ) : ℤ)), s.mem⟩ := by
      simp only [Prim.step, Function.update_self, Function.update_idem]
      congr 2; push_cast; ring
    rw [hst] at p2
    simpa [advancePtrByConst, Stmt.repeatN, Nat.add_comm] using p1.seq p2

/-- Retreat pointer `q` by a compile-time constant `k`. -/
def retreatPtrByConst (k q : ℕ) : Stmt :=
  Stmt.repeatN k (.prim (.pdec q))

theorem retreatPtrByConst_spec {rMin pMin : ℕ} {memBound : ℤ} (k : ℕ) {q : ℕ}
    (hq : pMin ≤ q) (s : MState) :
    SpecRun rMin pMin memBound (retreatPtrByConst k q) s
      ⟨s.regs, Function.update s.ptrs q (s.ptrs q - (k : ℤ)), s.mem⟩ k := by
  induction k generalizing s with
  | zero =>
    have heq : Function.update s.ptrs q (s.ptrs q - ((0 : ℕ) : ℤ)) = s.ptrs := by simp
    rw [heq]
    exact SpecRun.skip rMin pMin memBound s
  | succ k ih =>
    have p1 : SpecRun rMin pMin memBound (.prim (.pdec q)) s ((Prim.pdec q).step s) 1 :=
      SpecRun.prim hq (by intro _ _ h; cases h)
    have p2 := ih ((Prim.pdec q).step s)
    have hst : (⟨((Prim.pdec q).step s).regs,
        Function.update ((Prim.pdec q).step s).ptrs q
          (((Prim.pdec q).step s).ptrs q - (k : ℤ)),
        ((Prim.pdec q).step s).mem⟩ : MState) =
        ⟨s.regs, Function.update s.ptrs q (s.ptrs q - ((k + 1 : ℕ) : ℤ)), s.mem⟩ := by
      simp only [Prim.step, Function.update_self, Function.update_idem]
      congr 2; push_cast; ring
    rw [hst] at p2
    simpa [retreatPtrByConst, Stmt.repeatN, Nat.add_comm] using p1.seq p2

/-! ## Fixed-Dimension Vector Predicates and Gadgets -/

/-- `s.regs` stores `v : Fin d → ℝ` at `rVec .. rVec + d - 1`. -/
def VecRegs {d : ℕ} (s : MState) (rVec : ℕ) (v : Fin d → ℝ) : Prop :=
  ∀ j : Fin d, s.regs (rVec + j.1) = v j

/-- `mem` stores `v : Fin d → ℝ` at `addr .. addr + d - 1`. -/
def VecAt {d : ℕ} (mem : ℤ → ℝ) (addr : ℤ) (v : Fin d → ℝ) : Prop :=
  ∀ j : Fin d, mem (addr + (j.1 : ℤ)) = v j

/-- `mem` stores an `m × d` LP row table `(A, b)` at `base` with stride `d + 1`. -/
def RowTableAt {m d : ℕ} (mem : ℤ → ℝ) (base : ℤ)
    (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) : Prop :=
  ∀ i : Fin m,
    VecAt mem (base + (i.1 : ℤ) * ((d : ℤ) + 1)) (A i) ∧
    mem (base + (i.1 : ℤ) * ((d : ℤ) + 1) + (d : ℤ)) = b i

theorem VecRegs.of_pres {d : ℕ} {s₁ s₂ : MState} {rVec : ℕ} {v : Fin d → ℝ}
    (hv : VecRegs s₁ rVec v) (hp : ∀ j < d, s₂.regs (rVec + j) = s₁.regs (rVec + j)) :
    VecRegs s₂ rVec v :=
  fun j => (hp j.1 j.2).trans (hv j)

theorem VecAt.of_mem_pres {d : ℕ} {bound addr : ℤ} {m₁ m₂ : ℤ → ℝ} {v : Fin d → ℝ}
    (hv : VecAt m₁ addr v) (hm : MemPreservedBelow bound m₁ m₂)
    (hb : addr + (d : ℤ) ≤ bound) :
    VecAt m₂ addr v := by
  intro j
  have hlt : addr + (j.1 : ℤ) < bound := by have := j.2; omega
  exact (hm _ hlt).trans (hv j)

theorem RowTableAt.of_mem_pres {m d : ℕ} {bound base : ℤ} {m₁ m₂ : ℤ → ℝ}
    {A : Fin m → Fin d → ℝ} {b : Fin m → ℝ}
    (ht : RowTableAt m₁ base A b) (hm : MemPreservedBelow bound m₁ m₂)
    (hb : base + (m : ℤ) * ((d : ℤ) + 1) ≤ bound) :
    RowTableAt m₂ base A b := by
  intro i
  obtain ⟨hA, hbi⟩ := ht i
  have hi_end : base + ((i.1 : ℤ) + 1) * ((d : ℤ) + 1) ≤ bound := by
    have hle : ((i.1 : ℤ) + 1) * ((d : ℤ) + 1) ≤ (m : ℤ) * ((d : ℤ) + 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.succ_le_of_lt i.2
      · omega
    linarith
  refine ⟨hA.of_mem_pres hm (by linarith), ?_⟩
  exact (hm _ (by linarith)).trans hbi

/-- Zero out `k` consecutive registers `rDst .. rDst + k - 1`. -/
noncomputable def zeroRegs : ℕ → ℕ → Stmt
  | 0, _ => .skip
  | k + 1, rDst => .seq (.prim (.const rDst 0)) (zeroRegs k (rDst + 1))

theorem zeroRegs_spec {rMin pMin : ℕ} {memBound : ℤ} (d : ℕ) {rDst : ℕ}
    (hDst : rMin ≤ rDst) (s : MState) :
    ∃ s', SpecRun rMin pMin memBound (zeroRegs d rDst) s s' d ∧
      VecRegs s' rDst (0 : Fin d → ℝ) ∧
      (∀ i, i < rDst ∨ rDst + d ≤ i → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  induction d generalizing rMin rDst s with
  | zero =>
    exact ⟨s, SpecRun.skip rMin pMin memBound s, fun j => Fin.elim0 j,
      fun _ _ => rfl, rfl, rfl⟩
  | succ d ih =>
    have p1 : SpecRun rMin pMin memBound (.prim (.const rDst 0)) s
        ((Prim.const rDst 0).step s) 1 :=
      SpecRun.prim hDst (by intro _ _ h; cases h)
    set s₁ := (Prim.const rDst 0).step s
    obtain ⟨s₂, p2, hv, hother, hptrs, hmem⟩ := ih (rMin := rDst + 1) (rDst := rDst + 1) le_rfl s₁
    refine ⟨s₂, (p1.seq (p2.weakenFrame (by omega) le_rfl le_rfl)).mono (by omega),
      ?_, ?_, hptrs, hmem⟩
    · refine Fin.cases ?_ (fun j' => ?_)
      · simp only [Fin.val_zero, Nat.add_zero]
        rw [p2.regs_pres rDst (by omega)]
        simp [s₁, Prim.step]
      · have := hv j'
        simpa [Nat.add_assoc, Nat.add_comm 1] using this
    · intro i hi
      rw [hother i (by omega)]
      simp [s₁, Prim.step, Function.update_of_ne (show i ≠ rDst by omega)]

/-- Copy `d` registers from `rSrc .. rSrc + d - 1` to `rDst .. rDst + d - 1` using `rZero`. -/
noncomputable def copyRegs : ℕ → ℕ → ℕ → ℕ → Stmt
  | 0, _, _, _ => .skip
  | k + 1, rDst, rSrc, rZero =>
    .seq (copyReg rDst rSrc rZero) (copyRegs k (rDst + 1) (rSrc + 1) rZero)

theorem copyRegs_spec {rMin pMin : ℕ} {memBound : ℤ} (d : ℕ)
    {rDst rSrc rZero : ℕ} {v : Fin d → ℝ} {s : MState}
    (hv : VecRegs s rSrc v)
    (hDst : rMin ≤ rDst) (hZero : rMin ≤ rZero)
    (hDisjDS : rDst + d ≤ rSrc ∨ rSrc + d ≤ rDst)
    (hDisjSZ : rZero < rSrc ∨ rSrc + d ≤ rZero)
    (hDisjDZ : rZero < rDst ∨ rDst + d ≤ rZero) :
    ∃ s', SpecRun rMin pMin memBound (copyRegs d rDst rSrc rZero) s s' (2 * d) ∧
      VecRegs s' rDst v ∧
      (∀ i, (i < rDst ∨ rDst + d ≤ i) → i ≠ rZero → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  induction d generalizing rDst rSrc s with
  | zero =>
    exact ⟨s, SpecRun.skip rMin pMin memBound s, fun j => Fin.elim0 j,
      fun _ _ _ => rfl, rfl, rfl⟩
  | succ d ih =>
    obtain ⟨s₁, p1, hdst0, _, hother1, hptrs1, hmem1⟩ :=
      copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
        (rDst := rDst) (rSrc := rSrc) (rZero := rZero) (s := s)
        hDst hZero (by omega) (by omega)
    have hvTail : VecRegs s₁ (rSrc + 1) (Fin.tail v) := by
      intro j
      rw [hother1 (rSrc + 1 + j.1) (by omega) (by omega)]
      have := hv j.succ
      simpa [Fin.tail, Nat.add_assoc, Nat.add_comm 1] using this
    obtain ⟨s₂, p2, hv2, hother2, hptrs2, hmem2⟩ :=
      ih (rDst := rDst + 1) (rSrc := rSrc + 1) (v := Fin.tail v) (s := s₁)
        hvTail (by omega) (by omega) (by omega) (by omega)
    refine ⟨s₂, (p1.seq p2).mono (by omega), ?_, ?_, hptrs2.trans hptrs1, hmem2.trans hmem1⟩
    · refine Fin.cases ?_ (fun j' => ?_)
      · simp only [Fin.val_zero, Nat.add_zero]
        rw [hother2 rDst (by omega) (by omega), hdst0]
        simpa using hv 0
      · have := hv2 j'
        simpa [Fin.tail, Nat.add_assoc, Nat.add_comm 1] using this
    · intro i hi hiZ
      rw [hother2 i (by omega) hiZ, hother1 i (by omega) hiZ]

/-- Load `d` reals from `[ptrs q .. ptrs q + d)` into `rDst .. rDst + d - 1`, advancing `q` by `d`. -/
def loadVec : ℕ → ℕ → ℕ → Stmt
  | 0, _, _ => .skip
  | k + 1, rDst, q =>
    .seq (.seq (.prim (.load rDst q)) (.prim (.pinc q))) (loadVec k (rDst + 1) q)

theorem loadVec_spec {rMin pMin : ℕ} {memBound : ℤ} (d : ℕ)
    {rDst q : ℕ} {v : Fin d → ℝ} {s : MState}
    (hv : VecAt s.mem (s.ptrs q) v)
    (hDst : rMin ≤ rDst) (hq : pMin ≤ q) :
    ∃ s', SpecRun rMin pMin memBound (loadVec d rDst q) s s' (2 * d) ∧
      VecRegs s' rDst v ∧
      (∀ i, i < rDst ∨ rDst + d ≤ i → s'.regs i = s.regs i) ∧
      s'.ptrs = Function.update s.ptrs q (s.ptrs q + (d : ℤ)) ∧
      s'.mem = s.mem := by
  induction d generalizing rMin rDst s with
  | zero =>
    refine ⟨s, SpecRun.skip rMin pMin memBound s, fun j => Fin.elim0 j,
      fun _ _ => rfl, ?_, rfl⟩
    simp
  | succ d ih =>
    have p1 : SpecRun rMin pMin memBound (.prim (.load rDst q)) s
        ((Prim.load rDst q).step s) 1 :=
      SpecRun.prim hDst (by intro _ _ h; cases h)
    set s₁ := (Prim.load rDst q).step s
    have p2 : SpecRun rMin pMin memBound (.prim (.pinc q)) s₁
        ((Prim.pinc q).step s₁) 1 :=
      SpecRun.prim hq (by intro _ _ h; cases h)
    set s₂ := (Prim.pinc q).step s₁
    have hvTail : VecAt s₂.mem (s₂.ptrs q) (Fin.tail v) := by
      intro j
      simp only [s₂, s₁, Prim.step, Function.update_self, Fin.tail]
      have h := hv j.succ
      simpa [add_assoc, add_comm (1 : ℤ)] using h
    obtain ⟨s₃, p3, hv3, hother3, hptrs3, hmem3⟩ :=
      ih (rMin := rDst + 1) (rDst := rDst + 1) (v := Fin.tail v) (s := s₂) hvTail le_rfl
    refine ⟨s₃, ((p1.seq p2).seq (p3.weakenFrame (by omega) le_rfl le_rfl)).mono (by omega),
      ?_, ?_, ?_, hmem3⟩
    · refine Fin.cases ?_ (fun j' => ?_)
      · simp only [Fin.val_zero, Nat.add_zero]
        rw [p3.regs_pres rDst (by omega)]
        simpa [s₂, s₁, Prim.step] using hv 0
      · have := hv3 j'
        simpa [Fin.tail, Nat.add_assoc, Nat.add_comm 1] using this
    · intro i hi
      rw [hother3 i (by omega)]
      simp [s₂, s₁, Prim.step, Function.update_of_ne (show i ≠ rDst by omega)]
    · rw [hptrs3]
      simp only [s₂, s₁, Prim.step, Function.update_self, Function.update_idem]
      congr 1; push_cast; ring

/-- Store `d` reals from `rSrc .. rSrc + d - 1` into `[ptrs q .. ptrs q + d)`, advancing `q` by `d`. -/
def storeVec : ℕ → ℕ → ℕ → Stmt
  | 0, _, _ => .skip
  | k + 1, q, rSrc =>
    .seq (.seq (.prim (.store q rSrc)) (.prim (.pinc q))) (storeVec k q (rSrc + 1))

theorem storeVec_spec {rMin pMin : ℕ} {memBound : ℤ} (d : ℕ)
    {q rSrc : ℕ} {v : Fin d → ℝ} {s : MState}
    (hv : VecRegs s rSrc v)
    (hq : pMin ≤ q) (hm : memBound ≤ s.ptrs q) :
    ∃ s', SpecRun rMin pMin memBound (storeVec d q rSrc) s s' (2 * d) ∧
      VecAt s'.mem (s.ptrs q) v ∧
      s'.regs = s.regs ∧
      s'.ptrs = Function.update s.ptrs q (s.ptrs q + (d : ℤ)) ∧
      (∀ a, a < s.ptrs q ∨ s.ptrs q + (d : ℤ) ≤ a → s'.mem a = s.mem a) := by
  induction d generalizing memBound rSrc s with
  | zero =>
    refine ⟨s, SpecRun.skip rMin pMin memBound s, fun j => Fin.elim0 j, rfl, ?_, fun _ _ => rfl⟩
    simp
  | succ d ih =>
    have p1 : SpecRun rMin pMin memBound (.prim (.store q rSrc)) s
        ((Prim.store q rSrc).step s) 1 :=
      SpecRun.prim trivial (by intro _ _ h; cases h; exact hm)
    set s₁ := (Prim.store q rSrc).step s
    have p2 : SpecRun rMin pMin memBound (.prim (.pinc q)) s₁
        ((Prim.pinc q).step s₁) 1 :=
      SpecRun.prim hq (by intro _ _ h; cases h)
    set s₂ := (Prim.pinc q).step s₁
    have hvTail : VecRegs s₂ (rSrc + 1) (Fin.tail v) := by
      intro j
      have := hv j.succ
      simpa [s₂, s₁, Prim.step, Fin.tail, Nat.add_assoc, Nat.add_comm 1] using this
    obtain ⟨s₃, p3, hv3, hregs3, hptrs3, hmem3⟩ :=
      ih (memBound := s.ptrs q + 1) (rSrc := rSrc + 1) (v := Fin.tail v) (s := s₂)
        hvTail (by simp [s₂, s₁, Prim.step])
    refine ⟨s₃, ((p1.seq p2).seq (p3.weakenFrame le_rfl le_rfl (by omega))).mono (by omega),
      ?_, hregs3, ?_, ?_⟩
    · refine Fin.cases ?_ (fun j' => ?_)
      · simp only [Fin.val_zero, Int.ofNat_zero, add_zero]
        rw [p3.mem_pres (s.ptrs q) (by omega)]
        simpa [s₂, s₁, Prim.step] using hv 0
      · have h := hv3 j'
        simp only [s₂, s₁, Prim.step, Function.update_self, Fin.tail] at h
        simpa [add_assoc, add_comm (1 : ℤ)] using h
    · rw [hptrs3]
      simp only [s₂, s₁, Prim.step, Function.update_self, Function.update_idem]
      congr 1; push_cast; ring
    · intro a ha
      have ha' : a < s₂.ptrs q ∨ s₂.ptrs q + (d : ℤ) ≤ a := by
        simp only [s₂, s₁, Prim.step, Function.update_self]
        rcases ha with h | h
        · left; omega
        · right; push_cast at h; linarith
      rw [hmem3 a ha']
      simp only [s₂, s₁, Prim.step]
      exact Function.update_of_ne (by rcases ha with h | h <;> [omega; (push_cast at h; omega)]) _ _

/-- Accumulate `∑ j : Fin k, a j * x j` into `rAcc` using scratch `rProd`. -/
def dotRegsAux : ℕ → ℕ → ℕ → ℕ → ℕ → Stmt
  | 0, _, _, _, _ => .skip
  | k + 1, rAcc, rA, rX, rProd =>
    .seq (.seq (.prim (.mul rProd rA rX)) (.prim (.add rAcc rAcc rProd)))
      (dotRegsAux k rAcc (rA + 1) (rX + 1) rProd)

/-- Compute dot product `a ⬝ᵥ x` (`d` coords) into `rAcc` using scratch `rProd`. -/
noncomputable def dotRegs (d rAcc rA rX rProd : ℕ) : Stmt :=
  .seq (.prim (.const rAcc 0)) (dotRegsAux d rAcc rA rX rProd)

theorem dotRegsAux_spec {rMin pMin : ℕ} {memBound : ℤ} (d : ℕ)
    {rAcc rA rX rProd : ℕ} {a x : Fin d → ℝ} {s : MState}
    (ha : VecRegs s rA a) (hx : VecRegs s rX x)
    (hAcc : rMin ≤ rAcc) (hProd : rMin ≤ rProd) (hAP : rAcc ≠ rProd)
    (hDisjA : (rAcc < rA ∨ rA + d ≤ rAcc) ∧ (rProd < rA ∨ rA + d ≤ rProd))
    (hDisjX : (rAcc < rX ∨ rX + d ≤ rAcc) ∧ (rProd < rX ∨ rX + d ≤ rProd)) :
    ∃ s', SpecRun rMin pMin memBound (dotRegsAux d rAcc rA rX rProd) s s' (2 * d) ∧
      s'.regs rAcc = s.regs rAcc + a ⬝ᵥ x ∧
      (∀ i, i ≠ rAcc → i ≠ rProd → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  induction d generalizing rA rX s with
  | zero =>
    refine ⟨s, SpecRun.skip rMin pMin memBound s, ?_, fun _ _ _ => rfl, rfl, rfl⟩
    simp [dotProduct]
  | succ d ih =>
    have p1 : SpecRun rMin pMin memBound (.prim (.mul rProd rA rX)) s
        ((Prim.mul rProd rA rX).step s) 1 :=
      SpecRun.prim hProd (by intro _ _ h; cases h)
    set s₁ := (Prim.mul rProd rA rX).step s
    have p2 : SpecRun rMin pMin memBound (.prim (.add rAcc rAcc rProd)) s₁
        ((Prim.add rAcc rAcc rProd).step s₁) 1 :=
      SpecRun.prim hAcc (by intro _ _ h; cases h)
    set s₂ := (Prim.add rAcc rAcc rProd).step s₁
    have haTail : VecRegs s₂ (rA + 1) (Fin.tail a) := by
      intro j
      have hne1 : rA + 1 + j.1 ≠ rAcc := by omega
      have hne2 : rA + 1 + j.1 ≠ rProd := by omega
      simp only [s₂, s₁, Prim.step, Function.update_of_ne hne1, Function.update_of_ne hne2]
      simpa [Fin.tail, Nat.add_assoc, Nat.add_comm 1] using ha j.succ
    have hxTail : VecRegs s₂ (rX + 1) (Fin.tail x) := by
      intro j
      have hne1 : rX + 1 + j.1 ≠ rAcc := by omega
      have hne2 : rX + 1 + j.1 ≠ rProd := by omega
      simp only [s₂, s₁, Prim.step, Function.update_of_ne hne1, Function.update_of_ne hne2]
      simpa [Fin.tail, Nat.add_assoc, Nat.add_comm 1] using hx j.succ
    obtain ⟨s₃, p3, hacc3, hother3, hptrs3, hmem3⟩ :=
      ih (rA := rA + 1) (rX := rX + 1) (a := Fin.tail a) (x := Fin.tail x) (s := s₂)
        haTail hxTail ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    refine ⟨s₃, ((p1.seq p2).seq p3).mono (by omega), ?_, ?_, hptrs3, hmem3⟩
    · rw [hacc3]
      have hs₂Acc : s₂.regs rAcc = s.regs rAcc + a 0 * x 0 := by
        simp only [s₂, s₁, Prim.step, Function.update_self, Function.update_of_ne hAP]
        rw [← ha 0, ← hx 0]; simp
      rw [hs₂Acc]
      simp only [dotProduct, Fin.sum_univ_succ, Fin.tail]
      ring
    · intro i hi1 hi2
      rw [hother3 i hi1 hi2]
      simp [s₂, s₁, Prim.step, Function.update_of_ne hi1, Function.update_of_ne hi2]

theorem dotRegs_spec {rMin pMin : ℕ} {memBound : ℤ} (d : ℕ)
    {rAcc rA rX rProd : ℕ} {a x : Fin d → ℝ} {s : MState}
    (ha : VecRegs s rA a) (hx : VecRegs s rX x)
    (hAcc : rMin ≤ rAcc) (hProd : rMin ≤ rProd) (hAP : rAcc ≠ rProd)
    (hDisjA : (rAcc < rA ∨ rA + d ≤ rAcc) ∧ (rProd < rA ∨ rA + d ≤ rProd))
    (hDisjX : (rAcc < rX ∨ rX + d ≤ rAcc) ∧ (rProd < rX ∨ rX + d ≤ rProd)) :
    ∃ s', SpecRun rMin pMin memBound (dotRegs d rAcc rA rX rProd) s s' (2 * d + 1) ∧
      s'.regs rAcc = a ⬝ᵥ x ∧
      (∀ i, i ≠ rAcc → i ≠ rProd → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have p0 : SpecRun rMin pMin memBound (.prim (.const rAcc 0)) s
      ((Prim.const rAcc 0).step s) 1 :=
    SpecRun.prim hAcc (by intro _ _ h; cases h)
  set s₀ := (Prim.const rAcc 0).step s
  have ha0 : VecRegs s₀ rA a :=
    ha.of_pres fun j hj => Function.update_of_ne (by omega) _ _
  have hx0 : VecRegs s₀ rX x :=
    hx.of_pres fun j hj => Function.update_of_ne (by omega) _ _
  obtain ⟨s₁, p1, hacc, hother, hptrs, hmem⟩ :=
    dotRegsAux_spec d ha0 hx0 hAcc hProd hAP hDisjA hDisjX (memBound := memBound)
  refine ⟨s₁, (p0.seq p1).mono (by omega), ?_, ?_, hptrs, hmem⟩
  · rw [hacc]; simp [s₀, Prim.step]
  · intro i hi1 hi2
    rw [hother i hi1 hi2]
    simp [s₀, Prim.step, Function.update_of_ne hi1]

/-! ## Row-Table Load / Store / Residual / `rInfeas` Evaluation -/

/-- Load one `(d + 1)`-cell row `(a, β)` through pointer `q`, advancing `q` by `d + 1`. -/
def loadRow (d rA rB q : ℕ) : Stmt :=
  .seq (loadVec d rA q) (.seq (.prim (.load rB q)) (.prim (.pinc q)))

theorem loadRow_spec {rMin pMin : ℕ} {memBound : ℤ} (d : ℕ)
    {rA rB q : ℕ} {a : Fin d → ℝ} {β : ℝ} {s : MState}
    (ha : VecAt s.mem (s.ptrs q) a) (hb : s.mem (s.ptrs q + (d : ℤ)) = β)
    (hA : rMin ≤ rA) (hB : rMin ≤ rB) (hAB : rA + d ≤ rB) (hq : pMin ≤ q) :
    ∃ s', SpecRun rMin pMin memBound (loadRow d rA rB q) s s' (2 * d + 2) ∧
      VecRegs s' rA a ∧ s'.regs rB = β ∧
      (∀ i, (i < rA ∨ rA + d ≤ i) → i ≠ rB → s'.regs i = s.regs i) ∧
      s'.ptrs = Function.update s.ptrs q (s.ptrs q + ((d : ℤ) + 1)) ∧
      s'.mem = s.mem := by
  obtain ⟨s₁, p1, hv1, hother1, hptrs1, hmem1⟩ := loadVec_spec d ha hA hq (memBound := memBound)
  have p2 : SpecRun rMin pMin memBound (.prim (.load rB q)) s₁
      ((Prim.load rB q).step s₁) 1 :=
    SpecRun.prim hB (by intro _ _ h; cases h)
  set s₂ := (Prim.load rB q).step s₁
  have p3 : SpecRun rMin pMin memBound (.prim (.pinc q)) s₂
      ((Prim.pinc q).step s₂) 1 :=
    SpecRun.prim hq (by intro _ _ h; cases h)
  set s₃ := (Prim.pinc q).step s₂
  refine ⟨s₃, (p1.seq (p2.seq p3)).mono (by omega), ?_, ?_, ?_, ?_, hmem1⟩
  · exact hv1.of_pres fun j hj => by
      simp [s₃, s₂, Prim.step, Function.update_of_ne (show rA + j ≠ rB by omega)]
  · simp [s₃, s₂, Prim.step, hptrs1, hmem1, hb]
  · intro i hiA hiB
    simp only [s₃, s₂, Prim.step, Function.update_of_ne hiB]
    exact hother1 i hiA
  · simp only [s₃, s₂, Prim.step, hptrs1, Function.update_self, Function.update_idem]
    congr 1; ring

/-- Store one `(d + 1)`-cell row `(a, β)` through pointer `q`, advancing `q` by `d + 1`. -/
def storeRow (d q rA rB : ℕ) : Stmt :=
  .seq (storeVec d q rA) (.seq (.prim (.store q rB)) (.prim (.pinc q)))

theorem storeRow_spec {rMin pMin : ℕ} {memBound : ℤ} (d : ℕ)
    {q rA rB : ℕ} {a : Fin d → ℝ} {β : ℝ} {s : MState}
    (ha : VecRegs s rA a) (hb : s.regs rB = β)
    (hq : pMin ≤ q) (hm : memBound ≤ s.ptrs q) :
    ∃ s', SpecRun rMin pMin memBound (storeRow d q rA rB) s s' (2 * d + 2) ∧
      VecAt s'.mem (s.ptrs q) a ∧ s'.mem (s.ptrs q + (d : ℤ)) = β ∧
      s'.regs = s.regs ∧
      s'.ptrs = Function.update s.ptrs q (s.ptrs q + ((d : ℤ) + 1)) ∧
      (∀ addr, addr < s.ptrs q ∨ s.ptrs q + ((d : ℤ) + 1) ≤ addr → s'.mem addr = s.mem addr) := by
  obtain ⟨s₁, p1, hv1, hregs1, hptrs1, hmem1⟩ := storeVec_spec d ha hq hm (rMin := rMin)
  have hm2 : memBound ≤ s₁.ptrs q := by rw [hptrs1, Function.update_self]; omega
  have p2 : SpecRun rMin pMin memBound (.prim (.store q rB)) s₁
      ((Prim.store q rB).step s₁) 1 :=
    SpecRun.prim trivial (by intro _ _ h; cases h; exact hm2)
  set s₂ := (Prim.store q rB).step s₁
  have p3 : SpecRun rMin pMin memBound (.prim (.pinc q)) s₂
      ((Prim.pinc q).step s₂) 1 :=
    SpecRun.prim hq (by intro _ _ h; cases h)
  set s₃ := (Prim.pinc q).step s₂
  refine ⟨s₃, (p1.seq (p2.seq p3)).mono (by omega), ?_, ?_, hregs1, ?_, ?_⟩
  · intro j
    simp only [s₃, s₂, Prim.step, hptrs1, Function.update_self]
    rw [Function.update_of_ne (by have := j.2; omega)]
    exact hv1 j
  · simp [s₃, s₂, Prim.step, hptrs1, hregs1, hb]
  · simp only [s₃, s₂, Prim.step, hptrs1, Function.update_self, Function.update_idem]
    congr 1; ring
  · intro addr haddr
    simp only [s₃, s₂, Prim.step, hptrs1, Function.update_self]
    rw [Function.update_of_ne (by omega)]
    exact hmem1 addr (by omega)

/-- Recursive prefix maximum over rows `0 .. k` of `b i - A i ⬝ᵥ x`. -/
noncomputable def prefResMax {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (x : Fin d → ℝ) :
    (k : ℕ) → k < m → ℝ
  | 0, _ => b ⟨0, hm⟩ - A ⟨0, hm⟩ ⬝ᵥ x
  | t + 1, ht1 =>
    max (prefResMax hm A b x t (Nat.lt_of_succ_lt ht1)) (b ⟨t + 1, ht1⟩ - A ⟨t + 1, ht1⟩ ⬝ᵥ x)

theorem prefResMax_spec {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (x : Fin d → ℝ) :
    ∀ (k : ℕ) (hk : k < m),
      (∀ i : Fin m, i.1 ≤ k → b i - A i ⬝ᵥ x ≤ prefResMax hm A b x k hk) ∧
      (∃ i : Fin m, i.1 ≤ k ∧ prefResMax hm A b x k hk = b i - A i ⬝ᵥ x)
  | 0, _ => by
    refine ⟨fun i hi => ?_, ⟨⟨0, hm⟩, le_rfl, rfl⟩⟩
    have h0 : i = ⟨0, hm⟩ := Fin.ext (Nat.eq_zero_of_le_zero hi)
    subst h0; exact le_rfl
  | t + 1, ht1 => by
    obtain ⟨hub, i₀, hi₀, heq₀⟩ := prefResMax_spec hm A b x t (Nat.lt_of_succ_lt ht1)
    refine ⟨fun i hi => ?_, ?_⟩
    · simp only [prefResMax]
      rcases Nat.of_le_succ hi with hle | heq
      · exact le_max_of_le_left (hub i hle)
      · have hi_eq : i = ⟨t + 1, ht1⟩ := Fin.ext heq
        subst hi_eq; exact le_max_right _ _
    · simp only [prefResMax]
      rcases le_total (prefResMax hm A b x t (Nat.lt_of_succ_lt ht1))
          (b ⟨t + 1, ht1⟩ - A ⟨t + 1, ht1⟩ ⬝ᵥ x) with h | h
      · exact ⟨⟨t + 1, ht1⟩, le_rfl, max_eq_right h⟩
      · exact ⟨i₀, by omega, (max_eq_left h).trans heq₀⟩

theorem prefResMax_full {m d : ℕ} (hm : 0 < m)
    (A : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (x : Fin d → ℝ) :
    prefResMax hm A b x (m - 1) (by omega) = rInfeas hm A b x := by
  obtain ⟨hub, i₀, _, heq₀⟩ := prefResMax_spec hm A b x (m - 1) (by omega)
  apply le_antisymm
  · rw [heq₀]; exact le_rInfeas hm A b x i₀
  · rw [rInfeas_le_iff]
    exact fun i => hub i (by omega)

/-- Evaluate `rInfeas hm A b x` from `RowTableAt s.mem (s.ptrs pTabStart) A b` (`0 < m`)
and `VecRegs s rX x` into `rOut`.
Needs `d + 6` scratch registers starting at `rScratch` and `1` scratch pointer `pCur`. -/
noncomputable def evalRowInfeasStmt (d rOut pTabStart pTabEnd rX rScratch pCur : ℕ) : Stmt :=
  let rA := rScratch
  let rB := rScratch + d
  let rDot := rScratch + d + 1
  let rProd := rScratch + d + 2
  let rRes := rScratch + d + 3
  let rDiff := rScratch + d + 4
  let rZero := rScratch + d + 5
  let loadAndRes : Stmt :=
    .seq (loadRow d rA rB pCur)
      (.seq (dotRegs d rDot rA rX rProd)
        (.prim (.sub rRes rB rDot)))
  .seq (.prim (.pcopy pCur pTabStart))
    (.seq (.seq loadAndRes (copyReg rOut rRes rZero))
      (.whilePtrLt pCur pTabEnd
        (.seq loadAndRes (maxIntoReg rOut rRes rDiff rZero))))

theorem evalRowInfeasStmt_spec {rMin pMin m d : ℕ} {memBound : ℤ}
    (hm : 0 < m)
    {rOut pTabStart pTabEnd rX rScratch pCur : ℕ}
    {A : Fin m → Fin d → ℝ} {b : Fin m → ℝ} {x : Fin d → ℝ} {s : MState}
    (hTab : RowTableAt s.mem (s.ptrs pTabStart) A b)
    (hEnd : s.ptrs pTabEnd = s.ptrs pTabStart + (m : ℤ) * ((d : ℤ) + 1))
    (hx : VecRegs s rX x)
    (hOut : rMin ≤ rOut) (hScr : rMin ≤ rScratch) (hpCur : pMin ≤ pCur)
    (_hCurNeS : pCur ≠ pTabStart) (hCurNeE : pCur ≠ pTabEnd)
    (_hOutDisjX : rOut < rX ∨ rX + d ≤ rOut)
    (hOutDisjScr : rOut < rScratch ∨ rScratch + d + 6 ≤ rOut)
    (hXDisjScr : rX + d ≤ rScratch ∨ rScratch + d + 6 ≤ rX) :
    ∃ s', SpecRun rMin pMin memBound
        (evalRowInfeasStmt d rOut pTabStart pTabEnd rX rScratch pCur) s s'
        ((4 * d + 12) * m + 10) ∧
      s'.regs rOut = rInfeas hm A b x ∧
      (∀ i, i ≠ rOut → (i < rScratch ∨ rScratch + d + 6 ≤ i) → s'.regs i = s.regs i) ∧
      (∀ q, q ≠ pCur → s'.ptrs q = s.ptrs q) ∧
      s'.mem = s.mem := by
  set rA := rScratch
  set rB := rScratch + d
  set rDot := rScratch + d + 1
  set rProd := rScratch + d + 2
  set rRes := rScratch + d + 3
  set rDiff := rScratch + d + 4
  set rZero := rScratch + d + 5
  set loadAndRes : Stmt :=
    .seq (loadRow d rA rB pCur)
      (.seq (dotRegs d rDot rA rX rProd)
        (.prim (.sub rRes rB rDot)))
  set base := s.ptrs pTabStart
  have hLoadRes : ∀ (i : Fin m) (st : MState),
      st.mem = s.mem →
      st.ptrs pCur = base + (i.1 : ℤ) * ((d : ℤ) + 1) →
      VecRegs st rX x →
      ∃ st', SpecRun rMin pMin memBound loadAndRes st st' (4 * d + 4) ∧
        st'.regs rRes = b i - A i ⬝ᵥ x ∧
        (∀ r, (r < rScratch ∨ rScratch + d + 4 ≤ r) → st'.regs r = st.regs r) ∧
        st'.ptrs = Function.update st.ptrs pCur (base + ((i.1 : ℤ) + 1) * ((d : ℤ) + 1)) ∧
        st'.mem = s.mem := by
    intro i st hmem hpcur hxst
    obtain ⟨hAi, hbi⟩ := hTab i
    rw [← hmem, ← hpcur] at hAi hbi
    obtain ⟨st₁, q1, hvA1, hb1, hoth1, hptrs1, hmem1⟩ :=
      loadRow_spec d (rA := rA) (rB := rB) hAi hbi hScr (by omega) (by omega) hpCur
        (memBound := memBound)
    have hx1 : VecRegs st₁ rX x :=
      hxst.of_pres fun j hj => hoth1 (rX + j) (by omega) (by omega)
    obtain ⟨st₂, q2, hdot2, hoth2, hptrs2, hmem2⟩ :=
      dotRegs_spec (rMin := rMin) (pMin := pMin) (memBound := memBound) d hvA1 hx1
        (rAcc := rDot) (rProd := rProd)
        (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    have q3 : SpecRun rMin pMin memBound (.prim (.sub rRes rB rDot)) st₂
        ((Prim.sub rRes rB rDot).step st₂) 1 :=
      SpecRun.prim (show rMin ≤ rRes by omega) (by intro _ _ h; cases h)
    set st₃ := (Prim.sub rRes rB rDot).step st₂
    refine ⟨st₃, (q1.seq (q2.seq q3)).mono (by omega), ?_, ?_, ?_, ?_⟩
    · simp only [st₃, Prim.step, Function.update_self]
      rw [hoth2 rB (by omega) (by omega), hb1, hdot2]
    · intro r hr
      simp only [st₃, Prim.step, Function.update_of_ne (show r ≠ rRes by omega)]
      rw [hoth2 r (by omega) (by omega), hoth1 r (by omega) (by omega)]
    · simp only [st₃, Prim.step, hptrs2, hptrs1, hpcur]
      congr 1; ring
    · exact hmem2.trans (hmem1.trans hmem)
  have s0_step : SpecRun rMin pMin memBound (.prim (.pcopy pCur pTabStart)) s
      ((Prim.pcopy pCur pTabStart).step s) 1 :=
    SpecRun.prim hpCur (by intro _ _ h; cases h)
  set s₀ := (Prim.pcopy pCur pTabStart).step s
  obtain ⟨s₁, s1_step, hres1, hoth1, hptrs1, hmem1⟩ :=
    hLoadRes ⟨0, hm⟩ s₀ rfl (by simp [s₀, Prim.step, base]) hx
  obtain ⟨s₂, s2_step, hout2, _, hoth2, hptrs2, hmem2⟩ :=
    copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
      (rDst := rOut) (rSrc := rRes) (rZero := rZero) (s := s₁)
      hOut (by omega) (by omega) (by omega)
  let Inv : ℕ → MState → Prop := fun t st =>
    ∃ htm : t < m,
      st.mem = s.mem ∧
      st.ptrs pCur = base + ((t : ℤ) + 1) * ((d : ℤ) + 1) ∧
      (∀ q, q ≠ pCur → st.ptrs q = s.ptrs q) ∧
      st.regs rOut = prefResMax hm A b x t htm ∧
      (∀ r, r ≠ rOut → (r < rScratch ∨ rScratch + d + 6 ≤ r) → st.regs r = s.regs r)
  have hInv0 : Inv 0 s₂ := by
    refine ⟨hm, hmem2.trans hmem1, ?_, ?_, ?_, ?_⟩
    · rw [hptrs2, hptrs1]; simp
    · intro q hq; rw [hptrs2, hptrs1]; simp [s₀, Prim.step, Function.update_of_ne hq]
    · rw [hout2, hres1]; rfl
    · intro r hrO hrS
      rw [hoth2 r hrO (by omega), hoth1 r (by omega)]; rfl
  have hLoop := SpecRun.forLoop (rMin := rMin) (pMin := pMin) (memBound := memBound)
    (q₁ := pCur) (q₂ := pTabEnd)
    (body := .seq loadAndRes (maxIntoReg rOut rRes rDiff rZero))
    (m - 1) (4 * d + 9) Inv
    (fun t ht st hInv => by
      obtain ⟨htm, hmem, hpcur, hptrs, hout, hregs⟩ := hInv
      have ht1 : t + 1 < m := by omega
      refine ⟨?_, ?_⟩
      · rw [hpcur, hptrs pTabEnd hCurNeE.symm, hEnd]
        have hlt : ((t : ℤ) + 1) * ((d : ℤ) + 1) < (m : ℤ) * ((d : ℤ) + 1) := by
          apply mul_lt_mul_of_pos_right (by omega) (by omega)
        linarith
      · have hxst : VecRegs st rX x :=
          hx.of_pres fun j hj => hregs (rX + j) (by omega) (by omega)
        obtain ⟨st₁, q1, hres, hothL, hptrsL, hmemL⟩ :=
          hLoadRes ⟨t + 1, ht1⟩ st hmem (by simpa [Nat.cast_add] using hpcur) hxst
        obtain ⟨st₂, q2, hmax, hothM, hptrsM, hmemM⟩ :=
          maxIntoReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
            (rAcc := rOut) (rVal := rRes) (rDiff := rDiff) (rZero := rZero) (s := st₁)
            hOut (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        refine ⟨st₂, (q1.seq q2).mono (by omega), ht1, hmemM.trans hmemL, ?_, ?_, ?_, ?_⟩
        · rw [hptrsM, hptrsL, Function.update_self]
        · intro q hq; rw [hptrsM, hptrsL, Function.update_of_ne hq]; exact hptrs q hq
        · rw [hmax, hothL rOut (by omega), hout, hres]; rfl
        · intro r hrO hrS
          rw [hothM r hrO (by omega) (by omega), hothL r (by omega)]
          exact hregs r hrO hrS)
    (fun st hInv => by
      obtain ⟨_, _, hpcur, hptrs, _, _⟩ := hInv
      rw [hpcur, hptrs pTabEnd hCurNeE.symm, hEnd]
      have heq : ((m - 1 : ℕ) : ℤ) + 1 = (m : ℤ) := by omega
      rw [heq])
    (m - 1) le_rfl s₂ (by simpa using hInv0)
  obtain ⟨s₃, s3_step, hInvEnd⟩ := hLoop
  obtain ⟨htmEnd, hmemEnd, _, hptrsEnd, houtEnd, hregsEnd⟩ := hInvEnd
  refine ⟨s₃, (s0_step.seq ((s1_step.seq s2_step).seq s3_step)).mono ?_, ?_, hregsEnd, hptrsEnd, hmemEnd⟩
  · rcases m with _ | m'
    · omega
    · simp only [Nat.add_sub_cancel]
      nlinarith
  · rw [houtEnd, prefResMax_full]

end MegiddoLP.VectorGadgets


