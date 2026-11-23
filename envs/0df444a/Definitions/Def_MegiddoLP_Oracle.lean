-- Prove2me | Definitions.Def_MegiddoLP_Oracle
-- name    : MegiddoLP_Oracle
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-23T06:37:27.471322+00:00
-- url     : https://prove2.me/theorems/27c7b033-2baf-449e-9827-4b62f3dab55d
-- title:
--   The hyperplane comparison oracle for fixed-dimension linear programming
-- statement:
--   Given a smaller-dimensional infeasibility solver satisfying its machine contract, this program implements a comparison oracle for one higher dimension. The specifications track the ordering, the candidate solution, and the instruction bound.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §2 and §5. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_MegiddoLP_MachineFrame
import Definitions.Def_MegiddoLP_Infeasibility
import Definitions.Def_MegiddoLP_VectorGadgets
import Definitions.Def_MegiddoLP_ConstructiveApproachI
import Mathlib.Tactic

/-!
# Parametric Hyperplane Oracle Construction on `SmaleNinth.RAMProgram`

Defines the clean solver interfaces `MinInfeasSolver d` and `OracleSolver D`, and constructs
`buildOracleSolver (sol : MinInfeasSolver d) : OracleSolver (d + 1)` implementing Megiddo's
three-call dimension-reduction hyperplane oracle via compile-time pivot dispatch and
`MegiddoLP.Infeasibility.oracle_hyperplane`.
-/

namespace MegiddoLP.Oracle

open SmaleNinth Matrix LinearOptimization
open MegiddoLP.MachineDSL MegiddoLP.Infeasibility MegiddoLP.VectorGadgets
open MegiddoLP.ConstructiveApproachI

/-! ## Ordering & Option-Ordering Real Encodings -/

/-- Real encoding of `Ordering`: `-1` for `.lt`, `0` for `.eq`, `+1` for `.gt`. -/
def encodeOrd : Ordering → ℝ
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- Real encoding of `Option Ordering`: `0` for `none`, `encodeOrd o + 2 ∈ {1, 2, 3}` for `some o`. -/
def encodeOptOrd : Option Ordering → ℝ
  | none => 0
  | some o => encodeOrd o + 2

@[simp] theorem encodeOrd_swap (o : Ordering) : encodeOrd o.swap = -encodeOrd o := by
  cases o <;> simp [encodeOrd, Ordering.swap]

theorem encodeOrd_scaleOrd (p : ℝ) (o : Ordering) :
    encodeOrd (scaleOrd p o) = if 0 < p then encodeOrd o else -encodeOrd o := by
  unfold scaleOrd
  split_ifs <;> simp

theorem encodeOptOrd_pos_iff (u : Option Ordering) :
    0 < encodeOptOrd u ↔ u.isSome := by
  cases u with
  | none => simp [encodeOptOrd]
  | some o => cases o <;> norm_num [encodeOptOrd, encodeOrd]

theorem encodeOptOrd_le_zero_iff (u : Option Ordering) :
    encodeOptOrd u ≤ 0 ↔ u = none := by
  rcases u with _ | (_ | _ | _)
  · simp [encodeOptOrd]
  · simp [encodeOptOrd, encodeOrd]
  · simp [encodeOptOrd, encodeOrd]
  · simp [encodeOptOrd, encodeOrd]; norm_num

/-! ## Solver Interfaces -/

/-- A linear-time `MinInfeas` solver in fixed dimension `d`:
computes a global minimizer `xStar : Fin d → ℝ` of `rInfeas hm A b` (where Row `0 = (0, 0)`)
into `rOut .. rOut + d - 1` within `C * (m + 1)` instructions, preserving all registers `< rOut`,
all pointers `< pBase`, and all memory `< s.ptrs pArena`. -/
structure MinInfeasSolver (d : ℕ) where
  C : ℕ
  mkStmt : (rOut pTabStart pTabEnd pArena pBase : ℕ) → Stmt
  spec : ∀ {m : ℕ} (hm : 0 < m)
    {rOut pTabStart pTabEnd pArena pBase : ℕ}
    {A : Fin m → Fin d → ℝ} {b : Fin m → ℝ} {s : MState},
    RowTableAt s.mem (s.ptrs pTabStart) A b →
    A ⟨0, hm⟩ = 0 → b ⟨0, hm⟩ = 0 →
    s.ptrs pTabEnd = s.ptrs pTabStart + (m : ℤ) * ((d : ℤ) + 1) →
    s.ptrs pTabStart + (m : ℤ) * ((d : ℤ) + 1) ≤ s.ptrs pArena →
    pTabStart < pBase → pTabEnd < pBase → pArena < pBase →
    ∃ (s' : MState) (xStar : Fin d → ℝ),
      SpecRun rOut pBase (s.ptrs pArena)
        (mkStmt rOut pTabStart pTabEnd pArena pBase) s s' (C * (m + 1)) ∧
      VecRegs s' rOut xStar ∧
      (∀ w : Fin d → ℝ, rInfeas hm A b xStar ≤ rInfeas hm A b w)

/-- Base `d = 0` solver: `Fin 0 → ℝ` has a unique point `0`, so `.skip` solves in `1 * (m + 1)` steps. -/
def minInfeasSolverZero : MinInfeasSolver 0 where
  C := 1
  mkStmt := fun _ _ _ _ _ => .skip
  spec := by
    intro m hm rOut _ _ pArena pBase A b s _ _ _ _ _ _ _ _
    refine ⟨s, 0, (SpecRun.skip rOut pBase (s.ptrs pArena) s).mono (by omega),
      fun j => Fin.elim0 j, fun w => ?_⟩
    have heq : w = 0 := Subsingleton.elim w 0
    rw [heq]

/-- A linear-time hyperplane oracle in dimension `D`:
given `(A, b)` at `[pTabStart .. pTabEnd)` (`Row 0 = (0, 0)`) and nonzero hyperplane `(h, β)`
in `rH .. rH + D - 1` and `rBeta` (`rH + D ≤ rOut`, `rBeta < rOut`), writes:
- `x' : Fin D → ℝ` in `rOut .. rOut + D - 1`
- `v' = rInfeas hm A b x'` in `rOut + D`
- `encodeOrd σ` (`σ ∈ {.lt, .gt}`) in `rOut + D + 1`, valid on `{w | rInfeas w < v'}`. -/
structure OracleSolver (D : ℕ) where
  C : ℕ
  mkStmt : (rOut rH rBeta pTabStart pTabEnd pArena pBase : ℕ) → Stmt
  spec : ∀ {m : ℕ} (hm : 0 < m)
    {rOut rH rBeta pTabStart pTabEnd pArena pBase : ℕ}
    {A : Fin m → Fin D → ℝ} {b : Fin m → ℝ}
    {h : Fin D → ℝ} {β : ℝ} {s : MState},
    RowTableAt s.mem (s.ptrs pTabStart) A b →
    A ⟨0, hm⟩ = 0 → b ⟨0, hm⟩ = 0 →
    s.ptrs pTabEnd = s.ptrs pTabStart + (m : ℤ) * ((D : ℤ) + 1) →
    s.ptrs pTabStart + (m : ℤ) * ((D : ℤ) + 1) ≤ s.ptrs pArena →
    VecRegs s rH h → s.regs rBeta = β → h ≠ 0 →
    rH + D ≤ rOut → rBeta < rOut →
    pTabStart < pBase → pTabEnd < pBase → pArena < pBase →
    ∃ (s' : MState) (x' : Fin D → ℝ) (σ : Ordering),
      SpecRun rOut pBase (s.ptrs pArena)
        (mkStmt rOut rH rBeta pTabStart pTabEnd pArena pBase) s s' (C * (m + 1)) ∧
      VecRegs s' rOut x' ∧
      s'.regs (rOut + D) = rInfeas hm A b x' ∧
      s'.regs (rOut + D + 1) = encodeOrd σ ∧
      (∀ w : Fin D → ℝ, rInfeas hm A b w < rInfeas hm A b x' → compare (h ⬝ᵥ w) β = σ)

/-! ## Unrolled Coordinate-Slice Register Gadgets for Fixed Pivot `p : Fin (d + 1)` -/

/-- Unrolled computation of `Fin.init (transRowA h p ai)` (`k ≤ d` prefix) into `rDst .. rDst + d - 1`
given `rRatio = ai p / h p`. -/
def sliceRowAAux (d : ℕ) (p : Fin (d + 1)) (rDst rAi rH rRatio rTmp : ℕ) :
    (k : ℕ) → k ≤ d → Stmt
  | 0, _ => .skip
  | k + 1, hk =>
    let idx := (p.succAbove ⟨k, hk⟩).1
    .seq (sliceRowAAux d p rDst rAi rH rRatio rTmp k (Nat.le_of_succ_le hk))
      (.seq (.prim (.mul rTmp rRatio (rH + idx)))
        (.prim (.sub (rDst + k) (rAi + idx) rTmp)))

theorem sliceRowAAux_spec {rMin pMin d : ℕ} {memBound : ℤ} (p : Fin (d + 1))
    {rDst rAi rH rRatio rTmp : ℕ} {ai h : Fin (d + 1) → ℝ} {s : MState}
    (hai : VecRegs s rAi ai) (hh : VecRegs s rH h)
    (hDst : rMin ≤ rDst) (hTmp : rMin ≤ rTmp)
    (hDisj1 : rDst + d ≤ rAi ∨ rAi + (d + 1) ≤ rDst)
    (hDisj2 : rDst + d ≤ rH ∨ rH + (d + 1) ≤ rDst)
    (hDisj3 : rRatio < rDst ∨ rDst + d ≤ rRatio)
    (hDisj4 : rTmp < rDst ∨ rDst + d ≤ rTmp)
    (hTmpAi : rTmp < rAi ∨ rAi + (d + 1) ≤ rTmp)
    (hTmpH : rTmp < rH ∨ rH + (d + 1) ≤ rTmp)
    (hTmpR : rTmp ≠ rRatio) :
    ∀ (k : ℕ) (hk : k ≤ d),
      ∃ s', SpecRun rMin pMin memBound (sliceRowAAux d p rDst rAi rH rRatio rTmp k hk) s s' (2 * k) ∧
        (∀ j (hj : j < k), s'.regs (rDst + j) =
          ai (p.succAbove ⟨j, lt_of_lt_of_le hj hk⟩) - s.regs rRatio * h (p.succAbove ⟨j, lt_of_lt_of_le hj hk⟩)) ∧
        (∀ i, (i < rDst ∨ rDst + k ≤ i) → i ≠ rTmp → s'.regs i = s.regs i) ∧
        s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨s, SpecRun.skip rMin pMin memBound s, fun _ hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ => rfl, rfl, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨s₁, p1, hv1, hoth1, hp1, hm1⟩ := ih (Nat.le_of_succ_le hk)
    set idx := (p.succAbove ⟨k, hk⟩).1
    have hidx_lt : idx < d + 1 := (p.succAbove ⟨k, hk⟩).2
    have q1 : SpecRun rMin pMin memBound (.prim (.mul rTmp rRatio (rH + idx))) s₁ _ 1 :=
      SpecRun.prim hTmp (by intro _ _ h; cases h)
    set s₂ := (Prim.mul rTmp rRatio (rH + idx)).step s₁
    have q2 : SpecRun rMin pMin memBound (.prim (.sub (rDst + k) (rAi + idx) rTmp)) s₂ _ 1 :=
      SpecRun.prim (show rMin ≤ rDst + k by omega) (by intro _ _ h; cases h)
    set s₃ := (Prim.sub (rDst + k) (rAi + idx) rTmp).step s₂
    refine ⟨s₃, (p1.seq (q1.seq q2)).mono (by omega), ?_, ?_, hp1, hm1⟩
    · intro j hj
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
      · simp only [s₃, s₂, Prim.step, Function.update_of_ne (show rDst + j ≠ rDst + k by omega),
          Function.update_of_ne (show rDst + j ≠ rTmp by omega)]
        exact hv1 j hlt
      · simp only [s₃, s₂, Prim.step, Function.update_self,
          Function.update_of_ne (show rAi + idx ≠ rTmp by omega)]
        rw [hoth1 (rAi + idx) (by omega) (by omega), hoth1 rRatio (by omega) hTmpR.symm,
            hoth1 (rH + idx) (by omega) (by omega), hai (p.succAbove ⟨j, hk⟩), hh (p.succAbove ⟨j, hk⟩)]
    · intro i hi hiT
      simp only [s₃, s₂, Prim.step, Function.update_of_ne (show i ≠ rDst + k by omega),
        Function.update_of_ne hiT]
      exact hoth1 i (by omega) hiT

/-- Unrolled projection `rDst + j := rSrc + (p.succAbove j)` for `j < k ≤ d`. -/
noncomputable def projSuccAboveAux (d : ℕ) (p : Fin (d + 1)) (rDst rSrc rZero : ℕ) :
    (k : ℕ) → k ≤ d → Stmt
  | 0, _ => .skip
  | k + 1, hk =>
    let idx := (p.succAbove ⟨k, hk⟩).1
    .seq (projSuccAboveAux d p rDst rSrc rZero k (Nat.le_of_succ_le hk))
      (copyReg (rDst + k) (rSrc + idx) rZero)

theorem projSuccAboveAux_spec {rMin pMin d : ℕ} {memBound : ℤ} (p : Fin (d + 1))
    {rDst rSrc rZero : ℕ} {v : Fin (d + 1) → ℝ} {s : MState}
    (hv : VecRegs s rSrc v)
    (hDst : rMin ≤ rDst) (hZero : rMin ≤ rZero)
    (hDisj : rDst + d ≤ rSrc ∨ rSrc + (d + 1) ≤ rDst)
    (hZS : rZero < rSrc ∨ rSrc + (d + 1) ≤ rZero)
    (hZD : rZero < rDst ∨ rDst + d ≤ rZero) :
    ∀ (k : ℕ) (hk : k ≤ d),
      ∃ s', SpecRun rMin pMin memBound (projSuccAboveAux d p rDst rSrc rZero k hk) s s' (2 * k) ∧
        (∀ j (hj : j < k), s'.regs (rDst + j) = v (p.succAbove ⟨j, lt_of_lt_of_le hj hk⟩)) ∧
        (∀ i, (i < rDst ∨ rDst + k ≤ i) → i ≠ rZero → s'.regs i = s.regs i) ∧
        s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨s, SpecRun.skip rMin pMin memBound s, fun _ hj => absurd hj (Nat.not_lt_zero _),
      fun _ _ _ => rfl, rfl, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨s₁, p1, hv1, hoth1, hp1, hm1⟩ := ih (Nat.le_of_succ_le hk)
    set idx := (p.succAbove ⟨k, hk⟩).1
    have hidx_lt : idx < d + 1 := (p.succAbove ⟨k, hk⟩).2
    obtain ⟨s₂, p2, hd2, _, hoth2, hp2, hm2⟩ :=
      copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
        (rDst := rDst + k) (rSrc := rSrc + idx) (rZero := rZero) (s := s₁)
        (by omega) hZero (by omega) (by omega)
    refine ⟨s₂, (p1.seq p2).mono (by omega), ?_, ?_, hp2.trans hp1, hm2.trans hm1⟩
    · intro j hj
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
      · rw [hoth2 (rDst + j) (by omega) (by omega)]; exact hv1 j hlt
      · rw [hd2, hoth1 (rSrc + idx) (by omega) (by omega), hv (p.succAbove ⟨j, hk⟩)]
    · intro i hi hiZ
      rw [hoth2 i (by omega) hiZ, hoth1 i (by omega) hiZ]

/-- Unrolled scatter `rDst + (p.succAbove j) := rY + j` for `j < k ≤ d`, followed by `rDst + p := rXP`. -/
noncomputable def scatterInsertAux (d : ℕ) (p : Fin (d + 1)) (rDst rY rZero : ℕ) :
    (k : ℕ) → k ≤ d → Stmt
  | 0, _ => .skip
  | k + 1, hk =>
    let idx := (p.succAbove ⟨k, hk⟩).1
    .seq (scatterInsertAux d p rDst rY rZero k (Nat.le_of_succ_le hk))
      (copyReg (rDst + idx) (rY + k) rZero)

noncomputable def scatterInsertStmt (d : ℕ) (p : Fin (d + 1)) (rDst rY rXP rZero : ℕ) : Stmt :=
  .seq (scatterInsertAux d p rDst rY rZero d le_rfl)
    (copyReg (rDst + p.1) rXP rZero)

theorem scatterInsertStmt_spec {rMin pMin d : ℕ} {memBound : ℤ} (p : Fin (d + 1))
    {rDst rY rXP rZero : ℕ} {y : Fin d → ℝ} {s : MState}
    (hy : VecRegs s rY y)
    (hDst : rMin ≤ rDst) (hZero : rMin ≤ rZero)
    (hDisjDY : rDst + (d + 1) ≤ rY ∨ rY + d ≤ rDst)
    (hXPD : rXP < rDst ∨ rDst + (d + 1) ≤ rXP)
    (hZD : rZero < rDst ∨ rDst + (d + 1) ≤ rZero)
    (hZY : rZero < rY ∨ rY + d ≤ rZero)
    (hZXP : rXP ≠ rZero) :
    ∃ s', SpecRun rMin pMin memBound (scatterInsertStmt d p rDst rY rXP rZero) s s' (2 * d + 2) ∧
      VecRegs s' rDst (p.insertNth (s.regs rXP) y) ∧
      (∀ i, (i < rDst ∨ rDst + (d + 1) ≤ i) → i ≠ rZero → s'.regs i = s.regs i) ∧
      s'.ptrs = s.ptrs ∧ s'.mem = s.mem := by
  have hAux : ∀ (k : ℕ) (hk : k ≤ d),
      ∃ s₁, SpecRun rMin pMin memBound (scatterInsertAux d p rDst rY rZero k hk) s s₁ (2 * k) ∧
        (∀ j (hj : j < k), s₁.regs (rDst + (p.succAbove ⟨j, lt_of_lt_of_le hj hk⟩).1) =
          y ⟨j, lt_of_lt_of_le hj hk⟩) ∧
        (∀ i, (i < rDst ∨ rDst + (d + 1) ≤ i) → i ≠ rZero → s₁.regs i = s.regs i) ∧
        s₁.ptrs = s.ptrs ∧ s₁.mem = s.mem := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨s, SpecRun.skip rMin pMin memBound s, fun _ hj => absurd hj (Nat.not_lt_zero _),
        fun _ _ _ => rfl, rfl, rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨s₁, p1, hv1, hoth1, hp1, hm1⟩ := ih (Nat.le_of_succ_le hk)
      set idx := (p.succAbove ⟨k, hk⟩).1
      have hidx_lt : idx < d + 1 := (p.succAbove ⟨k, hk⟩).2
      obtain ⟨s₂, p2, hd2, _, hoth2, hp2, hm2⟩ :=
        copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
          (rDst := rDst + idx) (rSrc := rY + k) (rZero := rZero) (s := s₁)
          (by omega) hZero (by omega) (by omega)
      refine ⟨s₂, (p1.seq p2).mono (by omega), ?_, ?_, hp2.trans hp1, hm2.trans hm1⟩
      · intro j hj
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
        · have hne_fin : p.succAbove ⟨j, lt_of_lt_of_le hlt (Nat.le_of_succ_le hk)⟩ ≠ p.succAbove ⟨k, hk⟩ := by
            intro heq
            have := Fin.succAbove_right_injective heq
            simp [Fin.ext_iff] at this; omega
          have hne_val : (p.succAbove ⟨j, lt_of_lt_of_le hlt (Nat.le_of_succ_le hk)⟩).1 ≠ idx :=
            fun hv => hne_fin (Fin.ext hv)
          rw [hoth2 (rDst + _) (by omega) (by omega)]
          exact hv1 j hlt
        · rw [hd2, hoth1 (rY + j) (by omega) (by omega), hy ⟨j, hk⟩]
      · intro i hi hiZ
        rw [hoth2 i (by omega) hiZ, hoth1 i hi hiZ]
  obtain ⟨s₁, p1, hv1, hoth1, hp1, hm1⟩ := hAux d le_rfl
  obtain ⟨s₂, p2, hd2, _, hoth2, hp2, hm2⟩ :=
    copyReg_spec (rMin := rMin) (pMin := pMin) (memBound := memBound)
      (rDst := rDst + p.1) (rSrc := rXP) (rZero := rZero) (s := s₁)
      (by have := p.2; omega) hZero hZXP (by have := p.2; omega)
  refine ⟨s₂, (p1.seq p2).mono (by omega), ?_, ?_, hp2.trans hp1, hm2.trans hm1⟩
  · intro idx
    by_cases hidx : idx = p
    · subst hidx
      rw [Fin.insertNth_apply_same, hd2, hoth1 rXP hXPD hZXP]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hidx
      rw [Fin.insertNth_apply_succAbove]
      have hne_p : (p.succAbove j).1 ≠ p.1 := fun hv => Fin.succAbove_ne p j (Fin.ext hv)
      rw [hoth2 (rDst + (p.succAbove j).1) (by omega) (by have := (p.succAbove j).2; omega)]
      exact hv1 j.1 j.2
  · intro i hi hiZ
    have := p.2
    rw [hoth2 i (by omega) hiZ, hoth1 i hi hiZ]

/-! ## Oracle Implementation for Fixed Pivot `p : Fin (d + 1)` -/

/-- Test feasibility of tight-row directional `d`-system (`negLast = true` for `sys1`,
`false` for `sys2`) using `sol : MinInfeasSolver d` + `evalRowInfeasStmt d`, placing `vDir`
(`≤ 0 ↔ feasible`) into `rVDir`. -/
noncomputable def checkTightDirStmt {d : ℕ} (sol : MinInfeasSolver d) (p : Fin (d + 1)) (negLast : Bool)
    (rVDir rXPrime rVPrime rH pTabStart pTabEnd pArena rWork pWork : ℕ) : Stmt :=
  let rAi := rWork                         -- d + 1 regs
  let rBi := rWork + (d + 1)
  let rDot := rWork + (d + 2)
  let rProd := rWork + (d + 3)
  let rRes := rWork + (d + 4)
  let rGap := rWork + (d + 5)
  let rRatio := rWork + (d + 6)
  let rRhs := rWork + (d + 7)
  let rZero := rWork + (d + 8)
  let rSliceA := rWork + (d + 9)           -- d regs
  let rSubOut := rWork + 2 * d + 9         -- d regs for sol output yDir
  let rEvalScr := rWork + 3 * d + 9        -- d + 6 regs for evalRowInfeasStmt
  let pRead := pWork
  let pWrite := pWork + 1
  let pEval := pWork + 2
  let pSubBase := pWork + 3
  let rhsStmt : Stmt :=
    if negLast then
      .seq (.prim (.const rZero 0)) (.prim (.sub rRhs rZero rRatio))
    else
      copyReg rRhs rRatio rZero
  let writeRow0 : Stmt :=
    Stmt.block [
      .prim (.pcopy pWrite pArena),
      zeroRegs d rSliceA,
      .prim (.const rRhs 0),
      storeRow d pWrite rSliceA rRhs]
  let filterTightLoop : Stmt :=
    .seq (.prim (.pcopy pRead pTabStart))
      (.whilePtrLt pRead pTabEnd
        (.seq (loadRow (d + 1) rAi rBi pRead)
          (.seq (dotRegs (d + 1) rDot rAi rXPrime rProd)
            (.seq (.prim (.sub rRes rBi rDot))
              (.seq (.prim (.sub rGap rVPrime rRes))
                (.ifLeZero rGap
                  (Stmt.block [
                    .prim (.div rRatio (rAi + p.1) (rH + p.1)),
                    sliceRowAAux d p rSliceA rAi rH rRatio rProd d le_rfl,
                    rhsStmt,
                    storeRow d pWrite rSliceA rRhs])
                  .skip))))))
  Stmt.block [
    writeRow0,
    filterTightLoop,
    sol.mkStmt rSubOut pArena pWrite pWrite pSubBase,
    evalRowInfeasStmt d rVDir pArena pWrite rSubOut rEvalScr pEval]

set_option maxHeartbeats 400000 in
theorem checkTightDirStmt_spec {m d : ℕ} (sol : MinInfeasSolver d) (p : Fin (d + 1))
    (negLast : Bool) (hm : 0 < m)
    {rVDir rXPrime rVPrime rH pTabStart pTabEnd pArena rWork pWork : ℕ}
    {A : Fin m → Fin (d + 1) → ℝ} {b : Fin m → ℝ}
    {h x' : Fin (d + 1) → ℝ} {s : MState}
    (hTab : RowTableAt s.mem (s.ptrs pTabStart) A b)
    (hEnd : s.ptrs pTabEnd = s.ptrs pTabStart + (m : ℤ) * ((d : ℤ) + 2))
    (hTabAr : s.ptrs pTabStart + (m : ℤ) * ((d : ℤ) + 2) ≤ s.ptrs pArena)
    (hh : VecRegs s rH h) (_hp : h p ≠ 0)
    (hx' : VecRegs s rXPrime x') (hv' : s.regs rVPrime = rInfeas hm A b x')
    (hH_X : rH + (d + 1) ≤ rXPrime)
    (hX_VP : rXPrime + (d + 1) ≤ rVPrime)
    (hVP_VD : rVPrime < rVDir)
    (hVD_W : rVDir < rWork)
    (hpTS : pTabStart < pWork) (hpTE : pTabEnd < pWork) (hpAr : pArena < pWork) :
    ∃ s', SpecRun rVDir pWork (s.ptrs pArena)
        (checkTightDirStmt sol p negLast rVDir rXPrime rVPrime rH pTabStart pTabEnd pArena rWork pWork)
        s s' ((sol.C + 16 * d + 40) * (m + 2)) ∧
      (decide (s'.regs rVDir ≤ 0) = true ↔
        ∃ y' : Fin d → ℝ, ∀ i : Fin m,
          rInfeas hm A b x' = b i - A i ⬝ᵥ x' →
          (if negLast then -(transRowA h p (A i) (Fin.last d))
           else transRowA h p (A i) (Fin.last d)) ≤ Fin.init (transRowA h p (A i)) ⬝ᵥ y') := by
  set arena := s.ptrs pArena
  set v' := rInfeas hm A b x'
  let rAi := rWork
  let rBi := rWork + (d + 1)
  let rDot := rWork + (d + 2)
  let rProd := rWork + (d + 3)
  let rRes := rWork + (d + 4)
  let rGap := rWork + (d + 5)
  let rRatio := rWork + (d + 6)
  let rRhs := rWork + (d + 7)
  let rZero := rWork + (d + 8)
  let rSliceA := rWork + (d + 9)
  let rSubOut := rWork + 2 * d + 9
  let rEvalScr := rWork + 3 * d + 9
  let pRead := pWork
  let pWrite := pWork + 1
  let pEval := pWork + 2
  let pSubBase := pWork + 3
  -- Phase 1: writeRow0 at `[arena .. arena + (d + 1))`
  have w0_1 : SpecRun rVDir pWork arena (.prim (.pcopy pWrite pArena)) s _ 1 :=
    SpecRun.prim (show pWork ≤ pWrite by omega) (by intro _ _ e; cases e)
  set sw₁ := (Prim.pcopy pWrite pArena).step s
  obtain ⟨sw₂, w0_2, hvZ, hothZ, hpZ, hmZ⟩ :=
    zeroRegs_spec (rMin := rVDir) (pMin := pWork) (memBound := arena) d (rDst := rSliceA) (by omega) sw₁
  have w0_3 : SpecRun rVDir pWork arena (.prim (.const rRhs 0)) sw₂ _ 1 :=
    SpecRun.prim (show rVDir ≤ rRhs by omega) (by intro _ _ e; cases e)
  set sw₃ := (Prim.const rRhs 0).step sw₂
  have hvZ3 : VecRegs sw₃ rSliceA (0 : Fin d → ℝ) :=
    hvZ.of_pres fun j hj => Function.update_of_ne (by omega) _ _
  obtain ⟨sw₄, w0_4, hRow0A, hRow0B, hregsW4, hpW4, hmW4⟩ :=
    storeRow_spec (rMin := rVDir) (pMin := pWork) (memBound := arena) d
      (q := pWrite) (rA := rSliceA) (rB := rRhs) (β := 0) hvZ3 (by simp [sw₃, Prim.step])
      (by omega) (by simp [sw₃, Prim.step, hpZ, sw₁, arena])
  have hWrite0 : SpecRun rVDir pWork arena _ s sw₄ (3 * d + 4) :=
    (w0_1.seq (w0_2.seq (w0_3.seq w0_4))).mono (by omega)
  have hpW4_val : sw₄.ptrs pWrite = arena + ((d : ℤ) + 1) := by
    rw [hpW4]; simp [sw₃, Prim.step, hpZ, sw₁, arena]
  -- Define filtered list of tight row indices in `0 .. t - 1`
  let isTight (i : Fin m) : Bool := decide (v' - (b i - A i ⬝ᵥ x') ≤ 0)
  have isTight_iff : ∀ i : Fin m, isTight i = true ↔ v' = b i - A i ⬝ᵥ x' := by
    intro i
    simp only [isTight, decide_eq_true_eq]
    have hle := le_rInfeas hm A b x' i
    change b i - A i ⬝ᵥ x' ≤ v' at hle
    constructor <;> intro h <;> linarith
  let rowVec (i : Fin m) : Fin d → ℝ := Fin.init (transRowA h p (A i))
  let rowRhs (i : Fin m) : ℝ :=
    if negLast then -(transRowA h p (A i) (Fin.last d)) else transRowA h p (A i) (Fin.last d)
  have rowRhs_eq : ∀ i : Fin m, rowRhs i =
      if negLast then -(A i p / h p) else A i p / h p := by
    intro i; simp [rowRhs, transRowA]
  -- Phase 2: filterTightLoop (`m` iterations)
  have f0 : SpecRun rVDir pWork arena (.prim (.pcopy pRead pTabStart)) sw₄ _ 1 :=
    SpecRun.prim le_rfl (by intro _ _ e; cases e)
  set sf₀ := (Prim.pcopy pRead pTabStart).step sw₄
  let rhsStmt : Stmt :=
    if negLast then .seq (.prim (.const rZero 0)) (.prim (.sub rRhs rZero rRatio))
    else copyReg rRhs rRatio rZero
  let loopBody : Stmt :=
    .seq (loadRow (d + 1) rAi rBi pRead)
      (.seq (dotRegs (d + 1) rDot rAi rXPrime rProd)
        (.seq (.prim (.sub rRes rBi rDot))
          (.seq (.prim (.sub rGap rVPrime rRes))
            (.ifLeZero rGap
              (Stmt.block [
                .prim (.div rRatio (rAi + p.1) (rH + p.1)),
                sliceRowAAux d p rSliceA rAi rH rRatio rProd d le_rfl,
                rhsStmt,
                storeRow d pWrite rSliceA rRhs])
              .skip))))
  let tightPref (t : ℕ) : List (Fin m) :=
    ((List.finRange m).take t).filter isTight
  let InvF : ℕ → MState → Prop := fun t st =>
    MemPreservedBelow arena s.mem st.mem ∧
    VecAt st.mem arena (0 : Fin d → ℝ) ∧
    st.mem (arena + (d : ℤ)) = 0 ∧
    (∀ k (hk : k < (tightPref t).length),
      VecAt st.mem (arena + ((k : ℤ) + 1) * ((d : ℤ) + 1)) (rowVec (tightPref t)[k]) ∧
      st.mem (arena + ((k : ℤ) + 1) * ((d : ℤ) + 1) + (d : ℤ)) = rowRhs (tightPref t)[k]) ∧
    st.ptrs pRead = s.ptrs pTabStart + (t : ℤ) * ((d : ℤ) + 2) ∧
    st.ptrs pWrite = arena + (((tightPref t).length : ℤ) + 1) * ((d : ℤ) + 1) ∧
    (∀ q < pWork, st.ptrs q = s.ptrs q) ∧
    (∀ r < rWork, st.regs r = s.regs r)
  have hInvF0 : InvF 0 sf₀ := by
    have hpW0 : sw₃.ptrs pWrite = arena := by simp [sw₃, Prim.step, hpZ, sw₁, arena]
    refine ⟨hWrite0.mem_pres, by simpa [sf₀, Prim.step, hpW0] using hRow0A,
      by simpa [sf₀, Prim.step, hpW0] using hRow0B,
      fun k hk => by simp [tightPref] at hk,
      by simp [sf₀, Prim.step, hWrite0.ptrs_pres pTabStart hpTS],
      by simp [sf₀, Prim.step, Function.update_of_ne (show pWrite ≠ pRead by omega), hpW4_val, tightPref],
      fun q hq => by
        simp only [sf₀, Prim.step]
        rw [Function.update_of_ne (by omega)]
        exact hWrite0.ptrs_pres q hq,
      fun r hr => by
        simp only [sf₀, Prim.step]
        rw [hregsW4]
        simp only [sw₃, Prim.step]
        rw [Function.update_of_ne (by omega), hothZ r (by omega)]
        rfl⟩
  have hLoopF := SpecRun.forLoop (rMin := rVDir) (pMin := pWork) (memBound := arena)
    (q₁ := pRead) (q₂ := pTabEnd) (body := loopBody) m (8 * d + 20) InvF
    (fun t ht st hInv => by
      obtain ⟨hmPres, h0A, h0B, hRows, hpR, hpW, hpo, hro⟩ := hInv
      let i_t : Fin m := ⟨t, ht⟩
      have htake_t : (List.finRange m).take (t + 1) = (List.finRange m).take t ++ [i_t] := by
        have hlen : t < (List.finRange m).length := by simp [ht]
        rw [List.take_succ_eq_append_getElem hlen]; simp [i_t]
      refine ⟨by rw [hpR, hpo pTabEnd hpTE, hEnd]
                 have : (t : ℤ) * ((d : ℤ) + 2) < (m : ℤ) * ((d : ℤ) + 2) :=
                   mul_lt_mul_of_pos_right (by omega) (by omega)
                 linarith, ?_⟩
      -- Load row `i_t` from `pRead` (`< arena`, preserved by `hmPres`)
      have hTab_st : RowTableAt st.mem (s.ptrs pTabStart) A b :=
        hTab.of_mem_pres hmPres (by simpa [add_assoc] using hTabAr)
      obtain ⟨hAi_m, hbi_m⟩ := hTab_st i_t
      have hpR_eq : st.ptrs pRead = s.ptrs pTabStart + (i_t.1 : ℤ) * (((d + 1 : ℕ) : ℤ) + 1) := by
        simpa [i_t, Nat.cast_add, add_assoc] using hpR
      rw [← hpR_eq] at hAi_m hbi_m
      obtain ⟨st₁, b1, hvAi1, hbi1, hoth1, hp1, hm1⟩ :=
        loadRow_spec (rMin := rWork) (pMin := pWork) (memBound := arena) (d + 1)
          (rA := rAi) (rB := rBi) (q := pRead) hAi_m hbi_m le_rfl (by omega) (by omega) le_rfl
      have hx_st1 : VecRegs st₁ rXPrime x' :=
        hx'.of_pres fun j hj => (hoth1 (rXPrime + j) (by omega) (by omega)).trans (hro (rXPrime + j) (by omega))
      obtain ⟨st₂, b2, hdot2, hoth2, hp2, hm2⟩ :=
        dotRegs_spec (rMin := rWork) (pMin := pWork) (memBound := arena) (d + 1)
          hvAi1 hx_st1 (rAcc := rDot) (rProd := rProd)
          (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      have b3 : SpecRun rWork pWork arena (.prim (.sub rRes rBi rDot)) st₂ _ 1 :=
        SpecRun.prim (show rWork ≤ rRes by omega) (by intro _ _ e; cases e)
      set st₃ := (Prim.sub rRes rBi rDot).step st₂
      have b4 : SpecRun rWork pWork arena (.prim (.sub rGap rVPrime rRes)) st₃ _ 1 :=
        SpecRun.prim (show rWork ≤ rGap by omega) (by intro _ _ e; cases e)
      set st₄ := (Prim.sub rGap rVPrime rRes).step st₃
      have hgap4 : st₄.regs rGap = v' - (b i_t - A i_t ⬝ᵥ x') := by
        simp only [st₄, st₃, Prim.step, Function.update_self,
          Function.update_of_ne (show rVPrime ≠ rRes by omega)]
        rw [hoth2 rVPrime (by omega) (by omega), hoth1 rVPrime (by omega) (by omega),
            hro rVPrime (by omega), hv', hoth2 rBi (by omega) (by omega), hbi1, hdot2]
      by_cases hT : isTight i_t = true
      · have hle_gap : st₄.regs rGap ≤ 0 := by
          rw [hgap4]; exact of_decide_eq_true hT
        have c1 : SpecRun rWork pWork arena (.prim (.div rRatio (rAi + p.1) (rH + p.1))) st₄ _ 1 :=
          SpecRun.prim (show rWork ≤ rRatio by omega) (by intro _ _ e; cases e)
        set st₅ := (Prim.div rRatio (rAi + p.1) (rH + p.1)).step st₄
        have hvAi5 : VecRegs st₅ rAi (A i_t) :=
          hvAi1.of_pres fun j hj => by
            simp only [st₅, st₄, st₃, Prim.step]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
            exact hoth2 (rAi + j) (by omega) (by omega)
        have hh5 : VecRegs st₅ rH h :=
          hh.of_pres fun j hj => by
            simp only [st₅, st₄, st₃, Prim.step]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), hoth2 (rH + j) (by omega) (by omega),
                hoth1 (rH + j) (by omega) (by omega)]
            exact hro (rH + j) (by omega)
        have hrat5 : st₅.regs rRatio = A i_t p / h p := by
          have hp_lt := p.2
          simp only [st₅, st₄, st₃, Prim.step, Function.update_self,
            Function.update_of_ne (show rAi + p.1 ≠ rGap by omega),
            Function.update_of_ne (show rAi + p.1 ≠ rRes by omega),
            Function.update_of_ne (show rH + p.1 ≠ rGap by omega),
            Function.update_of_ne (show rH + p.1 ≠ rRes by omega)]
          rw [hoth2 (rAi + p.1) (by omega) (by omega), hvAi1 p,
              hoth2 (rH + p.1) (by omega) (by omega), hoth1 (rH + p.1) (by omega) (by omega),
              hro (rH + p.1) (by omega), hh p]
        obtain ⟨st₆, c2, hslice6, hoth6, hp6, hm6⟩ :=
          sliceRowAAux_spec (rMin := rWork) (pMin := pWork) (memBound := arena) p
            (rDst := rSliceA) (rAi := rAi) (rH := rH) (rRatio := rRatio) (rTmp := rProd)
            hvAi5 hh5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) d le_rfl
        have hvSlice6 : VecRegs st₆ rSliceA (rowVec i_t) := by
          intro j
          rw [hslice6 j.1 j.2, hrat5]
          simp [rowVec, transRowA]
        -- `rhsStmt`
        have hRhsStep : ∃ st₇, SpecRun rWork pWork arena rhsStmt st₆ st₇ 2 ∧
            st₇.regs rRhs = rowRhs i_t ∧
            VecRegs st₇ rSliceA (rowVec i_t) ∧
            st₇.ptrs = st₆.ptrs ∧ st₇.mem = st₆.mem := by
          cases negLast
          · obtain ⟨st₇, cr, hrhs7, _, hoth7, hp7, hm7⟩ :=
              copyReg_spec (rMin := rWork) (pMin := pWork) (memBound := arena)
                (rDst := rRhs) (rSrc := rRatio) (rZero := rZero) (s := st₆)
                (by omega) (by omega) (by omega) (by omega)
            refine ⟨st₇, cr, ?_, hvSlice6.of_pres fun j hj => hoth7 (rSliceA + j) (by omega) (by omega),
              hp7, hm7⟩
            rw [hrhs7, hoth6 rRatio (by omega) (by omega), hrat5, rowRhs_eq]; simp
          · have n1 : SpecRun rWork pWork arena (.prim (.const rZero 0)) st₆ _ 1 :=
              SpecRun.prim (show rWork ≤ rZero by omega) (by intro _ _ e; cases e)
            have n2 : SpecRun rWork pWork arena (.prim (.sub rRhs rZero rRatio))
                ((Prim.const rZero 0).step st₆) _ 1 :=
              SpecRun.prim (show rWork ≤ rRhs by omega) (by intro _ _ e; cases e)
            set st₇ := (Prim.sub rRhs rZero rRatio).step ((Prim.const rZero 0).step st₆)
            refine ⟨st₇, n1.seq n2, ?_,
              hvSlice6.of_pres fun j hj => by
                simp only [st₇, Prim.step]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
              rfl, rfl⟩
            simp only [st₇, Prim.step, Function.update_self,
              Function.update_of_ne (show rRatio ≠ rZero by omega)]
            rw [hoth6 rRatio (by omega) (by omega), hrat5, rowRhs_eq]; simp
        obtain ⟨st₇, c3, hrhs7, hvSlice7, hp7, hm7⟩ := hRhsStep
        have hpW7 : st₇.ptrs pWrite = arena + (((tightPref t).length : ℤ) + 1) * ((d : ℤ) + 1) := by
          rw [hp7, hp6]; simp [st₅, st₄, st₃, Prim.step, hp2, hp1,
            Function.update_of_ne (show pWrite ≠ pRead by omega), hpW]
        obtain ⟨st₈, c4, hStA, hStB, _, hp8, hm8⟩ :=
          storeRow_spec (rMin := rWork) (pMin := pWork) (memBound := arena) d
            (q := pWrite) (rA := rSliceA) (rB := rRhs) hvSlice7 hrhs7 (by omega)
            (by rw [hpW7]; nlinarith)
        have hBodyRun : SpecRun rWork pWork arena loopBody st st₈ (8 * d + 20) :=
          (b1.seq (b2.seq (b3.seq (b4.seq
            (SpecRun.ifLeZero_true (e := .skip) hle_gap
              (c1.seq (c2.seq (c3.seq c4)))))))).mono (by omega)
        have hBodyW := hBodyRun.weakenFrame (le_of_lt hVD_W) le_rfl le_rfl
        have hmEq7 : st₇.mem = st.mem := by rw [hm7, hm6]; simp [st₅, st₄, st₃, Prim.step, hm2, hm1]
        have htp_succ : tightPref (t + 1) = tightPref t ++ [i_t] := by
          simp [tightPref, htake_t, List.filter_append, List.filter_cons_of_pos hT]
        refine ⟨st₈, hBodyW, hmPres.trans hBodyW.mem_pres,
          h0A.of_mem_pres (bound := st₇.ptrs pWrite)
            (fun a ha => by rw [hm8 a (Or.inl ha), hmEq7]) (by rw [hpW7]; nlinarith),
          by rw [hm8 _ (Or.inl (by rw [hpW7]; nlinarith)), hmEq7]; exact h0B,
          ?_, ?_, ?_,
          fun q hq => (hBodyW.ptrs_pres q hq).trans (hpo q hq),
          fun r hr => (hBodyRun.regs_pres r hr).trans (hro r hr)⟩
        · intro k hk
          simp only [htp_succ, List.length_append, List.length_singleton] at hk
          by_cases hlt_k : k < (tightPref t).length
          · simp only [htp_succ, List.getElem_append_left hlt_k]
            obtain ⟨hkA, hkB⟩ := hRows k hlt_k
            have hbound_k : arena + ((k : ℤ) + 1) * ((d : ℤ) + 1) + ((d : ℤ) + 1) ≤ st₇.ptrs pWrite := by
              rw [hpW7]
              have : ((k : ℤ) + 2) * ((d : ℤ) + 1) ≤ (((tightPref t).length : ℤ) + 1) * ((d : ℤ) + 1) :=
                mul_le_mul_of_nonneg_right (by omega) (by omega)
              linarith
            refine ⟨hkA.of_mem_pres (bound := st₇.ptrs pWrite)
              (fun a ha => by rw [hm8 a (Or.inl ha), hmEq7]) (by linarith),
              by rw [hm8 _ (Or.inl (by linarith)), hmEq7]; exact hkB⟩
          · have heq_k : k = (tightPref t).length := by omega
            subst heq_k
            simp only [htp_succ, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
            rw [hpW7] at hStA hStB
            exact ⟨hStA, hStB⟩
        · rw [hp8, Function.update_of_ne (show pRead ≠ pWrite by omega), hp7, hp6]
          simp [st₅, st₄, st₃, Prim.step, hp2, hp1, hpR]; ring
        · rw [hp8, Function.update_self, hpW7, htp_succ]; simp; ring
      · have hTF : isTight i_t = false := Bool.eq_false_iff.mpr hT
        have hnotle_gap : ¬ st₄.regs rGap ≤ 0 := by
          rw [hgap4]; simpa [isTight] using hTF
        have hBodyRun : SpecRun rWork pWork arena loopBody st st₄ (8 * d + 20) :=
          (b1.seq (b2.seq (b3.seq (b4.seq
            (SpecRun.ifLeZero_false (t := _) hnotle_gap
              (SpecRun.skip rWork pWork arena st₄)))))).mono (by omega)
        have hBodyW := hBodyRun.weakenFrame (le_of_lt hVD_W) le_rfl le_rfl
        have hmEq4 : st₄.mem = st.mem := by simp [st₄, st₃, Prim.step, hm2, hm1]
        have htp_succ : tightPref (t + 1) = tightPref t := by
          have hnotT : ¬ isTight i_t = true := hT
          simp only [tightPref, htake_t, List.filter_append,
            List.filter_cons_of_neg hnotT, List.filter_nil, List.append_nil]
        refine ⟨st₄, hBodyW, hmPres.trans hBodyW.mem_pres,
          by rw [hmEq4]; exact h0A, by rw [hmEq4]; exact h0B,
          by rw [htp_succ, hmEq4]; exact hRows,
          by simp [st₄, st₃, Prim.step, hp2, hp1, hpR]; ring,
          by rw [htp_succ]; simp [st₄, st₃, Prim.step, hp2, hp1,
              Function.update_of_ne (show pWrite ≠ pRead by omega), hpW],
          fun q hq => (hBodyW.ptrs_pres q hq).trans (hpo q hq),
          fun r hr => (hBodyRun.regs_pres r hr).trans (hro r hr)⟩)
    (fun st hInv => by
      obtain ⟨_, _, _, _, hpR, _, hpo, _⟩ := hInv
      rw [hpR, hpo pTabEnd hpTE, hEnd])
    m le_rfl sf₀ (by simpa using hInvF0)
  obtain ⟨sf₁, hfRun, hmPres1, h0A_1, h0B_1, hRows1, _, hpW1, hpo1, _⟩ := hLoopF
  set Tlist := tightPref m
  set nT := Tlist.length
  have hnT_le : nT ≤ m := by
    dsimp [nT, Tlist, tightPref]
    exact le_trans (List.length_filter_le _ _) (by simp)
  -- Assemble `(augA M_T, augB rhs_T)` table at `[arena .. sf₁.ptrs pWrite)`
  let M_T : Matrix (Fin nT) (Fin d) ℝ := fun k => rowVec Tlist[k.1]
  let rhs_T : Fin nT → ℝ := fun k => rowRhs Tlist[k.1]
  have hpAr1 : sf₁.ptrs pArena = arena := hpo1 pArena hpAr
  have hTabSys : RowTableAt sf₁.mem (sf₁.ptrs pArena) (augA M_T) (augB rhs_T) := by
    rw [hpAr1]
    intro idx
    refine Fin.cases ?_ (fun k => ?_) idx
    · simp [augA, augB, h0A_1, h0B_1]
    · simp only [Fin.val_succ, augA, augB, Fin.cases_succ, Nat.cast_add, Nat.cast_one]
      exact hRows1 k.1 k.2
  have hpEndSys : sf₁.ptrs pWrite = sf₁.ptrs pArena + ((nT + 1 : ℕ) : ℤ) * ((d : ℤ) + 1) := by
    rw [hpAr1, hpW1]; push_cast; rfl
  -- Phase 3: call `sol.mkStmt` (`MinInfeasSolver d`) on `[pArena .. pWrite)` with sub-arena `pWrite`
  obtain ⟨sf₂, yDir, hSolRun, hyDir, hMinDir⟩ :=
    sol.spec (Nat.succ_pos nT)
      (rOut := rSubOut) (pTabStart := pArena) (pTabEnd := pWrite) (pArena := pWrite) (pBase := pSubBase)
      hTabSys rfl rfl hpEndSys (by rw [hpEndSys]) (by omega) (by omega) (by omega)
  -- Because `hSolRun` preserved `< sf₁.ptrs pWrite` and `< pSubBase`, the table is intact!
  have hTabSys2 : RowTableAt sf₂.mem (sf₂.ptrs pArena) (augA M_T) (augB rhs_T) := by
    rw [hSolRun.ptrs_pres pArena (by omega)]
    exact hTabSys.of_mem_pres hSolRun.mem_pres (by rw [hpEndSys])
  have hpEndSys2 : sf₂.ptrs pWrite = sf₂.ptrs pArena + ((nT + 1 : ℕ) : ℤ) * ((d : ℤ) + 1) := by
    rw [hSolRun.ptrs_pres pWrite (by omega), hSolRun.ptrs_pres pArena (by omega), hpEndSys]
  -- Phase 4: evaluate `rInfeas` at `yDir` into `rVDir`
  obtain ⟨sf₃, hEvalRun, hvDir3, _, _, _⟩ :=
    evalRowInfeasStmt_spec (rMin := rVDir) (pMin := pWork) (memBound := arena)
      (Nat.succ_pos nT) (rOut := rVDir) (pTabStart := pArena) (pTabEnd := pWrite)
      (rX := rSubOut) (rScratch := rEvalScr) (pCur := pEval)
      hTabSys2 hpEndSys2 hyDir le_rfl (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hSolW : SpecRun rVDir pWork arena _ sf₁ sf₂ (sol.C * (m + 2)) :=
    (hSolRun.weakenFrame (by omega) (by omega) (by rw [hpW1]; nlinarith)).mono
      (Nat.mul_le_mul_left _ (by omega))
  have hEvalM : SpecRun rVDir pWork arena _ sf₂ sf₃ ((4 * d + 12) * (m + 2) + 10) :=
    hEvalRun.mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 10)
  have hTotal : SpecRun rVDir pWork arena _ s sf₃ ((sol.C + 16 * d + 40) * (m + 2)) :=
    (hWrite0.seq ((f0.seq hfRun).seq (hSolW.seq hEvalM))).mono (by nlinarith)
  refine ⟨sf₃, hTotal, ?_⟩
  rw [decide_eq_true_eq, hvDir3, polyhedron_nonempty_iff_min_aug M_T rhs_T yDir hMinDir]
  have hmemT : ∀ i : Fin m, i ∈ Tlist ↔ v' = b i - A i ⬝ᵥ x' := by
    intro i
    have htk : (List.finRange m).take m = List.finRange m := by simp
    simp [Tlist, tightPref, htk, isTight_iff]
  constructor
  · rintro ⟨y', hy'⟩
    refine ⟨y', fun i hi => ?_⟩
    obtain ⟨k, hk, heq_k⟩ := List.mem_iff_getElem.mp ((hmemT i).mpr hi)
    have hk_in := hy' ⟨k, hk⟩
    simpa [M_T, rhs_T, Matrix.mulVec, heq_k, rowVec, rowRhs] using hk_in
  · rintro ⟨y', hy'⟩
    refine ⟨y', fun k => ?_⟩
    have hk_mem : Tlist[k.1] ∈ Tlist := List.getElem_mem _
    have hk_in := hy' Tlist[k.1] ((hmemT _).mp hk_mem)
    simpa [M_T, rhs_T, Matrix.mulVec, rowVec, rowRhs] using hk_in

/-- Complete oracle for fixed pivot coordinate `p : Fin (d + 1)` (`h p ≠ 0`). -/
noncomputable def oracleFixedPivotStmt {d : ℕ} (sol : MinInfeasSolver d) (p : Fin (d + 1))
    (rOut rH rBeta pTabStart pTabEnd pArena pBase : ℕ) : Stmt :=
  let D := d + 1
  let rVPrime := rOut + D
  let rSigma  := rOut + D + 1
  let rV1     := rOut + D + 2
  let rV2     := rOut + D + 3
  let rWork   := rOut + D + 4
  let rAi     := rWork
  let rBi     := rWork + D
  let rRatio  := rWork + D + 1
  let rProd   := rWork + D + 2
  let rSliceA := rWork + D + 3      -- d regs
  let rSliceB := rWork + 2 * d + 4
  let rYStar  := rWork + 2 * d + 5  -- d regs
  let rHProj  := rWork + 3 * d + 5  -- d regs
  let rDot    := rWork + 4 * d + 5
  let rXP     := rWork + 4 * d + 6
  let rZero   := rWork + 4 * d + 7
  let rEvalS  := rWork + 4 * d + 8  -- D + 6 regs
  let pRead   := pBase
  let pWrite  := pBase + 1
  let pEval   := pBase + 2
  let pSub    := pBase + 3
  let buildSliceStmt : Stmt :=
    Stmt.block [
      .prim (.pcopy pRead pTabStart),
      .prim (.pcopy pWrite pArena),
      .whilePtrLt pRead pTabEnd
        (Stmt.block [
          loadRow D rAi rBi pRead,
          .prim (.div rRatio (rAi + p.1) (rH + p.1)),
          sliceRowAAux d p rSliceA rAi rH rRatio rProd d le_rfl,
          .prim (.mul rProd rRatio rBeta),
          .prim (.sub rSliceB rBi rProd),
          storeRow d pWrite rSliceA rSliceB])]
  let liftPreStmt : Stmt :=
    Stmt.block [
      projSuccAboveAux d p rHProj rH rZero d le_rfl,
      dotRegs d rDot rHProj rYStar rProd,
      .prim (.sub rXP rBeta rDot),
      .prim (.div rXP rXP (rH + p.1)),
      scatterInsertStmt d p rOut rYStar rXP rZero]
  let liftAndEvalStmt : Stmt :=
    .seq liftPreStmt (evalRowInfeasStmt D rVPrime pTabStart pTabEnd rOut rEvalS pEval)
  let chooseSigmaStmt : Stmt :=
    .ifLeZero rV1
      (.prim (.const rSigma 1))
      (.ifLeZero rV2 (.prim (.const rSigma (-1))) (.prim (.const rSigma 1)))
  Stmt.block [
    buildSliceStmt,
    sol.mkStmt rYStar pArena pWrite pWrite pSub,
    liftAndEvalStmt,
    checkTightDirStmt sol p true rV1 rOut rVPrime rH pTabStart pTabEnd pArena rWork pSub,
    checkTightDirStmt sol p false rV2 rOut rVPrime rH pTabStart pTabEnd pArena rWork pSub,
    chooseSigmaStmt]

set_option maxHeartbeats 400000 in
theorem oracleFixedPivotStmt_spec {m d : ℕ} (sol : MinInfeasSolver d) (p : Fin (d + 1))
    (hm : 0 < m)
    {rOut rH rBeta pTabStart pTabEnd pArena pBase : ℕ}
    {A : Fin m → Fin (d + 1) → ℝ} {b : Fin m → ℝ}
    {h : Fin (d + 1) → ℝ} {β : ℝ} {s : MState}
    (hTab : RowTableAt s.mem (s.ptrs pTabStart) A b)
    (hA0 : A ⟨0, hm⟩ = 0) (hb0 : b ⟨0, hm⟩ = 0)
    (hEnd : s.ptrs pTabEnd = s.ptrs pTabStart + (m : ℤ) * ((d : ℤ) + 2))
    (hTabAr : s.ptrs pTabStart + (m : ℤ) * ((d : ℤ) + 2) ≤ s.ptrs pArena)
    (hh : VecRegs s rH h) (hβ : s.regs rBeta = β) (hp : h p ≠ 0)
    (hHO : rH + (d + 1) ≤ rOut) (hBO : rBeta < rOut)
    (hpTS : pTabStart < pBase) (hpTE : pTabEnd < pBase) (hpAr : pArena < pBase) :
    ∃ (s' : MState) (x' : Fin (d + 1) → ℝ) (σ : Ordering),
      SpecRun rOut pBase (s.ptrs pArena)
        (oracleFixedPivotStmt sol p rOut rH rBeta pTabStart pTabEnd pArena pBase)
        s s' ((6 * sol.C + 90 * d + 220) * (m + 1)) ∧
      VecRegs s' rOut x' ∧
      s'.regs (rOut + (d + 1)) = rInfeas hm A b x' ∧
      s'.regs (rOut + (d + 1) + 1) = encodeOrd σ ∧
      (∀ w : Fin (d + 1) → ℝ, rInfeas hm A b w < rInfeas hm A b x' → compare (h ⬝ᵥ w) β = σ) := by
  let D := d + 1
  set arena := s.ptrs pArena
  let rVPrime := rOut + D
  let rSigma  := rOut + D + 1
  let rV1     := rOut + D + 2
  let rV2     := rOut + D + 3
  let rWork   := rOut + D + 4
  let rAi     := rWork
  let rBi     := rWork + D
  let rRatio  := rWork + D + 1
  let rProd   := rWork + D + 2
  let rSliceA := rWork + D + 3
  let rSliceB := rWork + 2 * d + 4
  let rYStar  := rWork + 2 * d + 5
  let rHProj  := rWork + 3 * d + 5
  let rDot    := rWork + 4 * d + 5
  let rXP     := rWork + 4 * d + 6
  let rZero   := rWork + 4 * d + 7
  let rEvalS  := rWork + 4 * d + 8
  let pRead   := pBase
  let pWrite  := pBase + 1
  let pEval   := pBase + 2
  let pSub    := pBase + 3
  -- Phase 1: buildSliceStmt at `[arena .. arena + m * (d + 1))`
  let slA : Fin m → Fin d → ℝ := fun i => Fin.init (transRowA h p (A i))
  let slB : Fin m → ℝ := fun i => transRowB h p β (A i) (b i)
  have bs1 : SpecRun rWork pBase arena (.prim (.pcopy pRead pTabStart)) s _ 1 :=
    SpecRun.prim le_rfl (by intro _ _ e; cases e)
  have bs2 : SpecRun rWork pBase arena (.prim (.pcopy pWrite pArena))
      ((Prim.pcopy pRead pTabStart).step s) _ 1 :=
    SpecRun.prim (show pBase ≤ pWrite by omega) (by intro _ _ e; cases e)
  set sb₀ := (Prim.pcopy pWrite pArena).step ((Prim.pcopy pRead pTabStart).step s)
  let bsBody : Stmt :=
    Stmt.block [
      loadRow D rAi rBi pRead,
      .prim (.div rRatio (rAi + p.1) (rH + p.1)),
      sliceRowAAux d p rSliceA rAi rH rRatio rProd d le_rfl,
      .prim (.mul rProd rRatio rBeta),
      .prim (.sub rSliceB rBi rProd),
      storeRow d pWrite rSliceA rSliceB]
  let InvS : ℕ → MState → Prop := fun t st =>
    MemPreservedBelow arena s.mem st.mem ∧
    (∀ (k : Fin m), k.1 < t →
      VecAt st.mem (arena + (k.1 : ℤ) * ((d : ℤ) + 1)) (slA k) ∧
      st.mem (arena + (k.1 : ℤ) * ((d : ℤ) + 1) + (d : ℤ)) = slB k) ∧
    st.ptrs pRead = s.ptrs pTabStart + (t : ℤ) * ((d : ℤ) + 2) ∧
    st.ptrs pWrite = arena + (t : ℤ) * ((d : ℤ) + 1) ∧
    (∀ q < pBase, st.ptrs q = s.ptrs q) ∧
    (∀ r < rWork, st.regs r = s.regs r)
  have hInvS0 : InvS 0 sb₀ := by
    refine ⟨MemPreservedBelow.refl _ _, fun _ hk => absurd hk (Nat.not_lt_zero _),
      by simp [sb₀, Prim.step, Function.update_of_ne (show pRead ≠ pWrite by omega)],
      by simp [sb₀, Prim.step, Function.update_of_ne (show pArena ≠ pRead by omega), arena],
      fun q hq => by
        simp only [sb₀, Prim.step]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
      fun _ _ => rfl⟩
  have hLoopS := SpecRun.forLoop (rMin := rWork) (pMin := pBase) (memBound := arena)
    (q₁ := pRead) (q₂ := pTabEnd) (body := bsBody) m (6 * d + 9) InvS
    (fun t ht st hInv => by
      obtain ⟨hmPres, hRows, hpR, hpW, hpo, hro⟩ := hInv
      let i_t : Fin m := ⟨t, ht⟩
      refine ⟨by rw [hpR, hpo pTabEnd hpTE, hEnd]
                 have : (t : ℤ) * ((d : ℤ) + 2) < (m : ℤ) * ((d : ℤ) + 2) :=
                   mul_lt_mul_of_pos_right (by omega) (by omega)
                 linarith, ?_⟩
      have hTab_st : RowTableAt st.mem (s.ptrs pTabStart) A b :=
        hTab.of_mem_pres hmPres (by simpa [add_assoc] using hTabAr)
      obtain ⟨hAi_m, hbi_m⟩ := hTab_st i_t
      have hpR_eq : st.ptrs pRead = s.ptrs pTabStart + (i_t.1 : ℤ) * (((d + 1 : ℕ) : ℤ) + 1) := by
        simpa [i_t, Nat.cast_add, add_assoc] using hpR
      rw [← hpR_eq] at hAi_m hbi_m
      obtain ⟨st₁, q1, hvAi1, hbi1, hoth1, hp1, hm1⟩ :=
        loadRow_spec (rMin := rWork) (pMin := pBase) (memBound := arena) D
          (rA := rAi) (rB := rBi) (q := pRead) hAi_m hbi_m le_rfl (by omega) (by omega) le_rfl
      have q2 : SpecRun rWork pBase arena (.prim (.div rRatio (rAi + p.1) (rH + p.1))) st₁ _ 1 :=
        SpecRun.prim (show rWork ≤ rRatio by omega) (by intro _ _ e; cases e)
      set st₂ := (Prim.div rRatio (rAi + p.1) (rH + p.1)).step st₁
      have hvAi2 : VecRegs st₂ rAi (A i_t) :=
        hvAi1.of_pres fun j hj => Function.update_of_ne (by omega) _ _
      have hh2 : VecRegs st₂ rH h :=
        hh.of_pres fun j hj => by
          simp only [st₂, Prim.step]
          rw [Function.update_of_ne (by omega), hoth1 (rH + j) (by omega) (by omega)]
          exact hro (rH + j) (by omega)
      have hrat2 : st₂.regs rRatio = A i_t p / h p := by
        have hp_lt := p.2
        simp only [st₂, Prim.step, Function.update_self]
        rw [hvAi1 p, hoth1 (rH + p.1) (by omega) (by omega), hro (rH + p.1) (by omega), hh p]
      obtain ⟨st₃, q3, hslice3, hoth3, hp3, hm3⟩ :=
        sliceRowAAux_spec (rMin := rWork) (pMin := pBase) (memBound := arena) p
          (rDst := rSliceA) (rAi := rAi) (rH := rH) (rRatio := rRatio) (rTmp := rProd)
          hvAi2 hh2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) d le_rfl
      have q4 : SpecRun rWork pBase arena (.prim (.mul rProd rRatio rBeta)) st₃ _ 1 :=
        SpecRun.prim (show rWork ≤ rProd by omega) (by intro _ _ e; cases e)
      set st₄ := (Prim.mul rProd rRatio rBeta).step st₃
      have q5 : SpecRun rWork pBase arena (.prim (.sub rSliceB rBi rProd)) st₄ _ 1 :=
        SpecRun.prim (show rWork ≤ rSliceB by omega) (by intro _ _ e; cases e)
      set st₅ := (Prim.sub rSliceB rBi rProd).step st₄
      have hvSl5 : VecRegs st₅ rSliceA (slA i_t) := by
        intro j
        simp only [st₅, st₄, Prim.step, Function.update_of_ne (show rSliceA + j.1 ≠ rSliceB by omega),
          Function.update_of_ne (show rSliceA + j.1 ≠ rProd by omega)]
        rw [hslice3 j.1 j.2, hrat2]; simp [slA, transRowA]
      have hbSl5 : st₅.regs rSliceB = slB i_t := by
        simp only [st₅, st₄, Prim.step, Function.update_self,
          Function.update_of_ne (show rBi ≠ rProd by omega)]
        rw [hoth3 rBi (by omega) (by omega), hoth3 rRatio (by omega) (by omega),
            hoth3 rBeta (by omega) (by omega), hrat2]
        simp only [st₂, Prim.step, Function.update_of_ne (show rBi ≠ rRatio by omega),
          Function.update_of_ne (show rBeta ≠ rRatio by omega), hbi1,
          hoth1 rBeta (by omega) (by omega), hro rBeta (by omega), hβ, slB, transRowB]
      have hpW5 : st₅.ptrs pWrite = arena + (t : ℤ) * ((d : ℤ) + 1) := by
        simp [st₅, st₄, Prim.step, hp3, st₂, hp1, Function.update_of_ne (show pWrite ≠ pRead by omega), hpW]
      obtain ⟨st₆, q6, hStA, hStB, _, hp6, hm6⟩ :=
        storeRow_spec (rMin := rWork) (pMin := pBase) (memBound := arena) d
          (q := pWrite) (rA := rSliceA) (rB := rSliceB) hvSl5 hbSl5 (by omega)
          (by rw [hpW5]; nlinarith)
      have hBody : SpecRun rWork pBase arena bsBody st st₆ (6 * d + 9) :=
        (q1.seq (q2.seq (q3.seq (q4.seq (q5.seq q6))))).mono (by omega)
      have hmEq5 : st₅.mem = st.mem := by simp [st₅, st₄, Prim.step, hm3, st₂, hm1]
      refine ⟨st₆, hBody, hmPres.trans hBody.mem_pres, ?_, ?_, ?_,
        fun q hq => (hBody.ptrs_pres q hq).trans (hpo q hq),
        fun r hr => (hBody.regs_pres r hr).trans (hro r hr)⟩
      · intro k hk
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
        · obtain ⟨hkA, hkB⟩ := hRows k hlt
          have hbound_k : arena + (k.1 : ℤ) * ((d : ℤ) + 1) + ((d : ℤ) + 1) ≤ st₅.ptrs pWrite := by
            rw [hpW5]
            have : ((k.1 : ℤ) + 1) * ((d : ℤ) + 1) ≤ (t : ℤ) * ((d : ℤ) + 1) :=
              mul_le_mul_of_nonneg_right (by omega) (by omega)
            linarith
          exact ⟨hkA.of_mem_pres (bound := st₅.ptrs pWrite)
            (fun a ha => by rw [hm6 a (Or.inl ha), hmEq5]) (by linarith),
            by rw [hm6 _ (Or.inl (by linarith)), hmEq5]; exact hkB⟩
        · have hk_eq : k = i_t := Fin.ext heq
          subst hk_eq
          rw [hpW5] at hStA hStB; exact ⟨hStA, hStB⟩
      · rw [hp6, Function.update_of_ne (show pRead ≠ pWrite by omega)]
        simp [st₅, st₄, Prim.step, hp3, st₂, hp1, hpR, D]; ring
      · rw [hp6, Function.update_self, hpW5]; push_cast; ring)
    (fun st hInv => by
      obtain ⟨_, _, hpR, _, hpo, _⟩ := hInv
      rw [hpR, hpo pTabEnd hpTE, hEnd])
    m le_rfl sb₀ (by simpa using hInvS0)
  obtain ⟨s₁, hbsRun, hmPres1, hRows1, _, hpW1, hpo1, hro1⟩ := hLoopS
  have hBuildSlice : SpecRun rOut pBase arena _ s s₁ ((6 * d + 11) * m + 5) :=
    ((bs1.seq (bs2.seq hbsRun)).weakenFrame (by omega) le_rfl le_rfl).mono (by nlinarith)
  have hTabSl : RowTableAt s₁.mem (s₁.ptrs pArena) slA slB := by
    rw [hpo1 pArena hpAr]
    exact fun i => hRows1 i i.2
  have hpEndSl : s₁.ptrs pWrite = s₁.ptrs pArena + (m : ℤ) * ((d : ℤ) + 1) := by
    rw [hpo1 pArena hpAr, hpW1]
  have hslA0 : slA ⟨0, hm⟩ = 0 := by ext j; simp [slA, hA0, Fin.init]
  have hslB0 : slB ⟨0, hm⟩ = 0 := by simp [slB, hA0, hb0]
  -- Phase 2: call `sol.mkStmt` on `[pArena .. pWrite)` with sub-arena `pWrite`
  obtain ⟨s₂, yStar, hSol1_raw, hyStar, hSliceMin⟩ :=
    sol.spec hm (rOut := rYStar) (pTabStart := pArena) (pTabEnd := pWrite) (pArena := pWrite) (pBase := pSub)
      hTabSl hslA0 hslB0 hpEndSl (by rw [hpEndSl]) (by omega) (by omega) (by omega)
  have hSol1 : SpecRun rOut pBase arena _ s₁ s₂ (sol.C * (m + 1)) :=
    hSol1_raw.weakenFrame (by omega) (by omega) (by rw [hpW1]; nlinarith)
  -- Phase 3: lift `yStar` to `x' = liftSlice h p β yStar 0` and evaluate `v'`
  have hh2_in : VecRegs s₂ rH h :=
    hh.of_pres fun j hj => (hSol1_raw.regs_pres (rH + j) (by omega)).trans (hro1 (rH + j) (by omega))
  obtain ⟨sl₁, l1, hproj1, hothL1, hpL1, hmL1⟩ :=
    projSuccAboveAux_spec (rMin := rOut) (pMin := pBase) (memBound := arena) p
      (rDst := rHProj) (rSrc := rH) (rZero := rZero) hh2_in
      (by omega) (by omega) (by omega) (by omega) (by omega) d le_rfl
  have hvHProj : VecRegs sl₁ rHProj (fun j : Fin d => h (p.succAbove j)) :=
    fun j => hproj1 j.1 j.2
  have hyStar_l1 : VecRegs sl₁ rYStar yStar :=
    hyStar.of_pres fun j hj => hothL1 (rYStar + j) (by omega) (by omega)
  obtain ⟨sl₂, l2, hdotL2, hothL2, hpL2, hmL2⟩ :=
    dotRegs_spec (rMin := rOut) (pMin := pBase) (memBound := arena) d
      hvHProj hyStar_l1 (rAcc := rDot) (rProd := rProd)
      (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have l3 : SpecRun rOut pBase arena (.prim (.sub rXP rBeta rDot)) sl₂ _ 1 :=
    SpecRun.prim (show rOut ≤ rXP by omega) (by intro _ _ e; cases e)
  set sl₃ := (Prim.sub rXP rBeta rDot).step sl₂
  have l4 : SpecRun rOut pBase arena (.prim (.div rXP rXP (rH + p.1))) sl₃ _ 1 :=
    SpecRun.prim (show rOut ≤ rXP by omega) (by intro _ _ e; cases e)
  set sl₄ := (Prim.div rXP rXP (rH + p.1)).step sl₃
  have hxp4 : sl₄.regs rXP = (β + 0 - ∑ j : Fin d, h (p.succAbove j) * yStar j) / h p := by
    have hp_lt := p.2
    simp only [sl₄, sl₃, Prim.step, Function.update_self,
      Function.update_of_ne (show rH + p.1 ≠ rXP by omega)]
    have hbeta2 : sl₂.regs rBeta = β := by
      rw [hothL2 rBeta (by omega) (by omega), hothL1 rBeta (by omega) (by omega),
          hSol1_raw.regs_pres rBeta (by omega), hro1 rBeta (by omega), hβ]
    have hhp2 : sl₂.regs (rH + p.1) = h p := by
      rw [hothL2 (rH + p.1) (by omega) (by omega), hothL1 (rH + p.1) (by omega) (by omega), hh2_in p]
    rw [hbeta2, hdotL2, hhp2]; simp [dotProduct]
  have hyStar_l4 : VecRegs sl₄ rYStar yStar :=
    hyStar_l1.of_pres fun j hj => by
      simp only [sl₄, sl₃, Prim.step]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hothL2 (rYStar + j) (by omega) (by omega)
  obtain ⟨sl₅, l5, hvX5, hothL5, hpL5, hmL5⟩ :=
    scatterInsertStmt_spec (rMin := rOut) (pMin := pBase) (memBound := arena) p
      (rDst := rOut) (rY := rYStar) (rXP := rXP) (rZero := rZero) hyStar_l4
      le_rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hxp4] at hvX5
  set x' := liftSlice h p β yStar 0
  change VecRegs sl₅ rOut x' at hvX5
  have hLiftPre : SpecRun rOut pBase arena _ s₂ sl₅ (6 * d + 5) :=
    (l1.seq (l2.seq (l3.seq (l4.seq l5)))).mono (by omega)
  have hPreTo5 := (hBuildSlice.seq hSol1).seq hLiftPre
  have hTab5 : RowTableAt sl₅.mem (sl₅.ptrs pTabStart) A b := by
    rw [hPreTo5.ptrs_pres pTabStart hpTS]
    exact hTab.of_mem_pres hPreTo5.mem_pres (by simpa [add_assoc] using hTabAr)
  have hEnd5 : sl₅.ptrs pTabEnd = sl₅.ptrs pTabStart + (m : ℤ) * ((D : ℤ) + 1) := by
    rw [hPreTo5.ptrs_pres pTabEnd hpTE, hPreTo5.ptrs_pres pTabStart hpTS, hEnd]; dsimp [D]; ring
  obtain ⟨s₃, l6, hvP3, hothL6, hpL6, hmL6⟩ :=
    evalRowInfeasStmt_spec (rMin := rOut) (pMin := pBase) (memBound := arena)
      hm (rOut := rVPrime) (pTabStart := pTabStart) (pTabEnd := pTabEnd)
      (rX := rOut) (rScratch := rEvalS) (pCur := pEval)
      hTab5 hEnd5 hvX5 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hLiftEval : SpecRun rOut pBase arena _ s₂ s₃ ((10 * d + 20) * (m + 1)) :=
    (hLiftPre.seq l6).mono (by dsimp [D] at *; nlinarith)
  have hvX3 : VecRegs s₃ rOut x' :=
    hvX5.of_pres fun j hj => hothL6 (rOut + j) (by omega) (by omega)
  -- Phase 4: `checkTightDirStmt` for `sys1` (`negLast = true`)
  have hPre3 := (hBuildSlice.seq hSol1).seq hLiftEval
  have hTab3 : RowTableAt s₃.mem (s₃.ptrs pTabStart) A b := by
    rw [hPre3.ptrs_pres pTabStart hpTS]
    exact hTab.of_mem_pres hPre3.mem_pres (by simpa [add_assoc] using hTabAr)
  have hh3 : VecRegs s₃ rH h :=
    hh.of_pres fun j hj => hPre3.regs_pres (rH + j) (by omega)
  obtain ⟨s₄, hChk1_raw, hs1_iff⟩ :=
    checkTightDirStmt_spec sol p true hm
      (rVDir := rV1) (rXPrime := rOut) (rVPrime := rVPrime) (rH := rH)
      (pTabStart := pTabStart) (pTabEnd := pTabEnd) (pArena := pArena)
      (rWork := rWork) (pWork := pSub)
      hTab3 (by rw [hPre3.ptrs_pres pTabEnd hpTE, hPre3.ptrs_pres pTabStart hpTS, hEnd])
      (by rw [hPre3.ptrs_pres pTabStart hpTS, hPre3.ptrs_pres pArena hpAr]; exact hTabAr)
      hh3 hp hvX3 hvP3 hHO le_rfl (by omega) (by omega) (by omega) (by omega) (by omega)
  have hpAr3 : s₃.ptrs pArena = arena := hPre3.ptrs_pres pArena hpAr
  rw [hpAr3] at hChk1_raw
  have hChk1 : SpecRun rOut pBase arena _ s₃ s₄ ((2 * sol.C + 32 * d + 80) * (m + 1)) :=
    (hChk1_raw.weakenFrame (by omega) (by omega) le_rfl).mono (by nlinarith)
  -- Phase 5: `checkTightDirStmt` for `sys2` (`negLast = false`)
  have hPre4 := hPre3.seq hChk1
  have hTab4 : RowTableAt s₄.mem (s₄.ptrs pTabStart) A b := by
    rw [hPre4.ptrs_pres pTabStart hpTS]
    exact hTab.of_mem_pres hPre4.mem_pres (by simpa [add_assoc] using hTabAr)
  have hh4 : VecRegs s₄ rH h :=
    hh.of_pres fun j hj => hPre4.regs_pres (rH + j) (by omega)
  have hvX4 : VecRegs s₄ rOut x' :=
    hvX3.of_pres fun j hj => hChk1_raw.regs_pres (rOut + j) (by omega)
  have hvP4 : s₄.regs rVPrime = rInfeas hm A b x' :=
    (hChk1_raw.regs_pres rVPrime (by omega)).trans hvP3
  obtain ⟨s₅, hChk2_raw, hs2_iff⟩ :=
    checkTightDirStmt_spec sol p false hm
      (rVDir := rV2) (rXPrime := rOut) (rVPrime := rVPrime) (rH := rH)
      (pTabStart := pTabStart) (pTabEnd := pTabEnd) (pArena := pArena)
      (rWork := rWork) (pWork := pSub)
      hTab4 (by rw [hPre4.ptrs_pres pTabEnd hpTE, hPre4.ptrs_pres pTabStart hpTS, hEnd])
      (by rw [hPre4.ptrs_pres pTabStart hpTS, hPre4.ptrs_pres pArena hpAr]; exact hTabAr)
      hh4 hp hvX4 hvP4 hHO le_rfl (by omega) (by omega) (by omega) (by omega) (by omega)
  have hpAr4 : s₄.ptrs pArena = arena := hPre4.ptrs_pres pArena hpAr
  rw [hpAr4] at hChk2_raw
  have hChk2 : SpecRun rOut pBase arena _ s₄ s₅ ((2 * sol.C + 32 * d + 80) * (m + 1)) :=
    (hChk2_raw.weakenFrame (by omega) (by omega) le_rfl).mono (by nlinarith)
  have hv1_5 : s₅.regs rV1 = s₄.regs rV1 := hChk2_raw.regs_pres rV1 (by omega)
  have hvX5_fin : VecRegs s₅ rOut x' :=
    hvX4.of_pres fun j hj => hChk2_raw.regs_pres (rOut + j) (by omega)
  have hvP5_fin : s₅.regs rVPrime = rInfeas hm A b x' :=
    (hChk2_raw.regs_pres rVPrime (by omega)).trans hvP4
  -- Phase 6: `chooseSigmaStmt`
  set s1 := decide (s₅.regs rV1 ≤ 0)
  set s2 := decide (s₅.regs rV2 ≤ 0)
  set σ : Ordering := if s1 && !s2 then .gt else if !s1 && s2 then .lt else .gt
  simp only [if_true] at hs1_iff
  simp only [Bool.false_eq_true, if_false] at hs2_iff
  rw [← hv1_5] at hs1_iff
  have hSound := oracle_hyperplane hm A b h p hp β yStar hSliceMin hs1_iff hs2_iff
  have hChoose : ∃ s₆, SpecRun rOut pBase arena
      (.ifLeZero rV1 (.prim (.const rSigma 1))
        (.ifLeZero rV2 (.prim (.const rSigma (-1))) (.prim (.const rSigma 1)))) s₅ s₆ 5 ∧
      VecRegs s₆ rOut x' ∧
      s₆.regs rVPrime = rInfeas hm A b x' ∧
      s₆.regs rSigma = encodeOrd σ := by
    by_cases hc1 : s₅.regs rV1 ≤ 0
    · have p6 : SpecRun rOut pBase arena (.prim (.const rSigma 1)) s₅ _ 1 :=
        SpecRun.prim (show rOut ≤ rSigma by omega) (by intro _ _ e; cases e)
      refine ⟨_, (SpecRun.ifLeZero_true (e := _) hc1 p6).mono (by omega),
        hvX5_fin.of_pres fun j hj => Function.update_of_ne (by omega) _ _,
        by simp [Prim.step, Function.update_of_ne (show rVPrime ≠ rSigma by omega), hvP5_fin],
        by have hs1T : s1 = true := decide_eq_true hc1
           cases hs2 : s2 <;> simp [σ, hs1T, hs2, encodeOrd, Prim.step]⟩
    · by_cases hc2 : s₅.regs rV2 ≤ 0
      · have p6 : SpecRun rOut pBase arena (.prim (.const rSigma (-1))) s₅ _ 1 :=
          SpecRun.prim (show rOut ≤ rSigma by omega) (by intro _ _ e; cases e)
        refine ⟨_, (SpecRun.ifLeZero_false (t := _) hc1
            (SpecRun.ifLeZero_true (e := _) hc2 p6)).mono (by omega),
          hvX5_fin.of_pres fun j hj => Function.update_of_ne (by omega) _ _,
          by simp [Prim.step, Function.update_of_ne (show rVPrime ≠ rSigma by omega), hvP5_fin],
          by have hs1F : s1 = false := decide_eq_false hc1
             have hs2T : s2 = true := decide_eq_true hc2
             simp [σ, hs1F, hs2T, encodeOrd, Prim.step]⟩
      · have p6 : SpecRun rOut pBase arena (.prim (.const rSigma 1)) s₅ _ 1 :=
          SpecRun.prim (show rOut ≤ rSigma by omega) (by intro _ _ e; cases e)
        refine ⟨_, (SpecRun.ifLeZero_false (t := _) hc1
            (SpecRun.ifLeZero_false (t := _) hc2 p6)).mono (by omega),
          hvX5_fin.of_pres fun j hj => Function.update_of_ne (by omega) _ _,
          by simp [Prim.step, Function.update_of_ne (show rVPrime ≠ rSigma by omega), hvP5_fin],
          by have hs1F : s1 = false := decide_eq_false hc1
             have hs2F : s2 = false := decide_eq_false hc2
             simp [σ, hs1F, hs2F, encodeOrd, Prim.step]⟩
  obtain ⟨s₆, hChRun, hvX6, hvP6, hSig6⟩ := hChoose
  have hStepBound : (6 * d + 11) * m + 5 +
      (sol.C * (m + 1) + ((10 * d + 20) * (m + 1) +
        ((2 * sol.C + 32 * d + 80) * (m + 1) +
          ((2 * sol.C + 32 * d + 80) * (m + 1) + 5)))) ≤
      (6 * sol.C + 90 * d + 220) * (m + 1) := by
    clear * -
    have h1 : (6 * d + 11) * m ≤ (6 * d + 11) * (m + 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : (6 * d + 11) * (m + 1) + sol.C * (m + 1) + (10 * d + 20) * (m + 1) +
        (2 * sol.C + 32 * d + 80) * (m + 1) + (2 * sol.C + 32 * d + 80) * (m + 1) +
        10 * (m + 1) = (5 * sol.C + 80 * d + 201) * (m + 1) := by ring
    have h3 : (5 * sol.C + 80 * d + 201) * (m + 1) ≤ (6 * sol.C + 90 * d + 220) * (m + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : 10 ≤ 10 * (m + 1) := by omega
    omega
  refine ⟨s₆, x', σ,
    (hBuildSlice.seq (hSol1.seq (hLiftEval.seq (hChk1.seq (hChk2.seq hChRun))))).mono hStepBound,
    hvX6, hvP6, hSig6, hSound⟩

/-! ## Compile-Time Pivot Cascade Building `OracleSolver (d + 1)` -/

/-- Test `h ⟨k, _⟩ = 0` for `k = 0 .. d`: the first nonzero coordinate dispatches to `oracleFixedPivotStmt`. -/
noncomputable def oraclePivotCascade {d : ℕ} (sol : MinInfeasSolver d)
    (rOut rH rBeta pTabStart pTabEnd pArena pBase : ℕ) :
    (k : ℕ) → k ≤ d + 1 → Stmt
  | 0, _ => .skip
  | j + 1, hj =>
    let idx := (d + 1) - (j + 1)
    have hidx : idx < d + 1 := by omega
    ifEqZero (rH + idx) rOut (rOut + 1)
      (oraclePivotCascade sol rOut rH rBeta pTabStart pTabEnd pArena pBase j (by omega))
      (oracleFixedPivotStmt sol ⟨idx, hidx⟩ rOut rH rBeta pTabStart pTabEnd pArena pBase)

/-- Construct an `OracleSolver (d + 1)` from any `MinInfeasSolver d`. -/
noncomputable def buildOracleSolver {d : ℕ} (sol : MinInfeasSolver d) : OracleSolver (d + 1) where
  C := 6 * sol.C + 95 * d + 230
  mkStmt := fun rOut rH rBeta pTabStart pTabEnd pArena pBase =>
    oraclePivotCascade sol rOut rH rBeta pTabStart pTabEnd pArena pBase (d + 1) le_rfl
  spec := by
    intro m hm rOut rH rBeta pTabStart pTabEnd pArena pBase A b h β s
      hTab hA0 hb0 hEnd hTabAr hh hβ hh_ne hHO hBO hpTS hpTE hpAr
    -- Induction on `j ≤ d + 1` assuming some `p ≥ (d + 1) - j` has `h p ≠ 0`
    have hCascade : ∀ (j : ℕ) (hj : j ≤ d + 1) (st : MState),
        st.mem = s.mem → st.ptrs = s.ptrs →
        (∀ r < rOut, st.regs r = s.regs r) →
        (∃ p : Fin (d + 1), (d + 1) - j ≤ p.1 ∧ h p ≠ 0) →
        ∃ (s' : MState) (x' : Fin (d + 1) → ℝ) (σ : Ordering),
          SpecRun rOut pBase (s.ptrs pArena)
            (oraclePivotCascade sol rOut rH rBeta pTabStart pTabEnd pArena pBase j hj)
            st s' ((6 * sol.C + 90 * d + 220) * (m + 1) + 5 * j) ∧
          VecRegs s' rOut x' ∧
          s'.regs (rOut + (d + 1)) = rInfeas hm A b x' ∧
          s'.regs (rOut + (d + 1) + 1) = encodeOrd σ ∧
          (∀ w : Fin (d + 1) → ℝ, rInfeas hm A b w < rInfeas hm A b x' → compare (h ⬝ᵥ w) β = σ) := by
      intro j
      induction j with
      | zero =>
        intro hj _ _ _ _ ⟨p, hp_ge, _⟩
        have := p.2; omega
      | succ j ih =>
        intro hj st hmem hptrs hregs ⟨p_wit, hp_ge, hp_wit_ne⟩
        set idx := (d + 1) - (j + 1)
        have hidx : idx < d + 1 := by omega
        let p₀ : Fin (d + 1) := ⟨idx, hidx⟩
        have hreg_idx : st.regs (rH + idx) = h p₀ := by
          rw [hregs (rH + idx) (by omega)]; exact hh p₀
        set stPre := eqZeroPre (rH + idx) rOut (rOut + 1) st
        have hregsPre : ∀ r < rOut, stPre.regs r = s.regs r := by
          intro r hr
          rw [eqZeroPre_regs_other st (by omega) (by omega)]
          exact hregs r hr
        by_cases hp0 : h p₀ = 0
        · have heq0 : st.regs (rH + idx) = 0 := hreg_idx.trans hp0
          have hp_gt : (d + 1) - j ≤ p_wit.1 := by
            have hne_p : p_wit.1 ≠ idx := fun hv => hp_wit_ne (by convert hp0; exact Fin.ext hv)
            omega
          obtain ⟨s', x', σ, hSub, hvX, hvP, hSig, hSound⟩ :=
            ih (by omega) stPre (by simp [stPre, hmem]) (by simp [stPre, hptrs]) hregsPre
              ⟨p_wit, hp_gt, hp_wit_ne⟩
          have hStep := ifEqZero_true_spec (rMin := rOut) (pMin := pBase) (memBound := s.ptrs pArena)
            (e := oracleFixedPivotStmt sol p₀ rOut rH rBeta pTabStart pTabEnd pArena pBase)
            le_rfl (by omega) (by omega) (by omega) (by omega) heq0 hSub
          exact ⟨s', x', σ, hStep.mono (by omega), hvX, hvP, hSig, hSound⟩
        · have hne0 : st.regs (rH + idx) ≠ 0 := by rw [hreg_idx]; exact hp0
          have hEnd_pre : stPre.ptrs pTabEnd = stPre.ptrs pTabStart + (m : ℤ) * ((d : ℤ) + 2) := by
            simp only [stPre, eqZeroPre_ptrs, hptrs, hEnd]; push_cast; ring
          obtain ⟨s', x', σ, hFix, hvX, hvP, hSig, hSound⟩ :=
            oracleFixedPivotStmt_spec sol p₀ hm
              (rOut := rOut) (rH := rH) (rBeta := rBeta)
              (pTabStart := pTabStart) (pTabEnd := pTabEnd) (pArena := pArena) (pBase := pBase)
              (s := stPre)
              (by simp [stPre, hmem, hptrs]; exact hTab)
              hA0 hb0 hEnd_pre
              (by simp [stPre, hptrs]; simpa [add_assoc] using hTabAr)
              (hh.of_pres fun k hk => hregsPre (rH + k) (by omega))
              (by rw [hregsPre rBeta hBO, hβ]) hp0
              hHO hBO hpTS hpTE hpAr
          simp only [stPre, eqZeroPre_ptrs, hptrs] at hFix
          have hStep := ifEqZero_false_spec (rMin := rOut) (pMin := pBase) (memBound := s.ptrs pArena)
            (t := oraclePivotCascade sol rOut rH rBeta pTabStart pTabEnd pArena pBase j (by omega))
            le_rfl (by omega) (by omega) (by omega) (by omega) hne0 hFix
          exact ⟨s', x', σ, hStep.mono (by omega), hvX, hvP, hSig, hSound⟩
    have hex : ∃ p : Fin (d + 1), 0 ≤ p.1 ∧ h p ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hh_ne; ext p; exact hall p (Nat.zero_le _)
    obtain ⟨s', x', σ, hRun, hvX, hvP, hSig, hSound⟩ :=
      hCascade (d + 1) le_rfl s rfl rfl (fun _ _ => rfl) (by simpa using hex)
    have hBnd : (6 * sol.C + 90 * d + 220) * (m + 1) + 5 * (d + 1) ≤
        (6 * sol.C + 95 * d + 230) * (m + 1) := by
      clear * -
      have h1 : 5 * (d + 1) ≤ (5 * d + 10) * (m + 1) :=
        le_trans (show 5 * (d + 1) ≤ (5 * d + 10) * 1 by omega) (Nat.mul_le_mul_left _ (by omega))
      have h2 : (6 * sol.C + 90 * d + 220) * (m + 1) + (5 * d + 10) * (m + 1) =
          (6 * sol.C + 95 * d + 230) * (m + 1) := by ring
      omega
    exact ⟨s', x', σ, hRun.mono hBnd, hvX, hvP, hSig, hSound⟩

end MegiddoLP.Oracle


