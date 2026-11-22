-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintGaussSetup20261120
-- name    : LinearSetReconciliation327_Main_HintGaussSetup20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T10:01:38.551515+00:00
-- url     : https://prove2.me/theorems/213b984b-6046-43c8-9aaf-a71985c4f5a6
-- title:
--   LinearSetReconciliation327 — HintGaussSetup (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintGaussSetup20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowMap20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintRowRank20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- Private Gaussian workspace parameters are read from ordinary RAM. Register14
    is the stable context pointer; register3 is temporary. -/
def hintLoadField (dest : Fin 16) (index : ℕ) : List Instr :=
  [.imm 3 index, .add 3 14 3, .load dest 3]

theorem hintLoadField_spec (E : RAMEnv) (state : RAMState) (dest : Fin 16) (index context : ℕ)
    (hContext : state.regs 14 = context) (hAddr : context + index < 2 ^ E.W) :
    let out := runBlock (hintLoadField dest index) E state
    out.pc = state.pc + 3 ∧ out.mem = state.mem ∧
      out.regs dest = state.mem (context + index) % 2 ^ E.W ∧
      (∀ r, r ≠ 3 → r ≠ dest → out.regs r = state.regs r) := by
  have hIndex : index < 2 ^ E.W := by omega
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hintLoadField, runBlock, execInstr, Nat.add_assoc]
  · rfl
  · simp [hintLoadField, runBlock, execInstr, hContext, Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hAddr]
  · intro r h3 hd
    simp [hintLoadField, runBlock, execInstr, Function.update_of_ne h3, Function.update_of_ne hd]

def hintLoadFields (fields : List (Fin 16 × ℕ)) : List Instr :=
  fields.flatMap (fun pair => hintLoadField pair.1 pair.2)

def hintLoadedValue (memory : ℕ → ℕ) (modulus context : ℕ) : List (Fin 16 × ℕ) → Fin 16 → ℕ → ℕ
  | [], _, old => old
  | (dest, index) :: rest, r, old =>
      hintLoadedValue memory modulus context rest r (if r = dest then memory (context + index) % modulus else old)

theorem hintLoadFields_spec (E : RAMEnv) (context : ℕ) (fields : List (Fin 16 × ℕ))
    (state : RAMState) (hContext : state.regs 14 = context)
    (hFields : ∀ pair ∈ fields, pair.1 ≠ 14 ∧ context + pair.2 < 2 ^ E.W) :
    let out := runBlock (hintLoadFields fields) E state
    out.pc = state.pc + 3 * fields.length ∧ out.mem = state.mem ∧ out.regs 14 = context ∧
      ∀ r, r ≠ 3 → out.regs r = hintLoadedValue state.mem (2 ^ E.W) context fields r (state.regs r) := by
  induction fields generalizing state with
  | nil => simp [hintLoadFields, runBlock, hintLoadedValue, hContext]
  | cons pair rest ih =>
      rcases pair with ⟨dest, index⟩
      let mid := runBlock (hintLoadField dest index) E state
      have hValid := hFields (dest, index) (by simp)
      have hHead := hintLoadField_spec E state dest index context hContext hValid.2
      have hMid14 : mid.regs 14 = context :=
        (hHead.2.2.2 14 (by decide) (Ne.symm hValid.1)).trans hContext
      have hTail := ih mid hMid14 (by intro pair hp; exact hFields pair (by simp [hp]))
      dsimp only
      rw [hintLoadFields, List.flatMap_cons, runBlock_append]
      refine ⟨?_, hTail.2.1.trans hHead.2.1, hTail.2.2.1, ?_⟩
      · change (runBlock (hintLoadFields rest) E mid).pc = state.pc + 3 * (rest.length + 1)
        rw [hTail.1, hHead.1]
        omega
      · intro r hr3
        have hValue : mid.regs r = if r = dest then state.mem (context + index) % 2 ^ E.W else state.regs r := by
          by_cases he : r = dest
          · subst r
            rw [if_pos rfl]
            exact hHead.2.2.1
          · rw [if_neg he]
            exact hHead.2.2.2 r hr3 he
        have hTailValue := hTail.2.2.2 r hr3
        have hMemory : mid.mem = state.mem := hHead.2.1
        rw [hMemory, hValue] at hTailValue
        exact hTailValue

theorem hintLoadFields_length (fields : List (Fin 16 × ℕ)) :
    (hintLoadFields fields).length = 3 * fields.length := by
  induction fields with
  | nil => rfl
  | cons pair rest ih =>
      change (hintLoadField pair.1 pair.2 ++ hintLoadFields rest).length = _
      rw [List.length_append, ih]
      change 3 + 3 * rest.length = 3 * (rest.length + 1)
      omega

theorem hintLoadFields_noBranch (fields : List (Fin 16 × ℕ)) : NoBranch (hintLoadFields fields) := by
  induction fields with
  | nil => trivial
  | cons pair rest ih =>
      change NoBranch (hintLoadField pair.1 pair.2 ++ hintLoadFields rest)
      rw [upNoBranch_append]
      exact ⟨by simp [hintLoadField, NoBranch, Instr.NoBranchI], ih⟩

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

/-- This is ordinary private RAM metadata, separate from the paper's det wire. -/
structure HintGaussArea where
  context : ℕ
  rows : ℕ
  hints : ℕ
  residual : ℕ
  lift : ℕ
  column : ℕ
  residualVec : ℕ
  kernelVec : ℕ
  pivotRow : ℕ
  hintList : ℕ
  node : ℕ
  row : ℕ
  buckets : ℕ
  steps : ℕ

def hintGaussHeaderValue (G : HintGaussArea) (j : ℕ) : ℕ → ℕ
  | 0 => G.rows
  | 1 => G.hints
  | 2 => G.residual
  | 3 => G.lift
  | 4 => G.column
  | 5 => G.residualVec
  | 6 => G.kernelVec
  | 7 => G.pivotRow
  | 8 => j
  | 9 => G.hintList
  | 10 => G.node
  | 11 => G.row
  | 12 => G.buckets
  | 13 => G.steps
  | _ => 0

def HintGaussHeader (G : HintGaussArea) (j : ℕ) (memory : ℕ → ℕ) : Prop :=
  ∀ i < 14, memory (G.context + i) = hintGaussHeaderValue G j i

structure HintGaussHeaderFits (E : RAMEnv) (G : HintGaussArea) (j : ℕ) : Prop where
  span : G.context + 14 < 2 ^ E.W
  values : ∀ i < 14, hintGaussHeaderValue G j i < 2 ^ E.W

theorem hintGaussHeader_mod (E : RAMEnv) (G : HintGaussArea) (j : ℕ) (memory : ℕ → ℕ)
    (hHeader : HintGaussHeader G j memory) (hFits : HintGaussHeaderFits E G j) :
    ∀ i < 14, memory (G.context + i) % 2 ^ E.W = hintGaussHeaderValue G j i := by
  intro i hi
  rw [hHeader i hi, Nat.mod_eq_of_lt (hFits.values i hi)]

def hintGaussSetupTail : List Instr := [.imm 7 1, .imm 15 1]

def hintGaussResidualFields : List (Fin 16 × ℕ) := [(4, 4), (5, 2), (6, 0), (8, 5), (13, 0)]
def hintGaussResidualSetup : List Instr := hintLoadFields hintGaussResidualFields ++ hintGaussSetupTail
theorem hintGaussResidualSetup_length : hintGaussResidualSetup.length = 17 := rfl

theorem hintGaussResidualSetup_spec (E : RAMEnv) (G : HintGaussArea) (j : ℕ) (state : RAMState)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G j state.mem)
    (hFits : HintGaussHeaderFits E G j) (hWord : 1 < 2 ^ E.W) :
    let out := runBlock hintGaussResidualSetup E state
    HintMatVecSetup G.residual G.column G.residualVec G.rows G.rows out ∧ out.mem = state.mem ∧ out.regs 14 = G.context := by
  have hValid : ∀ pair ∈ hintGaussResidualFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussResidualFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussResidualFields state hContext hValid
  have hValues := hintGaussHeader_mod E G j state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussResidualFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G j 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G j 4 := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [hintGaussResidualFields, hintLoadedValue, if_pos, if_neg, show (4 : Fin 16) = 4 from rfl,
      hZero, hValues 2 (by decide), hValues 4 (by decide), hValues 5 (by decide)] using hh
  have hR5 : mid.regs 5 = hintGaussHeaderValue G j 2 := by
    have hh := hLoad.2.2.2 5 (by decide)
    simpa [hintGaussResidualFields, hintLoadedValue, if_pos, if_neg, show (5 : Fin 16) = 5 from rfl,
      hZero, hValues 2 (by decide), hValues 4 (by decide), hValues 5 (by decide)] using hh
  have hR6 : mid.regs 6 = hintGaussHeaderValue G j 0 := by
    have hh := hLoad.2.2.2 6 (by decide)
    simpa [hintGaussResidualFields, hintLoadedValue, if_pos, if_neg, show (6 : Fin 16) = 6 from rfl,
      hZero, hValues 2 (by decide), hValues 4 (by decide), hValues 5 (by decide)] using hh
  have hR8 : mid.regs 8 = hintGaussHeaderValue G j 5 := by
    have hh := hLoad.2.2.2 8 (by decide)
    simpa [hintGaussResidualFields, hintLoadedValue, if_pos, if_neg, show (8 : Fin 16) = 8 from rfl,
      hZero, hValues 2 (by decide), hValues 4 (by decide), hValues 5 (by decide)] using hh
  have hR13 : mid.regs 13 = hintGaussHeaderValue G j 0 := by
    have hh := hLoad.2.2.2 13 (by decide)
    simpa [hintGaussResidualFields, hintLoadedValue, if_pos, if_neg, show (13 : Fin 16) = 13 from rfl,
      hZero, hValues 2 (by decide), hValues 4 (by decide), hValues 5 (by decide)] using hh
  dsimp only
  rw [hintGaussResidualSetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [hintGaussSetupTail, runBlock, execInstr, hR4, hR5, hR6, hR8, hR13,
      hintGaussHeaderValue, Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1]

def hintGaussLiftFields : List (Fin 16 × ℕ) := [(4, 4), (5, 3), (6, 0), (8, 6), (13, 1)]
def hintGaussLiftSetup : List Instr := hintLoadFields hintGaussLiftFields ++ hintGaussSetupTail
theorem hintGaussLiftSetup_length : hintGaussLiftSetup.length = 17 := rfl

theorem hintGaussLiftSetup_spec (E : RAMEnv) (G : HintGaussArea) (j : ℕ) (state : RAMState)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G j state.mem)
    (hFits : HintGaussHeaderFits E G j) (hWord : 1 < 2 ^ E.W) :
    let out := runBlock hintGaussLiftSetup E state
    HintMatVecSetup G.lift G.column G.kernelVec G.rows G.hints out ∧ out.mem = state.mem ∧ out.regs 14 = G.context := by
  have hValid : ∀ pair ∈ hintGaussLiftFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussLiftFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussLiftFields state hContext hValid
  have hValues := hintGaussHeader_mod E G j state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussLiftFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G j 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G j 4 := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [hintGaussLiftFields, hintLoadedValue, if_pos, if_neg, show (4 : Fin 16) = 4 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 4 (by decide), hValues 6 (by decide)] using hh
  have hR5 : mid.regs 5 = hintGaussHeaderValue G j 3 := by
    have hh := hLoad.2.2.2 5 (by decide)
    simpa [hintGaussLiftFields, hintLoadedValue, if_pos, if_neg, show (5 : Fin 16) = 5 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 4 (by decide), hValues 6 (by decide)] using hh
  have hR6 : mid.regs 6 = hintGaussHeaderValue G j 0 := by
    have hh := hLoad.2.2.2 6 (by decide)
    simpa [hintGaussLiftFields, hintLoadedValue, if_pos, if_neg, show (6 : Fin 16) = 6 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 4 (by decide), hValues 6 (by decide)] using hh
  have hR8 : mid.regs 8 = hintGaussHeaderValue G j 6 := by
    have hh := hLoad.2.2.2 8 (by decide)
    simpa [hintGaussLiftFields, hintLoadedValue, if_pos, if_neg, show (8 : Fin 16) = 8 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 4 (by decide), hValues 6 (by decide)] using hh
  have hR13 : mid.regs 13 = hintGaussHeaderValue G j 1 := by
    have hh := hLoad.2.2.2 13 (by decide)
    simpa [hintGaussLiftFields, hintLoadedValue, if_pos, if_neg, show (13 : Fin 16) = 13 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 4 (by decide), hValues 6 (by decide)] using hh
  dsimp only
  rw [hintGaussLiftSetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [hintGaussSetupTail, runBlock, execInstr, hR4, hR5, hR6, hR8, hR13,
      hintGaussHeaderValue, Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1]

def hintGaussRankResidualFields : List (Fin 16 × ℕ) := [(4, 2), (5, 7), (6, 0), (7, 5), (13, 0)]
def hintGaussRankResidualSetup : List Instr := hintLoadFields hintGaussRankResidualFields ++ [.imm 15 1]
theorem hintGaussRankResidualSetup_length : hintGaussRankResidualSetup.length = 16 := rfl

theorem hintGaussRankResidualSetup_spec (E : RAMEnv) (G : HintGaussArea) (j : ℕ) (state : RAMState)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G j state.mem)
    (hFits : HintGaussHeaderFits E G j) (hWord : 1 < 2 ^ E.W) :
    let out := runBlock hintGaussRankResidualSetup E state
    HintRankOneSetup G.residual G.pivotRow G.residualVec G.rows G.rows out ∧ out.mem = state.mem ∧ out.regs 14 = G.context := by
  have hValid : ∀ pair ∈ hintGaussRankResidualFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussRankResidualFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussRankResidualFields state hContext hValid
  have hValues := hintGaussHeader_mod E G j state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussRankResidualFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G j 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G j 2 := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [hintGaussRankResidualFields, hintLoadedValue, if_pos, if_neg, show (4 : Fin 16) = 4 from rfl,
      hZero, hValues 2 (by decide), hValues 5 (by decide), hValues 7 (by decide)] using hh
  have hR5 : mid.regs 5 = hintGaussHeaderValue G j 7 := by
    have hh := hLoad.2.2.2 5 (by decide)
    simpa [hintGaussRankResidualFields, hintLoadedValue, if_pos, if_neg, show (5 : Fin 16) = 5 from rfl,
      hZero, hValues 2 (by decide), hValues 5 (by decide), hValues 7 (by decide)] using hh
  have hR6 : mid.regs 6 = hintGaussHeaderValue G j 0 := by
    have hh := hLoad.2.2.2 6 (by decide)
    simpa [hintGaussRankResidualFields, hintLoadedValue, if_pos, if_neg, show (6 : Fin 16) = 6 from rfl,
      hZero, hValues 2 (by decide), hValues 5 (by decide), hValues 7 (by decide)] using hh
  have hR7 : mid.regs 7 = hintGaussHeaderValue G j 5 := by
    have hh := hLoad.2.2.2 7 (by decide)
    simpa [hintGaussRankResidualFields, hintLoadedValue, if_pos, if_neg, show (7 : Fin 16) = 7 from rfl,
      hZero, hValues 2 (by decide), hValues 5 (by decide), hValues 7 (by decide)] using hh
  have hR13 : mid.regs 13 = hintGaussHeaderValue G j 0 := by
    have hh := hLoad.2.2.2 13 (by decide)
    simpa [hintGaussRankResidualFields, hintLoadedValue, if_pos, if_neg, show (13 : Fin 16) = 13 from rfl,
      hZero, hValues 2 (by decide), hValues 5 (by decide), hValues 7 (by decide)] using hh
  dsimp only
  rw [hintGaussRankResidualSetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [hintGaussSetupTail, runBlock, execInstr, hR4, hR5, hR6, hR7, hR13,
      hintGaussHeaderValue, Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1]

def hintGaussRankLiftFields : List (Fin 16 × ℕ) := [(4, 3), (5, 7), (6, 0), (7, 6), (13, 1)]
def hintGaussRankLiftSetup : List Instr := hintLoadFields hintGaussRankLiftFields ++ [.imm 15 1]
theorem hintGaussRankLiftSetup_length : hintGaussRankLiftSetup.length = 16 := rfl

theorem hintGaussRankLiftSetup_spec (E : RAMEnv) (G : HintGaussArea) (j : ℕ) (state : RAMState)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G j state.mem)
    (hFits : HintGaussHeaderFits E G j) (hWord : 1 < 2 ^ E.W) :
    let out := runBlock hintGaussRankLiftSetup E state
    HintRankOneSetup G.lift G.pivotRow G.kernelVec G.rows G.hints out ∧ out.mem = state.mem ∧ out.regs 14 = G.context := by
  have hValid : ∀ pair ∈ hintGaussRankLiftFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintGaussRankLiftFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintGaussRankLiftFields state hContext hValid
  have hValues := hintGaussHeader_mod E G j state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintGaussRankLiftFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G j 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G j 3 := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [hintGaussRankLiftFields, hintLoadedValue, if_pos, if_neg, show (4 : Fin 16) = 4 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 6 (by decide), hValues 7 (by decide)] using hh
  have hR5 : mid.regs 5 = hintGaussHeaderValue G j 7 := by
    have hh := hLoad.2.2.2 5 (by decide)
    simpa [hintGaussRankLiftFields, hintLoadedValue, if_pos, if_neg, show (5 : Fin 16) = 5 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 6 (by decide), hValues 7 (by decide)] using hh
  have hR6 : mid.regs 6 = hintGaussHeaderValue G j 0 := by
    have hh := hLoad.2.2.2 6 (by decide)
    simpa [hintGaussRankLiftFields, hintLoadedValue, if_pos, if_neg, show (6 : Fin 16) = 6 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 6 (by decide), hValues 7 (by decide)] using hh
  have hR7 : mid.regs 7 = hintGaussHeaderValue G j 6 := by
    have hh := hLoad.2.2.2 7 (by decide)
    simpa [hintGaussRankLiftFields, hintLoadedValue, if_pos, if_neg, show (7 : Fin 16) = 7 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 6 (by decide), hValues 7 (by decide)] using hh
  have hR13 : mid.regs 13 = hintGaussHeaderValue G j 1 := by
    have hh := hLoad.2.2.2 13 (by decide)
    simpa [hintGaussRankLiftFields, hintLoadedValue, if_pos, if_neg, show (13 : Fin 16) = 13 from rfl,
      hZero, hValues 1 (by decide), hValues 3 (by decide), hValues 6 (by decide), hValues 7 (by decide)] using hh
  dsimp only
  rw [hintGaussRankLiftSetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    simp [hintGaussSetupTail, runBlock, execInstr, hR4, hR5, hR6, hR7, hR13,
      hintGaussHeaderValue, Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintGaussResidualSetup_spec
#print axioms LinearSetReconciliation327.Main.hintGaussLiftSetup_spec
#print axioms LinearSetReconciliation327.Main.hintGaussRankResidualSetup_spec
#print axioms LinearSetReconciliation327.Main.hintGaussRankLiftSetup_spec


