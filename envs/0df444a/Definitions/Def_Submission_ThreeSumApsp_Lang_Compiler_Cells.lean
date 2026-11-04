-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Cells
-- name    : Submission_ThreeSumApsp_Lang_Compiler_Cells
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:04:11.808828+00:00
-- url     : https://prove2.me/theorems/59996163-d1e1-4330-9385-573f9644eb0a
-- title:
--   Cells
-- statement:
--   Definitions and structural lemmas for Cells, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/Cells.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StatementCode
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr)
structure Fits (W : ℕ) (lim : Limits) (N Q : ℕ) : Prop where
  word : 2 * (2 * lim.word + 2) < (2 : ℤ) ^ W
  space : 2 * (lim.space : ℤ) < (2 : ℤ) ^ W
  stack : 2 * (2 * (Q : ℤ)) < (2 : ℤ) ^ W
  pool_lt : 2 * (N : ℤ) < (2 : ℤ) ^ W
structure Sizes (W : ℕ) extends CodeLayout where
  /-- The limits on the runs of the light program. -/
  lim : Limits
  /-- The number of stack cells. -/
  Q : ℕ
  /-- The word size fits the limits, the pool and the stack. -/
  fits : Fits W lim disp Q
  /-- The pool holds the numbers up to 2 (F + 1), which are the offsets in a frame. -/
  offsets_le : 2 * (F + 1) ≤ disp
def Temps (k F : ℕ) : Set ℤ := {a | a = cADDR ∨ ∃ j, k ≤ j ∧ j ≤ 2 * F ∧ a = cT j}
def Stack (q Q : ℕ) : Set ℤ := {a | ∃ j, q ≤ j ∧ j < Q ∧ a = cStack j}
def MainFrame (F : ℕ) : Set ℤ := Stack mainFrame (mainFrame + F)
def Pool (N : ℕ) : Set ℤ := {a | ∃ n, n ≤ N ∧ a = cPool n}
def Constants (N : ℕ) : Set ℤ := {cONE, cZERO, cNEG} ∪ Pool N
def Scratch (F : ℕ) : Set ℤ := {cD, cRET, cRR, cNFP} ∪ Temps 0 F
def Writable {W : ℕ} (Z : Sizes W) (q : ℕ) : Set ℤ :=
  Scratch Z.F ∪ {cFP} ∪ Stack q Z.Q ∪ {a | 0 ≤ a ∧ a < Z.lim.space}
theorem mem_temps_iff {k F : ℕ} {a : ℤ} :
    a ∈ Temps k F ↔ a = cADDR ∨ cT (2 * F) ≤ a ∧ a ≤ cT k ∧ 4 ∣ cT 0 - a := by
  simp only [Temps, cT, Set.mem_ofPred_eq]
  refine or_congr_right ⟨?_, fun h => ⟨((-23 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨j, hk, hj, rfl⟩
    omega
  · omega
theorem mem_stack_iff {q Q : ℕ} {a : ℤ} :
    a ∈ Stack q Q ↔ cStack Q < a ∧ a ≤ cStack q ∧ 2 ∣ a := by
  simp only [Stack, cStack, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨(-a / 2).toNat, ?_⟩⟩
  · rintro ⟨j, hq, hj, rfl⟩
    omega
  · omega
theorem mem_pool_iff {N : ℕ} {a : ℤ} :
    a ∈ Pool N ↔ cPool N ≤ a ∧ a ≤ cPool 0 ∧ 4 ∣ cPool 0 - a := by
  simp only [Pool, cPool, Set.mem_ofPred_eq]
  refine ⟨?_, fun h => ⟨((-25 - a) / 4).toNat, ?_⟩⟩
  · rintro ⟨n, hn, rfl⟩
    omega
  · omega



variable {W : ℕ} {Z : Sizes W} {F : ℕ}
structure Rel (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  one : m cONE = wd W 1
  zero : m cZERO = wd W 0
  neg : m cNEG = wd W (-1)
  pool : ∀ n ≤ Z.disp, m (cPool n) = wd W n
  fp : m cFP = wd W (cStack q)
  loc : ∀ x < Z.F, m (cStack (q + x)) = wd W (σ.loc x)
  mem : ∀ a < Z.lim.space, m (a : ℤ) = wd W (σ.mem a)
section Rel
variable {σ σ' : State} {q q' : ℕ} {m m' : ℤ → BitVec W}
end Rel
structure Framed (Z : Sizes W) (σ : State) (q : ℕ) (m : ℤ → BitVec W) : Prop where
  rel : Rel Z σ q m
  low : 1 ≤ q
  high : q + Z.F ≤ Z.Q
section code
variable {σ : State} {q pos : ℕ} {m m' : ℤ → BitVec W} {code rest : List Instr}
end code
end Light.Compiler


