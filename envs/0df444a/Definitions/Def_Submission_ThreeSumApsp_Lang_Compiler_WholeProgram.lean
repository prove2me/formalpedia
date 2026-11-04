-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
-- name    : Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T11:21:14.861126+00:00
-- url     : https://prove2.me/theorems/4d027b4d-1650-48ce-965e-53165e4a3fcb
-- title:
--   Whole Program
-- statement:
--   Definitions and structural lemmas for Whole Program, from the weighted-cache deterministic 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Compiler/WholeProgram.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_Simulation
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_StartUp
import Theorems.Thm_Light_Compiler_codeAt_bodies
import Theorems.Thm_Light_Compiler_codeAt_bodiesCode
import Theorems.Thm_Light_Compiler_codeAt_dispatcher_dispPos
import Theorems.Thm_Light_Compiler_two_mul_frameSize_add_le_dispPos
import Theorems.Thm_Light_Compiler_width_le_frameSize
import Definitions.Def_WeightedCache3SUM_Alias_e0bdc711e9667f3c
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil


set_option autoImplicit false
section
open ThreeSumApsp.WordRam
namespace Light.Compiler
open EndStatement (Instr exec)
variable {W : ℕ}
def _root_.Light.verdictOf (dec : Bool) (r : ℤ) : Bool := !dec || decide (0 < r)
structure Verdict (code : List Instr) (dec : Bool) (r : ℤ) (m : ℤ → BitVec W)
    (cfg : Cfg W) : Prop where
  verdict : step code cfg = .inr (verdictOf dec r)
  result : cfg.mem cRESULT = wd W r
  agree : AgreeOutside {cRESULT, cD} m cfg.mem
def startCost (P : Program) (dec : Bool) : ℕ := dispPos P dec + frameSize P + 13
def _root_.Light.ramSteps (P : Program) (dec : Bool) (c : ℕ) : ℕ :=
  startCost P dec + stepsPerStep (dispPos P dec) * c
def stackCells (P : Program) (lim : Limits) : ℕ :=
  mainFrame + (frameSize P + 1) * (lim.depth + 1)
def lowCell (P : Program) (dec : Bool) (lim : Limits) : ℕ :=
  max (2 * stackCells P lim) (25 + 4 * dispPos P dec)
section setting
variable {lim : Limits} {P : Program} {p0 : ℕ} {dec : Bool}
def setting (P : Program) (p0 : ℕ) (dec : Bool)
    (hfit : Fits W lim (dispPos P dec) (stackCells P lim)) : Setting W where
  toCodeLayout := codeLayout P dec
  lim := lim
  Q := stackCells P lim
  fits := hfit
  offsets_le := by
    have := two_mul_frameSize_add_le_dispPos P dec
    simp only [codeLayout]
    omega
  P := P
  code := compileProgram P p0 dec
  bodyAt := codeAt_bodies (codeLayout P dec) P _ (codeAt_bodiesCode P p0 dec)
  dispatcherAt := codeAt_dispatcher_dispPos P p0 dec
  width _ hb := width_le_frameSize hb
variable (hfit : Fits W lim (dispPos P dec) (stackCells P lim))
end setting
structure Holds (W : ℕ) (lim : Limits) (μ : ℕ → ℤ) (m : ℤ → BitVec W) : Prop where
  rep : ∀ a : ℕ, m (a : ℤ) = wd W (μ a)
  bounded : ∀ a, |μ a| ≤ lim.word
structure Input (lim : Limits) (μ : ℕ → ℤ) (i j : ℤ) (m : ℤ → BitVec W) : Prop
    extends Holds W lim μ m where
  arg1 : m cARG1 = wd W i
  arg2 : m cARG2 = wd W j
  arg1_le : |i| ≤ lim.word
  arg2_le : |j| ≤ lim.word
structure Outcome (lim : Limits) (P : Program) (dec : Bool) (m : ℤ → BitVec W) (σ' : State)
    (m' : ℤ → BitVec W) : Prop where
  /-- The cells 0, 1, 2, … hold the final memory. -/
  holds : Holds W lim σ'.mem m'
  /-- The cell for the result holds the result. -/
  result : (m' cRESULT).toInt = σ'.loc 0
  /-- The first argument is still there. -/
  arg1 : m' cARG1 = m cARG1
  /-- The second argument is still there. -/
  arg2 : m' cARG2 = m cARG2
  /-- The cells far below 0 and the cells from lim.space on are unchanged. -/
  far : ∀ a : ℤ, a < -(lowCell P dec lim : ℤ) ∨ (lim.space : ℤ) ≤ a → m' a = m a
end Light.Compiler


