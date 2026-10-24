-- Prove2me | Definitions.Def_PricingWithTips3DM_9d0f307f00b2056cbb09edb9
-- name    : PricingWithTips3DM_9d0f307f00b2056cbb09edb9
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:24:05.352547+00:00
-- url     : https://prove2.me/theorems/e6a159ee-0a18-468a-a207-a631e8c6a155
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionFamilyScript
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_89e84f871ac233a733dec4b6
import Definitions.Def_PricingWithTips3DM_cd3f6329cc4418a6bb3bc852
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Canonical runtime script for the complete transition family

This module mirrors the semantic adjacent-row recursion and extracts one
`AffineTransitionScript` per local transition.  The resulting runtime data is
proved byte-for-byte equal to the frozen dimension-only transition stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin
open StateTransition

/-- Extract the canonical local operand script for every adjacent tableau-row
pair, in the same prefix order as `transitionCircuitFamilyGateTrace`. -/
def compileTransitionFamilyScripts
    (tm : _root_.Turing.FinTM2) (H : Nat) (base : CircuitBuilder) :
    (T : Nat) → (rows : Fin (T + 1) → CfgWires tm H) →
      (∀ row, (rows row).ValidIn base) → List AffineTransitionScript
  | 0, _, _ => []
  | T + 1, rows, hrows =>
      let prefixRows : Fin (T + 1) → CfgWires tm H :=
        fun row => rows row.castSucc
      let hprefix : ∀ row, (prefixRows row).ValidIn base :=
        fun row => hrows row.castSucc
      let previous := transitionCircuitFamily tm H base prefixRows hprefix
      let currentRow : Fin (T + 2) := (Fin.last T).castSucc
      let nextRow : Fin (T + 2) := Fin.last (T + 1)
      let hcurrent : (rows currentRow).ValidIn previous.builder :=
        (hrows currentRow).mono previous.extension
      let hnext : (rows nextRow).ValidIn previous.builder :=
        (hrows nextRow).mono previous.extension
      compileTransitionFamilyScripts tm H base T prefixRows hprefix ++
        [compileTransitionScript tm H previous.builder
          (rows currentRow) (rows nextRow) hcurrent hnext]

@[simp] theorem compileTransitionFamilyScripts_length
    (tm : _root_.Turing.FinTM2) (H : Nat) (base : CircuitBuilder)
    (T : Nat) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (compileTransitionFamilyScripts tm H base T rows hrows).length = T := by
  induction T generalizing base with
  | zero => rfl
  | succ T ih =>
      simp only [compileTransitionFamilyScripts, List.length_append,
        List.length_singleton]
      rw [ih]

/-- The canonical family script denotes exactly the semantic transition-family
gate trace, including its byte encoding. -/
theorem compileTransitionFamilyScripts_gateStream_eq_trace
    (tm : _root_.Turing.FinTM2) (H : Nat) (base : CircuitBuilder)
    (T : Nat) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    affineTransitionFamilyGateStream
        (compileTransitionFamilyScripts tm H base T rows hrows) =
      (transitionCircuitFamilyGateTrace tm H base T rows hrows).flatMap
        encodeCircuitGate := by
  induction T generalizing base with
  | zero => rfl
  | succ T ih =>
      simp only [compileTransitionFamilyScripts,
        transitionCircuitFamilyGateTrace,
        affineTransitionFamilyGateStream, List.flatMap_append,
        List.flatMap_singleton]
      have hprefix :
          List.flatMap affineTransitionGateStream
              (compileTransitionFamilyScripts tm H base T
                (fun row => rows row.castSucc)
                (fun row => hrows row.castSucc)) =
            List.flatMap encodeCircuitGate
              (transitionCircuitFamilyGateTrace tm H base T
                (fun row => rows row.castSucc)
                (fun row => hrows row.castSucc)) := by
        simpa only [affineTransitionFamilyGateStream] using
          ih base (fun row => rows row.castSucc)
            (fun row => hrows row.castSucc)
      rw [hprefix]
      rw [compileTransitionScript_gateStream_eq_trace]

/-- Dimension-only canonical script following the already-frozen validity
builder. -/
def compileTransitionFamilyScriptsAt
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    List AffineTransitionScript :=
  let rows := arithmeticRowsAt tm H T
  let pool := arithmeticPoolAt tm H T
  let validity := arithmeticValidityAt tm H T
  compileTransitionFamilyScripts tm H validity.builder T rows.rows
    (fun row =>
      (rows.rowValid row).mono (pool.extension.trans validity.extension))

@[simp] theorem compileTransitionFamilyScriptsAt_length
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    (compileTransitionFamilyScriptsAt tm H T).length = T := by
  simp [compileTransitionFamilyScriptsAt]

/-- The dimension-only canonical script is byte-for-byte the already frozen
transition generator target. -/
theorem compileTransitionFamilyScriptsAt_gateStream_eq
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    affineTransitionFamilyGateStream
        (compileTransitionFamilyScriptsAt tm H T) =
      transitionGateStreamAt tm H T := by
  rw [transitionGateStreamAt_eq_trace]
  simpa [compileTransitionFamilyScriptsAt, transitionFamilyGateTraceAt,
    arithmeticRowsAt, arithmeticPoolAt, arithmeticValidityAt] using
    compileTransitionFamilyScripts_gateStream_eq_trace tm H
      (arithmeticValidityAt tm H T).builder T
      (arithmeticRowsAt tm H T).rows
      (fun row =>
        ((arithmeticRowsAt tm H T).rowValid row).mono
          ((arithmeticPoolAt tm H T).extension.trans
            (arithmeticValidityAt tm H T).extension))

/-- One fixed controller executes the canonical dimension-only transition
family and halts with precisely `transitionGateStreamAt`. -/
def compileTransitionFamilyScriptsAt_run
    (tm : _root_.Turing.FinTM2) (H T : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step affineTransitionFamilyRevProgram)
      (affineTransitionFamilyLoopCfg
        (encodeAffineTransitionFamily
          (compileTransitionFamilyScriptsAt tm H T)) output)
      (some (haltCfg affineTransitionFamilyRevProgram
        ((transitionGateStreamAt tm H T).reverse ++ output)))
      (affineTransitionFamilyTotalSteps
        (compileTransitionFamilyScriptsAt tm H T)) := by
  simpa [compileTransitionFamilyScriptsAt_gateStream_eq] using
    affineTransitionFamily_run
      (compileTransitionFamilyScriptsAt tm H T) output

/-- The canonical family run remains linear in its exact runtime encoding. -/
theorem compileTransitionFamilyScriptsAt_steps_le
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    affineTransitionFamilyTotalSteps
        (compileTransitionFamilyScriptsAt tm H T) ≤
      500 * (encodeAffineTransitionFamily
        (compileTransitionFamilyScriptsAt tm H T)).length + 2 :=
  affineTransitionFamily_steps_le
    (compileTransitionFamilyScriptsAt tm H T)

end CLRS.Chapter34.Turing.PolyBuilder


