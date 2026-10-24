-- Prove2me | Definitions.Def_PricingWithTips3DM_e54fd9f21278f9dc24c110df
-- name    : PricingWithTips3DM_e54fd9f21278f9dc24c110df
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:25:12.667976+00:00
-- url     : https://prove2.me/theorems/68fab1c0-5e52-41d9-b026-a44e96a0c894
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameUnquoteSimulation
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_fc044af4e5ea7dd381bd01dc
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact simulation of quoted-row decoding
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev unquoteStep := step unaryFrameUnquoteRevProgram

/-- Exact number of controller steps on every total-decoder branch. -/
def unaryFrameUnquoteSteps : List UnaryFrameSym → Nat
  | [] => 2
  | .frameEnd :: tail => tail.length + 3
  | [.tick] => 3
  | .tick :: .tick :: rest => 3 + unaryFrameUnquoteSteps rest
  | .tick :: .separator :: rest => 3 + unaryFrameUnquoteSteps rest
  | .tick :: .frameEnd :: tail => tail.length + 4
  | [.separator] => 3
  | .separator :: .tick :: rest => 3 + unaryFrameUnquoteSteps rest
  | .separator :: .separator :: tail => tail.length + 4
  | .separator :: .frameEnd :: tail => tail.length + 4

/-- Draining an ignored suffix clears the input buffer and halts cleanly. -/
private def unaryFrameUnquote_drain_run
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    EvalsToInTime unquoteStep
      (unaryFrameUnquoteCfg .drain buffer input output)
      (some (haltCfg unaryFrameUnquoteRevProgram output))
      (input.length + 2) := by
  induction input generalizing buffer with
  | nil => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | cons symbol rest ih =>
      have hfirst : EvalsToInTime unquoteStep
          (unaryFrameUnquoteCfg .drain buffer (symbol :: rest) output)
          (some (unaryFrameUnquoteCfg .drain (some symbol) rest output)) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      let full := EvalsToInTime.trans unquoteStep 1 (rest.length + 2)
        _ (unaryFrameUnquoteCfg .drain (some symbol) rest output) _
        hfirst (ih (some symbol))
      convert full using 1 <;> simp <;> omega

/-- Exact contextual run of the total reverse-output decoder. -/
def unaryFrameUnquoteRev_context
    (buffer : Option UnaryFrameSym) (input output : List UnaryFrameSym) :
    EvalsToInTime unquoteStep
      (unaryFrameUnquoteCfg .scan buffer input output)
      (some (haltCfg unaryFrameUnquoteRevProgram
        ((unquoteUnaryFrameStream input).reverse ++ output)))
      (unaryFrameUnquoteSteps input) := by
  induction input using List.twoStepInduction generalizing buffer output with
  | nil => exact ⟨⟨2, rfl⟩, le_rfl⟩
  | singleton first => cases first <;> exact ⟨⟨3, rfl⟩, le_rfl⟩
  | cons_cons first second tail ih _ =>
      cases first with
      | frameEnd =>
          have hfirst : EvalsToInTime unquoteStep
              (unaryFrameUnquoteCfg .scan buffer
                (.frameEnd :: second :: tail) output)
              (some (unaryFrameUnquoteCfg .drain
                (some .frameEnd) (second :: tail) output)) 1 :=
            ⟨⟨1, rfl⟩, le_rfl⟩
          let full := EvalsToInTime.trans unquoteStep 1
            ((second :: tail).length + 2) _
            (unaryFrameUnquoteCfg .drain
              (some .frameEnd) (second :: tail) output) _ hfirst
            (unaryFrameUnquote_drain_run
              (some .frameEnd) (second :: tail) output)
          convert full using 1 <;>
            simp [unaryFrameUnquoteSteps, unquoteUnaryFrameStream] <;> omega
      | tick =>
          cases second with
          | tick =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameUnquoteCfg .scan buffer
                    (.tick :: .tick :: tail) output)
                  (some (unaryFrameUnquoteCfg .scan (some .tick) tail
                    (.tick :: output))) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 3
                (unaryFrameUnquoteSteps tail) _
                (unaryFrameUnquoteCfg .scan (some .tick) tail
                  (.tick :: output)) _ hprefix
                (ih (some .tick) (.tick :: output))
              convert full using 1 <;>
                simp [unaryFrameUnquoteSteps, unquoteUnaryFrameStream,
                  List.reverse_cons, List.append_assoc] <;> omega
          | separator =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameUnquoteCfg .scan buffer
                    (.tick :: .separator :: tail) output)
                  (some (unaryFrameUnquoteCfg .scan (some .separator) tail
                    (.separator :: output))) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 3
                (unaryFrameUnquoteSteps tail) _
                (unaryFrameUnquoteCfg .scan (some .separator) tail
                  (.separator :: output)) _ hprefix
                (ih (some .separator) (.separator :: output))
              convert full using 1 <;>
                simp [unaryFrameUnquoteSteps, unquoteUnaryFrameStream,
                  List.reverse_cons, List.append_assoc] <;> omega
          | frameEnd =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameUnquoteCfg .scan buffer
                    (.tick :: .frameEnd :: tail) output)
                  (some (unaryFrameUnquoteCfg .drain
                    (some .frameEnd) tail output)) 2 :=
                ⟨⟨2, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 2
                (tail.length + 2) _
                (unaryFrameUnquoteCfg .drain
                  (some .frameEnd) tail output) _ hprefix
                (unaryFrameUnquote_drain_run
                  (some .frameEnd) tail output)
              convert full using 1 <;>
                simp [unaryFrameUnquoteSteps,
                  unquoteUnaryFrameStream] <;> omega
      | separator =>
          cases second with
          | tick =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameUnquoteCfg .scan buffer
                    (.separator :: .tick :: tail) output)
                  (some (unaryFrameUnquoteCfg .scan (some .tick) tail
                    (.frameEnd :: output))) 3 := ⟨⟨3, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 3
                (unaryFrameUnquoteSteps tail) _
                (unaryFrameUnquoteCfg .scan (some .tick) tail
                  (.frameEnd :: output)) _ hprefix
                (ih (some .tick) (.frameEnd :: output))
              convert full using 1 <;>
                simp [unaryFrameUnquoteSteps, unquoteUnaryFrameStream,
                  List.reverse_cons, List.append_assoc] <;> omega
          | separator =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameUnquoteCfg .scan buffer
                    (.separator :: .separator :: tail) output)
                  (some (unaryFrameUnquoteCfg .drain
                    (some .separator) tail output)) 2 :=
                ⟨⟨2, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 2
                (tail.length + 2) _
                (unaryFrameUnquoteCfg .drain
                  (some .separator) tail output) _ hprefix
                (unaryFrameUnquote_drain_run
                  (some .separator) tail output)
              convert full using 1 <;>
                simp [unaryFrameUnquoteSteps,
                  unquoteUnaryFrameStream] <;> omega
          | frameEnd =>
              have hprefix : EvalsToInTime unquoteStep
                  (unaryFrameUnquoteCfg .scan buffer
                    (.separator :: .frameEnd :: tail) output)
                  (some (unaryFrameUnquoteCfg .drain
                    (some .frameEnd) tail output)) 2 :=
                ⟨⟨2, rfl⟩, le_rfl⟩
              let full := EvalsToInTime.trans unquoteStep 2
                (tail.length + 2) _
                (unaryFrameUnquoteCfg .drain
                  (some .frameEnd) tail output) _ hprefix
                (unaryFrameUnquote_drain_run
                  (some .frameEnd) tail output)
              convert full using 1 <;>
                simp [unaryFrameUnquoteSteps,
                  unquoteUnaryFrameStream] <;> omega

/-- Canonical exact decoder run. -/
def unaryFrameUnquoteRev_run (input : List UnaryFrameSym) :
    EvalsToInTime unquoteStep
      (initialCfg unaryFrameUnquoteRevProgram input)
      (some (haltCfg unaryFrameUnquoteRevProgram
        (unquoteUnaryFrameStream input).reverse))
      (unaryFrameUnquoteSteps input) := by
  change EvalsToInTime unquoteStep
    (unaryFrameUnquoteCfg .scan none input []) _ _
  simpa using unaryFrameUnquoteRev_context none input []

/-- The total decoder is uniformly linear in its physical input length. -/
theorem unaryFrameUnquoteSteps_le (input : List UnaryFrameSym) :
    unaryFrameUnquoteSteps input ≤ 3 * input.length + 3 := by
  induction input using List.twoStepInduction with
  | nil => simp [unaryFrameUnquoteSteps]
  | singleton first => cases first <;> simp [unaryFrameUnquoteSteps]
  | cons_cons first second tail ih _ =>
      cases first <;> cases second <;>
        simp [unaryFrameUnquoteSteps] <;> omega

end CLRS.Chapter34.Turing.PolyBuilder


