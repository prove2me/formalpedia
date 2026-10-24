-- Prove2me | Definitions.Def_PricingWithTips3DM_048074518e2d97cbf6f67793
-- name    : PricingWithTips3DM_048074518e2d97cbf6f67793
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:37:07.409153+00:00
-- url     : https://prove2.me/theorems/51ea236c-31bd-43be-bec5-6eedc3ca8b63
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Selector.Run
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_559bc85b391ed65ee6a0a876
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# VERTEX-COVER complement machine: complete selector run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter.Selector

open PolyBuilder
open NonedgeFilter

def iterationsSteps : List (Nat × Nat) → List Bool → Nat
  | edge :: edges, bit :: bits =>
      1 + selectSteps bit edge + iterationsSteps edges bits
  | _, _ => 2

private def final_run (output : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .nextBit buffer₁ buffer₂ test [] output [] [])
      (some (haltCfg program output)) 2 := by
  exact ⟨⟨2, by
    simp [Function.iterate_succ_apply, flip, step, program, cfg, stepOp,
      haltCfg]⟩, le_rfl⟩

private def nextBit_run (bit : Bool) (bits : List Bool)
    (output : List CliqueSym) (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .nextBit buffer₁ buffer₂ test
        (some (selectorBitSymbol bit) :: (bits.map selectorBitSymbol).map some)
        output work₁ work₂)
      (some (cfg (.select bit) (some (some (selectorBitSymbol bit))) buffer₂ test
        ((bits.map selectorBitSymbol).map some) output work₁ work₂)) 1 := by
  cases bit <;>
    exact ⟨⟨1, by simp [flip, step, program, cfg, stepOp, selectorBitSymbol]⟩,
      le_rfl⟩

/-- Process equally many candidate records and answer bits. -/
def iterations_run (edges : List (Nat × Nat)) (bits : List Bool)
    (hlength : edges.length = bits.length)
    (output : List CliqueSym)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg .nextBit buffer₁ buffer₂ test
        ((bits.map selectorBitSymbol).map some) output
        ((edges.flatMap encodeCliqueEdge).map some) [])
      (some (haltCfg program
        ((selectedStream edges bits).reverse ++ output)))
      (iterationsSteps edges bits) := by
  induction edges generalizing bits output buffer₁ buffer₂ test with
  | nil =>
      cases bits with
      | nil =>
          simpa [iterationsSteps, selectedStream, selectedEdges] using
            final_run output buffer₁ buffer₂ test
      | cons bit bits => simp at hlength
  | cons edge edges ih =>
      cases bits with
      | nil => simp at hlength
      | cons bit bits =>
          have htail : edges.length = bits.length := by
            simpa using hlength
          have first := nextBit_run bit bits output
            ((encodeCliqueEdge edge).map some ++
              (edges.flatMap encodeCliqueEdge).map some) []
            buffer₁ buffer₂ test
          have selected := select_run bit edge
            ((bits.map selectorBitSymbol).map some) output
            ((edges.flatMap encodeCliqueEdge).map some) []
            (some (some (selectorBitSymbol bit))) buffer₂ test
          have remaining := ih bits htail
            (if bit then output else (encodeCliqueEdge edge).reverse ++ output)
            (some (some CliqueSym.recordEnd)) buffer₂ test
          let throughSelect := EvalsToInTime.trans (step program)
            1 (selectSteps bit edge) _ _ _ first selected
          let full := EvalsToInTime.trans (step program)
            (selectSteps bit edge + 1) (iterationsSteps edges bits)
            _ _ _ throughSelect remaining
          cases bit <;>
            simpa [iterationsSteps, selectedStream, selectedEdges,
              List.reverse_append, List.append_assoc, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using full

def selectorSteps (edges : List (Nat × Nat)) (bits : List Bool) : Nat :=
  (edges.flatMap encodeCliqueEdge).length + 2 +
    iterationsSteps edges bits

/-- Exact complete execution of the fixed selector. -/
def run (edges : List (Nat × Nat)) (bits : List Bool)
    (hlength : edges.length = bits.length) :
    EvalsToInTime (step program)
      (initialCfg program (inputEncoding (edges, bits)))
      (some (haltCfg program (selectedReverseStream edges bits)))
      (selectorSteps edges bits) := by
  have loaded := load_run edges bits
  have selected := iterations_run edges bits hlength []
    (some none) none false
  let full := EvalsToInTime.trans (step program)
    ((edges.flatMap encodeCliqueEdge).length + 2)
    (iterationsSteps edges bits) _ _ _ loaded selected
  simpa [selectorSteps, selectedReverseStream, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter.Selector


