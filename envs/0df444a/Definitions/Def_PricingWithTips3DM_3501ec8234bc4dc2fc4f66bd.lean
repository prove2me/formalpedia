-- Prove2me | Definitions.Def_PricingWithTips3DM_3501ec8234bc4dc2fc4f66bd
-- name    : PricingWithTips3DM_3501ec8234bc4dc2fc4f66bd
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:28:40.426391+00:00
-- url     : https://prove2.me/theorems/2cc71ea1-37e0-4958-aea1-5add98eff285
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowQuotedDelimiterMapSimulation
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_f5a947acd4786694aefa1167
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Exact simulation of quoted delimiter materialization
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Exact instruction count.  Payload symbols use one pop and two output
pushes; a reserved row boundary uses one pop and one output push. -/
def unaryFrameQuotedDelimiterMapSteps : List UnaryFrameSym → Nat
  | [] => 2
  | .tick :: rest => unaryFrameQuotedDelimiterMapSteps rest + 3
  | .separator :: rest => unaryFrameQuotedDelimiterMapSteps rest + 3
  | .frameEnd :: rest => unaryFrameQuotedDelimiterMapSteps rest + 2

/-- Exact run from any cyclic delimiter position and any accumulated reversed
output. -/
def unaryFrameQuotedDelimiterMap_scan_run
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (index : Fin delimiters.length)
    (buffer : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty))
      (unaryFrameQuotedDelimiterMapCfg delimiters hnonempty (.scan index)
        buffer input output)
      (some (haltCfg
        (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty)
        ((rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty index
          input).reverse ++ output)))
      (unaryFrameQuotedDelimiterMapSteps input) := by
  induction input generalizing index buffer output with
  | nil =>
      refine ⟨⟨2, ?_⟩, le_rfl⟩
      rfl
  | cons symbol rest ih =>
      cases symbol with
      | tick =>
          let afterPop := unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
            (.emitFirst index .tick) (some .tick) rest output
          let afterFirst := unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
            (.emitSecond index .tick) (some .tick) rest
              (quoteUnaryFrameFirst .tick :: output)
          let afterSecond := unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
            (.scan index) (some .tick) rest
              (quoteUnaryFrameSecond .tick ::
                quoteUnaryFrameFirst .tick :: output)
          have hpop : EvalsToInTime
              (step (unaryFrameQuotedDelimiterMapRevProgram delimiters
                hnonempty))
              (unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
                (.scan index) buffer (.tick :: rest) output)
              (some afterPop) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
          have hfirst : EvalsToInTime
              (step (unaryFrameQuotedDelimiterMapRevProgram delimiters
                hnonempty)) afterPop (some afterFirst) 1 :=
            ⟨⟨1, rfl⟩, le_rfl⟩
          have hsecond : EvalsToInTime
              (step (unaryFrameQuotedDelimiterMapRevProgram delimiters
                hnonempty)) afterFirst (some afterSecond) 1 :=
            ⟨⟨1, rfl⟩, le_rfl⟩
          have htail := ih index (some .tick)
            (quoteUnaryFrameSecond .tick ::
              quoteUnaryFrameFirst .tick :: output)
          let h₁ := EvalsToInTime.trans _ 1 1 _ afterPop _ hpop hfirst
          let h₂ := EvalsToInTime.trans _ 2 1 _ afterFirst _ h₁ hsecond
          let full := EvalsToInTime.trans _ 3
            (unaryFrameQuotedDelimiterMapSteps rest) _ afterSecond _ h₂
              htail
          convert full using 1 <;>
            simp [afterSecond, rewriteUnaryFrameQuotedDelimitersFrom,
              quoteUnaryFrameSym_eq_pair, List.reverse_append,
              List.append_assoc, unaryFrameQuotedDelimiterMapSteps] <;>
            omega
      | separator =>
          let nextIndex :=
            unaryFrameDelimiterNext delimiters hnonempty index
          let materialized := delimiters.get index
          let afterPop := unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
            (.emitFirst nextIndex materialized) (some .separator) rest output
          let afterFirst := unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
            (.emitSecond nextIndex materialized) (some .separator) rest
              (quoteUnaryFrameFirst materialized :: output)
          let afterSecond := unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
            (.scan nextIndex) (some .separator) rest
              (quoteUnaryFrameSecond materialized ::
                quoteUnaryFrameFirst materialized :: output)
          have hpop : EvalsToInTime
              (step (unaryFrameQuotedDelimiterMapRevProgram delimiters
                hnonempty))
              (unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
                (.scan index) buffer (.separator :: rest) output)
              (some afterPop) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
          have hfirst : EvalsToInTime
              (step (unaryFrameQuotedDelimiterMapRevProgram delimiters
                hnonempty)) afterPop (some afterFirst) 1 :=
            ⟨⟨1, rfl⟩, le_rfl⟩
          have hsecond : EvalsToInTime
              (step (unaryFrameQuotedDelimiterMapRevProgram delimiters
                hnonempty)) afterFirst (some afterSecond) 1 :=
            ⟨⟨1, rfl⟩, le_rfl⟩
          have htail := ih nextIndex (some .separator)
            (quoteUnaryFrameSecond materialized ::
              quoteUnaryFrameFirst materialized :: output)
          let h₁ := EvalsToInTime.trans _ 1 1 _ afterPop _ hpop hfirst
          let h₂ := EvalsToInTime.trans _ 2 1 _ afterFirst _ h₁ hsecond
          let full := EvalsToInTime.trans _ 3
            (unaryFrameQuotedDelimiterMapSteps rest) _ afterSecond _ h₂
              htail
          convert full using 1 <;>
            simp [afterSecond, nextIndex, materialized,
              rewriteUnaryFrameQuotedDelimitersFrom,
              quoteUnaryFrameSym_eq_pair, List.reverse_append,
              List.append_assoc, unaryFrameQuotedDelimiterMapSteps] <;>
            omega
      | frameEnd =>
          let afterPop := unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
            (.emitBoundary index) (some .frameEnd) rest output
          let afterBoundary :=
            unaryFrameQuotedDelimiterMapCfg delimiters hnonempty (.scan index)
              (some .frameEnd) rest (.frameEnd :: output)
          have hpop : EvalsToInTime
              (step (unaryFrameQuotedDelimiterMapRevProgram delimiters
                hnonempty))
              (unaryFrameQuotedDelimiterMapCfg delimiters hnonempty
                (.scan index) buffer (.frameEnd :: rest) output)
              (some afterPop) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
          have hboundary : EvalsToInTime
              (step (unaryFrameQuotedDelimiterMapRevProgram delimiters
                hnonempty)) afterPop (some afterBoundary) 1 :=
            ⟨⟨1, rfl⟩, le_rfl⟩
          have htail := ih index (some .frameEnd) (.frameEnd :: output)
          let hprefix := EvalsToInTime.trans _ 1 1 _ afterPop _ hpop
            hboundary
          let full := EvalsToInTime.trans _ 2
            (unaryFrameQuotedDelimiterMapSteps rest) _ afterBoundary _
              hprefix htail
          convert full using 1 <;>
            simp [afterBoundary, rewriteUnaryFrameQuotedDelimitersFrom,
              List.append_assoc, unaryFrameQuotedDelimiterMapSteps] <;>
            omega

/-- Exact reversed-output run from the public initial configuration. -/
def unaryFrameQuotedDelimiterMapRev_run
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (input : List UnaryFrameSym) :
    EvalsToInTime
      (step (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty))
      (initialCfg
        (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty) input)
      (some (haltCfg
        (unaryFrameQuotedDelimiterMapRevProgram delimiters hnonempty)
        (rewriteUnaryFrameQuotedDelimiters delimiters hnonempty input).reverse))
      (unaryFrameQuotedDelimiterMapSteps input) := by
  simpa [initialCfg, rewriteUnaryFrameQuotedDelimiters,
    unaryFrameQuotedDelimiterMapRevProgram,
    unaryFrameQuotedDelimiterMapCfg] using
      unaryFrameQuotedDelimiterMap_scan_run delimiters hnonempty
        ⟨0, hnonempty⟩ none input []

end CLRS.Chapter34.Turing.PolyBuilder


