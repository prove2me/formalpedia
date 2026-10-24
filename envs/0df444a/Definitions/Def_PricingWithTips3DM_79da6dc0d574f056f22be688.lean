-- Prove2me | Definitions.Def_PricingWithTips3DM_79da6dc0d574f056f22be688
-- name    : PricingWithTips3DM_79da6dc0d574f056f22be688
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T04:07:04.368816+00:00
-- url     : https://prove2.me/theorems/dc4183cf-4828-4019-9b3c-85600a0a118b
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineHeadQuotedRowSource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a334573f76f9a2a276c25fca
import Definitions.Def_PricingWithTips3DM_4b1286992e63c1b9c246e220
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Delimiter-safe row source for affine statement heads

Each transition seed receives one quoted controller-script row.  Unlike the
earlier raw controller stream, literal `frameEnd`s inside the script are
quoted, while the seed-row boundary stays literal.  The resulting family can
be combined pointwise with recursive child sources.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One delimiter-safe quoted affine-head payload per transition seed. -/
noncomputable def verifierTransitionAffineHeadQuotedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm)
    (input : List Γ) : UnaryFrameMarkedRowFamily where
  rows := (verifierTransitionRowSeeds W input).map fun seed =>
    quoteUnaryFrameStream
      (transitionStmtAffineFormsControllerFrames seed phases)
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rw [List.mem_map] at hrow
    rcases hrow with ⟨seed, hseed, rfl⟩
    exact quoteUnaryFrameStream_frameEnd_free _ symbol hsymbol

/-- Public row semantics of the quoted affine-head family. -/
@[simp] theorem verifierTransitionAffineHeadQuotedFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm)
    (input : List Γ) :
    (verifierTransitionAffineHeadQuotedFamily W phases input).rows =
      (verifierTransitionRowSeeds W input).map fun seed =>
        quoteUnaryFrameStream
          (transitionStmtAffineFormsControllerFrames seed phases) := rfl

/-- The combined fixed-delimiter/quotation pass has the exact marked-family
semantics required by the recursive row assembler. -/
theorem verifierTransitionAffineHeadQuoted_rewrite
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm)
    (hphases : phases ≠ []) (input : List Γ) :
    rewriteUnaryFrameQuotedDelimiters
        (transitionAffineStmtScriptDelimiters phases)
        (transitionAffineStmtScriptDelimiters_nonempty hphases)
        (encodeUnaryFrameMarkedRowFamily
          (verifierTransitionAffineFormDescriptorFamily W
            (transitionAffineStmtScriptFieldForms phases) input)) =
      encodeUnaryFrameMarkedRowFamily
        (verifierTransitionAffineHeadQuotedFamily W phases input) := by
  let rows := (verifierTransitionRowSeeds W input).map fun seed =>
    affineUnaryTripleMap
      (transitionAffineStmtScriptFieldForms phases)
      (transitionTailAffineSeed seed)
  have hlength : ∀ row ∈ rows,
      row.length = (transitionAffineStmtScriptDelimiters phases).length := by
    intro row hrow
    rw [List.mem_map] at hrow
    rcases hrow with ⟨seed, hseed, rfl⟩
    simpa [affineUnaryTripleMap] using
      transitionAffineStmtScript_lengths phases
  have hrewrite := rewriteUnaryFrameQuotedDelimiters_markedRows
    (transitionAffineStmtScriptDelimiters phases)
    (transitionAffineStmtScriptDelimiters_nonempty hphases)
    rows hlength
  have hsource :
      encodeUnaryFrameMarkedRowFamily
          (verifierTransitionAffineFormDescriptorFamily W
            (transitionAffineStmtScriptFieldForms phases) input) =
        rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd] := by
    simp [verifierTransitionAffineFormDescriptorFamily,
      encodeUnaryFrameMarkedRowFamily, rows, List.flatMap_map]
  have htarget :
      encodeUnaryFrameMarkedRowFamily
          (verifierTransitionAffineHeadQuotedFamily W phases input) =
        (verifierTransitionRowSeeds W input).flatMap fun seed =>
          quoteUnaryFrameStream
              (transitionStmtAffineFormsControllerFrames seed phases) ++
            [.frameEnd] := by
    unfold encodeUnaryFrameMarkedRowFamily
    rw [verifierTransitionAffineHeadQuotedFamily_rows, List.flatMap_map]
  rw [hsource, hrewrite]
  dsimp [rows]
  rw [List.flatMap_map, htarget]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionAffineStmtScriptForms_fixed_encoding]
  rfl

/-- A fixed polynomial-time TM2 emits quoted affine-head rows directly from
the raw verifier input, including the empty head of `halt`. -/
noncomputable def
    verifierTransitionAffineHeadQuotedFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionAffineHeadQuotedFamily W phases) := by
  by_cases hphases : phases = []
  · subst phases
    let source :=
      verifierTransitionAffineFormDescriptorFamilyTotal_computableInPolyTime
        W []
    exact
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun input => by
          have run := source.outputsFun input
          simpa [verifierTransitionAffineHeadQuotedFamily,
            verifierTransitionAffineFormDescriptorFamily,
            transitionStmtAffineFormsControllerFrames,
            affineUnaryTripleMap, encodeUnaryFrame,
            encodeAffineStmtControllerScript] using run }
  · let source :=
      verifierTransitionAffineFormDescriptorFamilyTotal_computableInPolyTime
        W (transitionAffineStmtScriptFieldForms phases)
    let sourceRaw : _root_.Turing.TM2ComputableInPolyTime id id
        (fun input => encodeUnaryFrameMarkedRowFamily
          (verifierTransitionAffineFormDescriptorFamily W
            (transitionAffineStmtScriptFieldForms phases) input)) :=
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun input => by
          simpa only [id_eq] using source.outputsFun input }
    let materializer := unaryFrameQuotedDelimiterMap_computableInPolyTime
      (transitionAffineStmtScriptDelimiters phases)
      (transitionAffineStmtScriptDelimiters_nonempty hphases)
    let composed :=
      _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch sourceRaw
        materializer
    let result := Classical.choice composed
    exact
      { tm := result.tm
        inputAlphabet := result.inputAlphabet
        outputAlphabet := result.outputAlphabet
        time := result.time
        outputsFun := fun input => by
          have run := result.outputsFun input
          simp only [Function.comp_apply, id_eq] at run
          rw [verifierTransitionAffineHeadQuoted_rewrite W phases hphases
            input] at run
          exact run }

/-- Typed seed-row source used by the recursive statement construction. -/
noncomputable def verifierTransitionAffineHeadQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm) :
    VerifierTransitionSeedRowSource W where
  row := fun seed => quoteUnaryFrameStream
    (transitionStmtAffineFormsControllerFrames seed phases)
  family := verifierTransitionAffineHeadQuotedFamily W phases
  rows_eq := verifierTransitionAffineHeadQuotedFamily_rows W phases
  computableInPolyTime :=
    verifierTransitionAffineHeadQuotedFamily_computableInPolyTime W phases

end CLRS.Chapter34.Turing.CookLevin


