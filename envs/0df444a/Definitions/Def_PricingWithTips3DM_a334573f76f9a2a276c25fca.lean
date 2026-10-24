-- Prove2me | Definitions.Def_PricingWithTips3DM_a334573f76f9a2a276c25fca
-- name    : PricingWithTips3DM_a334573f76f9a2a276c25fca
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T03:18:43.358737+00:00
-- url     : https://prove2.me/theorems/95fd2aa2-63d9-4afc-96dc-5534cb454745
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineHeadControllerSource
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_6986319a00044f1dceca69fb
import Definitions.Def_PricingWithTips3DM_437c204810c3cbe698cd91bd
import Definitions.Def_PricingWithTips3DM_1b942700d84b7e3bcd2471a6
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Delimiter-exact controller source for fixed affine statement heads

The numeric head descriptor carries one marked row per transition seed.  For
a nonempty fixed phase table, a cyclic delimiter pass materializes the exact
tagged statement-controller frames and preserves the outer row marker.  The
empty table used by `halt` already consists solely of those outer markers.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Delimiter-exact affine-head controller frames, retaining one additional
outer marker after each complete seed-local head. -/
noncomputable def verifierTransitionAffineHeadControllerMarkedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm)
    (input : List Γ) : List UnaryFrameSym :=
  if hphases : phases = [] then
    encodeUnaryFrameMarkedRowFamily
      (verifierTransitionAffineFormDescriptorFamily W [] input)
  else
    rewriteUnaryFrameDelimiters
      (transitionAffineStmtScriptDelimiters phases)
      (transitionAffineStmtScriptDelimiters_nonempty hphases)
      (encodeUnaryFrameMarkedRowFamily
        (verifierTransitionAffineFormDescriptorFamily W
          (transitionAffineStmtScriptFieldForms phases) input))

/-- Exact seed-major semantics of affine-head delimiter materialization. -/
theorem verifierTransitionAffineHeadControllerMarkedFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm)
    (input : List Γ) :
    verifierTransitionAffineHeadControllerMarkedFrames W phases input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        transitionStmtAffineFormsControllerFrames seed phases ++
          [.frameEnd] := by
  by_cases hphases : phases = []
  · subst phases
    unfold verifierTransitionAffineHeadControllerMarkedFrames
      verifierTransitionAffineFormDescriptorFamily
      encodeUnaryFrameMarkedRowFamily
      transitionStmtAffineFormsControllerFrames
    simp only [dite_true]
    rw [List.flatMap_map]
    generalize verifierTransitionRowSeeds W input = seeds
    induction seeds with
    | nil => rfl
    | cons seed seeds ih =>
        have htail :
            (seeds.flatMap fun seed =>
                encodeUnaryFrame
                    (affineUnaryTripleMap []
                      (transitionTailAffineSeed seed)) ++
                  [.frameEnd]) =
              (seeds.flatMap fun seed =>
                encodeAffineStmtControllerScript [] ++
                  [.frameEnd]) := by
          exact ih
        simpa [affineUnaryTripleMap, encodeUnaryFrame,
          encodeAffineStmtControllerScript] using
            congrArg (List.cons UnaryFrameSym.frameEnd) htail
  · rw [verifierTransitionAffineHeadControllerMarkedFrames]
    simp only [hphases, ↓reduceDIte]
    let rows := (verifierTransitionRowSeeds W input).map fun seed =>
      affineUnaryTripleMap
        (transitionAffineStmtScriptFieldForms phases)
        (transitionTailAffineSeed seed)
    have hlength : ∀ row ∈ rows,
        row.length =
          (transitionAffineStmtScriptDelimiters phases).length := by
      intro row hrow
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      simpa [affineUnaryTripleMap] using
        transitionAffineStmtScript_lengths phases
    have hrewrite := rewriteUnaryFrameDelimiters_markedRows
      (transitionAffineStmtScriptDelimiters phases)
      (transitionAffineStmtScriptDelimiters_nonempty hphases)
      rows hlength
    have hinput :
        encodeUnaryFrameMarkedRowFamily
            (verifierTransitionAffineFormDescriptorFamily W
              (transitionAffineStmtScriptFieldForms phases) input) =
          rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd] := by
      unfold encodeUnaryFrameMarkedRowFamily
        verifierTransitionAffineFormDescriptorFamily
      simp [rows, List.flatMap_map]
    rw [hinput, hrewrite]
    unfold rows
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro seed hseed
    rw [transitionAffineStmtScriptForms_fixed_encoding]
    rfl

/-- Concrete polynomial-time TM2 for every fixed affine head, including the
empty `halt` head. -/
noncomputable def
    verifierTransitionAffineHeadControllerMarkedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (phases : List TransitionAffineStmtPhaseForm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineHeadControllerMarkedFrames W phases) := by
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
          simpa only [id_eq,
            verifierTransitionAffineHeadControllerMarkedFrames, dite_true]
            using run }
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
    let delimited := unaryFrameDelimiterMap_computableInPolyTime
      (transitionAffineStmtScriptDelimiters phases)
      (transitionAffineStmtScriptDelimiters_nonempty hphases)
    let composed :=
      _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch sourceRaw
        delimited
    let result := Classical.choice composed
    exact
      { tm := result.tm
        inputAlphabet := result.inputAlphabet
        outputAlphabet := result.outputAlphabet
        time := result.time
        outputsFun := fun input => by
          have run := result.outputsFun input
          simpa only [Function.comp_def, id_eq,
            verifierTransitionAffineHeadControllerMarkedFrames, hphases,
            dite_false] using run }

end CLRS.Chapter34.Turing.CookLevin


