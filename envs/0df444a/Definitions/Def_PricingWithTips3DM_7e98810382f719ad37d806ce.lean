-- Prove2me | Definitions.Def_PricingWithTips3DM_7e98810382f719ad37d806ce
-- name    : PricingWithTips3DM_7e98810382f719ad37d806ce
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:59:34.893614+00:00
-- url     : https://prove2.me/theorems/d93832b1-1a02-4550-a60a-cfc1df31139e
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorHalfDuplicate
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_aaab3594e8025ebfe65392cc
import Definitions.Def_PricingWithTips3DM_645fa74d60687a6229a5303d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Duplicating both routed dispatch-mux descriptor halves

The first routing stage produces an arm-descriptor row followed by a
selector/coordinate row for every transition seed.  This module duplicates
each physical row, preparing four independently transformable channels for
the descriptor interpreter.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem encodeUnaryFrame_frameEnd_free (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  simp only [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with (⟨hvalue, rfl⟩ | rfl) <;> simp

/-- The two descriptor halves of every seed as a typed marked-row family. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorHalfRowFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierTransitionRowSeeds W input).flatMap fun seed =>
      [ encodeUnaryFrame
          (transitionDispatchMuxInvocationDescriptorTailValues
            W.machine.tm seed),
        encodeUnaryFrame
          (transitionDispatchMuxInvocationDescriptorHeadValues
            W.machine.tm seed) ]
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_flatMap] at hrow
      rcases hrow with ⟨seed, hseed, hrow⟩
      simp at hrow
      rcases hrow with rfl | rfl
      · exact encodeUnaryFrame_frameEnd_free _ symbol hsymbol
      · exact encodeUnaryFrame_frameEnd_free _ symbol hsymbol }

/-- The typed marked-row encoding is exactly the routed two-half stream. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorHalfRowFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionDispatchMuxInvocationDescriptorHalfRowFamily
          W input) =
      verifierTransitionDispatchMuxInvocationDescriptorHalfRows W input := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorHalfRows_eq]
  unfold encodeUnaryFrameMarkedRowFamily
    verifierTransitionDispatchMuxInvocationDescriptorHalfRowFamily
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  simp [List.append_assoc]

/-- Four physical rows per transition seed: two arm-section copies followed
by two selector/coordinate-section copies. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameDuplicatedMarkedRowFamily
    (verifierTransitionDispatchMuxInvocationDescriptorHalfRowFamily W input)

/-- Exact seed-major shape of the four-row stream. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        let tail := encodeUnaryFrame
          (transitionDispatchMuxInvocationDescriptorTailValues
            W.machine.tm seed)
        let head := encodeUnaryFrame
          (transitionDispatchMuxInvocationDescriptorHeadValues
            W.machine.tm seed)
        tail ++ [.frameEnd] ++ tail ++ [.frameEnd] ++
          head ++ [.frameEnd] ++ head ++ [.frameEnd] := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows
    encodeUnaryFrameDuplicatedMarkedRowFamily
    verifierTransitionDispatchMuxInvocationDescriptorHalfRowFamily
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  simp [List.append_assoc]

/-- The raw descriptor source through four-row duplication remains one
continuous polynomial-time TM2 pipeline. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorDuplicatedHalfRows
        W) := by
  let source :=
    verifierTransitionDispatchMuxInvocationDescriptorHalfRows_computableInPolyTime
      W
  let typedSource : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionDispatchMuxInvocationDescriptorHalfRowFamily W) :=
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        have run := source.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorHalfRowFamily_encoding_eq
            W input] using run }
  let duplicated :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch typedSource
      unaryFrameMarkedRowDuplicate_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      encodeUnaryFrameDuplicatedMarkedRowFamily
        (verifierTransitionDispatchMuxInvocationDescriptorHalfRowFamily
          W input))
  simpa [Function.comp_def] using Classical.choice duplicated

end CLRS.Chapter34.Turing.CookLevin


