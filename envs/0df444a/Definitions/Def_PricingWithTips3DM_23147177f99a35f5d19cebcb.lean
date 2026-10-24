-- Prove2me | Definitions.Def_PricingWithTips3DM_23147177f99a35f5d19cebcb
-- name    : PricingWithTips3DM_23147177f99a35f5d19cebcb
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T02:49:14.210428+00:00
-- url     : https://prove2.me/theorems/38d06f22-5589-434d-a046-71bac3d29584
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketAssemblerVerifier
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_9d60a4548308dd576bc2e422
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Verifier-level dispatch-mux packet assembly

This module instantiates the whole-family theorem with every label view derived
from every canonical verifier transition-row seed.  The result is an exact,
halting execution from the concrete prepared packet stream to the reverse of
the already verified dispatch-mux invocation source.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Seed-major list of every canonical dispatch-mux label view. -/
noncomputable def verifierTransitionDispatchMuxInvocationViews
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List TransitionDispatchMuxInvocationView :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    transitionDispatchMuxDescriptorInvocationViews W.machine.tm seed

/-- Every view in the complete verifier family satisfies the row-alignment
invariant required by the concrete assembler. -/
theorem verifierTransitionDispatchMuxInvocationViews_rowAligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ∀ view ∈ verifierTransitionDispatchMuxInvocationViews W input,
      view.RowAligned := by
  intro view hview
  rw [verifierTransitionDispatchMuxInvocationViews,
    List.mem_flatMap] at hview
  rcases hview with ⟨seed, hseed, hview⟩
  exact transitionDispatchMuxDescriptorInvocationViews_rowAligned
    W input seed hseed view hview

/-- Once all prepared labels are consumed, two control transitions enter the
actual halting configuration without changing the accumulated output. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_halt
    (output : List UnaryFrameSym) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg [] output)
      (some (haltCfg
        transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram output))
      2 := by
  exact ⟨⟨2, rfl⟩, le_rfl⟩

/-- Exact verifier-instance transition count, including the final halt. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
      (verifierTransitionDispatchMuxInvocationViews W input) + 2

/-- The concrete fixed assembler consumes the actual prepared verifier packet
stream, halts, and leaves exactly the reverse of the canonical dispatch-mux
invocation source on its output tape. -/
def verifierTransitionDispatchMuxInvocationLabelPacketAssembler_rev
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input) [])
      (some (haltCfg
        transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
        (verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
          W input).reverse))
      (verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps
        W input) := by
  let views := verifierTransitionDispatchMuxInvocationViews W input
  have hprepared :
      verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input =
        views.flatMap
          TransitionDispatchMuxInvocationView.preparedLabelPacketFrames := by
    simpa [views, verifierTransitionDispatchMuxInvocationViews] using
      verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames_eq
        W input
  have hsource :
      verifierTransitionDispatchMuxDescriptorInvocationSourceFrames W input =
        views.flatMap TransitionDispatchMuxInvocationView.sourceFrames := by
    rw [
      verifierTransitionDispatchMuxDescriptorInvocationSourceFrames_eq_reassembledViews]
    simp [views, verifierTransitionDispatchMuxInvocationViews,
      List.flatMap_assoc]
  have haligned : ∀ view ∈ views, view.RowAligned := by
    simpa [views] using
      verifierTransitionDispatchMuxInvocationViews_rowAligned W input
  have hfamily : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input) [])
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg []
        (verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
          W input).reverse))
      (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps
        views) := by
    simpa [hprepared, hsource] using
      transitionDispatchMuxInvocationLabelPacketAssembler_views_sourceFrames
        views [] [] haligned
  have hhalt :=
    transitionDispatchMuxInvocationLabelPacketAssembler_halt
      (verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
        W input).reverse
  let full := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    (transitionDispatchMuxInvocationLabelPacketAssemblerFamilySteps views)
    2 _
    (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg []
      (verifierTransitionDispatchMuxDescriptorInvocationSourceFrames
        W input).reverse)
    _ hfamily hhalt
  convert full using 1 <;>
    simp [verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps,
      views] <;>
    omega

/-- The same halting execution stated with the canonical invocation source
already consumed by the verified affine-mux controller. -/
def verifierTransitionDispatchMuxInvocationLabelPacketAssembler_rev_source
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (verifierTransitionDispatchMuxInvocationDescriptorPreparedLabelPacketFrames
          W input) [])
      (some (haltCfg
        transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
        (verifierTransitionDispatchMuxInvocationSourceFrames W input).reverse))
      (verifierTransitionDispatchMuxInvocationLabelPacketAssemblerSteps
        W input) := by
  simpa [verifierTransitionDispatchMuxDescriptorInvocationSourceFrames_eq]
    using
      verifierTransitionDispatchMuxInvocationLabelPacketAssembler_rev W input

end CLRS.Chapter34.Turing.CookLevin


