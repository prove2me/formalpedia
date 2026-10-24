-- Prove2me | Definitions.Def_PricingWithTips3DM_07f3fdf8789b7e6fee3d53d4
-- name    : PricingWithTips3DM_07f3fdf8789b7e6fee3d53d4
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T01:21:29.585575+00:00
-- url     : https://prove2.me/theorems/c6e66d7d-a012-4c61-85fb-c774733308e9
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0a2631b4ea0c8335f9d3178e
import Definitions.Def_PricingWithTips3DM_97076553854002c477c77e28
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Label-marked execution of routed dispatch-mux coordinates

The routed coordinate descriptor channel contains exactly one affine triple
progression per fixed program label.  Executing it with the singleton fixed-
group controller therefore retains one physical `frameEnd` after every label,
instead of flattening those boundaries away.  These boundaries are the first
piece of state needed by the final four-channel mux-source assembler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A singleton fixed group marks the output of every progression. -/
theorem affineUnaryTripleProgressionFixedGroupZeroFrameStream_eq
    (progressions : List AffineUnaryTripleProgression) :
    affineUnaryTripleProgressionFixedGroupFrameStream 0 progressions =
      progressions.flatMap fun progression =>
        affineUnaryTripleProgressionFrameStream progression ++ [.frameEnd] := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      simp only [affineUnaryTripleProgressionFixedGroupFrameStream,
        affineUnaryTripleProgressionFixedGroupFrameStreamFrom,
        List.flatMap_cons]
      change affineUnaryTripleProgressionFrameStream progression ++
          .frameEnd ::
            affineUnaryTripleProgressionFixedGroupFrameStream 0 rest = _
      rw [ih]
      simp [List.append_assoc]

/-- Encode one semantic list of fresh-coordinate triples as an ordinary unary
frame row. -/
def transitionDispatchMuxCoordinateRowFrames
    (coordinates : List (Nat × Nat × Nat)) : List UnaryFrameSym :=
  coordinates.flatMap fun coordinate =>
    encodeUnaryFrame
      [coordinate.1, coordinate.2.1, coordinate.2.2]

/-- Execute the physically recovered coordinate descriptors while preserving
one boundary after every dispatch label. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  affineUnaryTripleProgressionFixedGroupFrameStream 0
    ((verifierTransitionRowSeeds W input).flatMap
      (transitionDispatchMuxAffineProgressions W.machine.tm))

/-- The physical stream consists of one marked coordinate row per affine
label progression. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
        W input =
      ((verifierTransitionRowSeeds W input).flatMap
        (transitionDispatchMuxAffineProgressions W.machine.tm)).flatMap
          fun progression =>
            affineUnaryTripleProgressionFrameStream progression ++
              [.frameEnd] := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
  exact affineUnaryTripleProgressionFixedGroupZeroFrameStream_eq _

/-- On verifier-produced seeds, every retained physical boundary is exactly a
semantic label boundary of the fresh-coordinate layout. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_eq_layouts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
        W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        (transitionDispatchMuxFreshLayoutsFromSeed W.machine.tm seed).flatMap
          fun layout =>
            transitionDispatchMuxCoordinateRowFrames layout.coordinates ++
              [.frameEnd] := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_eq]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  have hwork : 0 < workHeight W.machine.tm seed.height := by
    have hheight := verifierTransitionRowSeeds_height_eq W input seed hseed
    rw [hheight]
    unfold workHeight
    exact Nat.add_pos_left (verifierHeight_eval_pos W input.length) _
  have hrows := transitionDispatchMuxCoordinateProgressionGroups_values
    W.machine.tm seed hwork
  unfold transitionDispatchMuxCoordinateProgressionGroups at hrows
  simp only [List.map_map] at hrows
  have hencoded := congrArg
    (List.map fun coordinates =>
      transitionDispatchMuxCoordinateRowFrames coordinates ++ [.frameEnd])
    hrows
  have hflattened := congrArg List.flatten hencoded
  rw [List.flatten_eq_flatMap, List.flatMap_map] at hflattened
  simpa [transitionDispatchMuxCoordinateRowFrames,
    affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleRowValues, List.flatten_eq_flatMap,
    List.flatMap_map, Function.comp_def]
    using hflattened

/-- The unified four-way route, coordinate selection, descriptor recovery,
and label-marked execution form one concrete polynomial-time TM2 from the
original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames
        W) := by
  let descriptors :=
    verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames_computableInPolyTime
      W
  let structured : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleProgressionFamily
      (fun input =>
        (verifierTransitionRowSeeds W input).flatMap
          (transitionDispatchMuxAffineProgressions W.machine.tm)) :=
    { tm := descriptors.tm
      inputAlphabet := descriptors.inputAlphabet
      outputAlphabet := descriptors.outputAlphabet
      time := descriptors.time
      outputsFun := fun input => by
        have run := descriptors.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorCoordinateFrames_eq
            W input] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch structured
      (affineUnaryTripleProgressionFixedGroupFrameStream_computableInPolyTime 0)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorCoordinateLabelFrames]
          using run }

end CLRS.Chapter34.Turing.CookLevin


