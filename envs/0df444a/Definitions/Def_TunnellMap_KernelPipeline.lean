-- Prove2me | Definitions.Def_TunnellMap_KernelPipeline
-- name    : TunnellMap_KernelPipeline
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:07:16.049906+00:00
-- url     : https://prove2.me/theorems/406579b4-5b29-48f1-a1a6-0e5336c947d7
-- title:
--   Kernel Pipeline
-- statement:
--   Definitions and structural lemmas for Kernel Pipeline, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelPipeline.lean

import Definitions.Def_TunnellMap_KernelGenerator
import Definitions.Def_TunnellMap_ComputablePipeline
set_option autoImplicit true
namespace TunnellMap
namespace BlockGen
variable {n : ℤ} {s : BResidual n}
end BlockGen
namespace RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
def frameExecK (hsq : Squarefree n) (s : BResidual n) :
    OrthogonalFrame (tau (residualSourceLift s)) :=
  reduceFrameK (orthogonalFrameExec (tau (residualSourceLift s))
    (tripleGCD_tau_residualSourceLift hsq s))
def framesExecK (hsq : Squarefree n) : FrameFamily n := frameExecK hsq
def stepK (frames : FrameFamily n) (E : DARun n) : Option (DARun n) :=
  match E.queue with
  | [] => none
  | s :: rest =>
      if s ∈ E.sources then
        match BlockGen.advanceK s (frames s) (E.gen s) with
        | none => none
        | some (r, g) =>
            match E.held r.target with
            | none =>
                some { E with
                  queue := rest
                  gen := Function.update E.gen s g
                  held := Function.update E.held r.target (some (s, r))
                  assigned := Function.update E.assigned s (some r) }
            | some (old, rold) =>
                if r.key < rold.key then
                  some { E with
                    queue := rest ++ [old]
                    gen := Function.update E.gen s g
                    held := Function.update E.held r.target (some (s, r))
                    assigned := Function.update
                      (Function.update E.assigned old none) s (some r) }
                else
                  some { E with
                    queue := rest ++ [s]
                    gen := Function.update E.gen s g }
      else none
def GenStarted (E : DARun n) : Prop := ∀ s : BResidual n, 1 ≤ (E.gen s).nextBlock
def runK (frames : FrameFamily n) : ℕ → DARun n → DARun n
  | 0, E => E
  | fuel + 1, E =>
      match stepK frames E with
      | none => E
      | some E' => runK frames fuel E'
end RecordDA
end TunnellMap


