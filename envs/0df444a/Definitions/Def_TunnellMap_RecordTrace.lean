-- Prove2me | Definitions.Def_TunnellMap_RecordTrace
-- name    : TunnellMap_RecordTrace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T16:08:22.123647+00:00
-- url     : https://prove2.me/theorems/0e46571c-8d0e-5363-b5c0-74cea3ea4c5e
-- title:
--   Record Trace
-- statement:
--   Definitions and structural lemmas for Record Trace, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean

import Definitions.Def_TunnellMap_KernelPipeline
set_option autoImplicit true
namespace TunnellMap
namespace RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
instance bRepDecidableEq (n : ℤ) : DecidableEq (BRep n) :=
  inferInstanceAs (DecidableEq {p : Triple // bForm p = n})
instance bResidualDecidableEq (n : ℤ) : DecidableEq (BResidual n) :=
  inferInstanceAs (DecidableEq {p : BOddRep n // ¬ DirectSourceUsed p})
inductive DAOutcome where
  /-- The target was free and the proposal was accepted. -/
  | accept : DAOutcome
  /-- The target was held by a worse record, which was displaced. -/
  | replace : DAOutcome
  /-- The target was held by a better record and the proposal was rejected. -/
  | reject : DAOutcome
  deriving DecidableEq, Repr
structure DAEvent (n : ℤ) where
  /-- The source that made the proposal. -/
  proposer : BResidual n
  /-- The lift of the target orbit representative that was proposed to. -/
  target : Triple
  /-- The projective key of the proposed edge. -/
  key : DirectionKey
  /-- The manuscript's sign `η` of the proposed edge. -/
  sign : ℤ
  /-- The outcome of the proposal. -/
  outcome : DAOutcome
  deriving DecidableEq
def stepTrace (frames : FrameFamily n) (E : DARun n) :
    Option (DAEvent n × DARun n) :=
  match E.queue with
  | [] => none
  | s :: rest =>
      if s ∈ E.sources then
        match BlockGen.advanceK s (frames s) (E.gen s) with
        | none => none
        | some (r, g) =>
            match E.held r.target with
            | none =>
                some (⟨s, r.target, r.key, r.sign, DAOutcome.accept⟩,
                  { E with
                    queue := rest
                    gen := Function.update E.gen s g
                    held := Function.update E.held r.target (some (s, r))
                    assigned := Function.update E.assigned s (some r) })
            | some (old, rold) =>
                if r.key < rold.key then
                  some (⟨s, r.target, r.key, r.sign, DAOutcome.replace⟩,
                    { E with
                      queue := rest ++ [old]
                      gen := Function.update E.gen s g
                      held := Function.update E.held r.target (some (s, r))
                      assigned := Function.update
                        (Function.update E.assigned old none) s (some r) })
                else
                  some (⟨s, r.target, r.key, r.sign, DAOutcome.reject⟩,
                    { E with
                      queue := rest ++ [s]
                      gen := Function.update E.gen s g })
      else none
def runWithTrace (frames : FrameFamily n) :
    ℕ → DARun n → DARun n × List (DAEvent n)
  | 0, E => (E, [])
  | fuel + 1, E =>
      match stepTrace frames E with
      | none => (E, [])
      | some (ev, E') =>
          let p := runWithTrace frames fuel E'
          (p.1, ev :: p.2)
end RecordDA
end TunnellMap


