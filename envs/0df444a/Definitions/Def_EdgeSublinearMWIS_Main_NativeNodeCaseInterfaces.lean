-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeNodeCaseInterfaces
-- name    : EdgeSublinearMWIS_Main_NativeNodeCaseInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T12:26:00.535108+00:00
-- url     : https://prove2.me/theorems/a135e52b-3851-481f-bb20-41b9c4cc0b03
-- title:
--   Saved recursive frames and child-execution interface
-- statement:
--   These definitions expose the word encoding of saved recursive frames and the child-execution relation used by the native MWIS node protocol. Saved frames contain the prescribed scalar and buffer contents. The child relation quantifies over each eligible induced component and target, with its actual machine-segment, answer and frame-preservation obligations. In particular, the interface records
--   $$\text{every eligible child has the specified bounded operational execution}. $$
--   It is an explicit hypothesis for a large-node composition theorem; the induction theorem subsequently supplies that hypothesis. No new transition rule or freely assigned clock is introduced.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/tree/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs — NativeFrameBuffers.lean (words), NativeFrameScalars.lean (words), NativeRecursionFrame.lean (words), NativeCollectionChild.lean (Recursive), NativeNodeProtocol.lean (Children).

import Definitions.Def_EdgeSublinearMWIS_Main_NativeCertificateInterfaces

-- Solutions.RAM_Lax263307Proofs_NativeFrameBuffers
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFrameBuffers

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def words (names : List String) (σ : Env) : List ℕ := names.flatMap σ.arrs












end Lax263307Proofs.NativeFrameBuffers

end

-- Solutions.RAM_Lax263307Proofs_NativeFrameScalars
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFrameScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def words (names : List String) (σ : Env) : List ℕ := names.map σ.vars







end Lax263307Proofs.NativeFrameScalars

end

-- Solutions.RAM_Lax263307Proofs_NativeRecursionFrame
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRecursionFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def words (arrays scalars : List String) (σ : Env) : List ℕ :=
  NativeFrameBuffers.words arrays σ++NativeFrameScalars.words scalars σ














end Lax263307Proofs.NativeRecursionFrame

end

-- Solutions.RAM_Lax263307Proofs_NativeCollectionChild
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCollectionChild

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeMasks



/-- Recursive execution required only at the actual child entry. -/
def Recursive {n : ℕ} (B S fuel childSteps childTime : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (target : ℕ) (front : List ℕ) (σ : Env) (answer : Option (Finset (Fin C.card))) : Prop :=
  ∀ saved entry,
      Run B (.seq NativeChildGraph.command (go 12)) σ saved (36*(C.card*C.card)+12) →
      Segment B (phases cfg) 1
        ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36) σ entry →
      Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" entry →
      entry.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length →
      Prefix (NativeWeightReduction.adjacency (ComputedSeparators.restriction G C)) "search.graph" entry →
      entry.vars "graph.n"=C.card → entry.vars "node.k"=target → entry.vars "recursion.fuel"=fuel →
      entry.vars "machine.running"=1 → entry.vars "machine.phase"=1 →
      ∃ done steps total,Segment B (phases cfg) steps total entry done ∧ steps≤ childSteps ∧ total≤ childTime ∧
        NativeRoundTrace.Stopped answer done ∧
        Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" done ∧
        done.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length ∧
        done.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length ∧ done.vars "recursion.stride"=S



end Lax263307Proofs.NativeCollectionChild

end

-- Solutions.RAM_Lax263307Proofs_NativeNodeProtocol
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNodeProtocol

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext



























def Children {n : ℕ} (B D fuel S v childSteps childTime : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (extent : String → ℕ) (front : List ℕ)
    (eligible : Eligible) (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) : Prop :=
  ∀ C target σ,eligible fuel C.card (ComputedSeparators.restriction G C) target
      (front.length+S*(frameArrays cfg).length+(frameScalars cfg).length) →
    Protocol B D S v cfg extent front σ → σ.vars "machine.phase"=11 →
    NativeCollectionChild.Recursive B S fuel childSteps childTime cfg G C target front σ (child C target)



end Lax263307Proofs.NativeNodeProtocol

end


