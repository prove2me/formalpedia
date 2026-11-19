-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeOracleInterfaces
-- name    : EdgeSublinearMWIS_Main_NativeOracleInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T12:53:01.536725+00:00
-- url     : https://prove2.me/theorems/58abca48-4dc9-4a6d-851f-2813ebac257c
-- title:
--   Native projection, oracle context and bounded-round execution interfaces
-- statement:
--   These interfaces describe the stored rational projection result, the complete native oracle context, and the resource setup for one oracle invocation and a bounded sequence of rounded updates. The context records the graph and moment data, storage lengths, stack frame and root data. The setup supplies the concrete projection call and the far and near branch bounds, including the executions required for recursive children.
--
--   For a round limit $L$, the interface specifies the actual command state and the uniform per-round resource data used to compose at most $L$ oracle calls. These are data and predicates; termination, correctness and the resulting step and time bounds are separate theorem obligations.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeOracleContext.lean; NativeOracleExecution.lean; NativeOracleRounds.lean; NativeProjectionResult.lean; NativeNearExecution.lean (definitions and setup structures)

import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Combinatorics.Colex
import Definitions.Def_EdgeSublinearMWIS_Main_NativeNodeCaseInterfaces

-- Solutions.RAM_Lax455465Proofs_RamRational
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-
Generic RAM utilities reused from the registered LP development, Apache-2.0:
https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864
Only namespaces and imports are adapted here. The LP solver itself is used
through its registered concept theorem, rather than its proof package.
-/

namespace Lax455465Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def fractionValue (s n d : ℕ) : ℚ := if s = 1 then -(n : ℚ) / d else (n : ℚ) / d

































end Lax455465Proofs.RamRational

end

-- Solutions.RAM_Lax263307Proofs_NativeSignedArithmetic
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeSignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational

/-- A reduced rational held in three ordinary RAM variables. Either sign
for zero is allowed, matching the registered exact arithmetic routines. -/
def Stored (name : String) (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars (name++".s")) (σ.vars (name++".n")) (σ.vars (name++".d"))=q ∧
    σ.vars (name++".n")=q.num.natAbs ∧ σ.vars (name++".d")=q.den ∧
    σ.vars (name++".s")≤1



















end Lax263307Proofs.NativeSignedArithmetic

end

-- Solutions.RAM_Lax263307_NativeCatalog
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Encoding the moment-coordinate catalogue
type: definition
---
The moment-coordinate catalogue lists subsets of the vertex set in the
order used by the relaxation. Each subset is represented by its binary
membership mask; `words` is the resulting list of masks.

# Formalization notes

Masks encode subsets of `Fin n`. The catalogue contains only the subsets
needed by the relaxation, rather than an array indexed by all $2^n$ masks.
-/

namespace Lax263307.NativeCatalog

open CoordinateCatalog (catalog)


def words (n r : ℕ) : List ℕ :=
  (catalog n r).map (fun A => subsetMask A.val)

end Lax263307.NativeCatalog

end

-- Solutions.RAM_Lax263307Proofs_NativeCatalogMetadata
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeCatalogMetadata

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307



def atIndex (n r : ℕ) (j : Fin (N n r)) : Finset (Fin n) := (CoordinateCatalog.indexing n r j).val

def cards (n r : ℕ) : List ℕ := List.ofFn fun j : Fin (N n r) => (atIndex n r j).card

def independent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) : List ℕ :=
  List.ofFn fun j : Fin (N n r) => if G.IsIndepSet (atIndex n r j : Set (Fin n)) then 1 else 0

def Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "catalog.count"=N n r ∧
  Prefix (Lax263307.NativeCatalog.words n r) "catalog.mask" σ ∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧ n≤(σ.arrs "subset.bits").length























end Lax263307Proofs.NativeCatalogMetadata

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentAccess
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentAccess

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 NativeCatalogMetadata

def Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ) (σ : Env) : Prop :=
  NativeCatalogMetadata.Data G r σ ∧ Prefix (cards n r) "catalog.card" σ ∧
  Prefix (independent G r) "catalog.independent" σ ∧ σ.vars "moment.r"=r

















end Lax263307Proofs.NativeMomentAccess

end

-- Solutions.RAM_Lax263307Proofs_NativeProjectionResult
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeProjectionResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection Lax263307.RationalProjection
open NativeSignedArithmetic



def CertificateBounded (M : ℕ) {m n : ℕ} : Certificate (m+(n+n)) (n+1) → Prop
  | .optimal z y => (∀ i,Bounded M (z i)) ∧ ∀ i,Bounded M (y i)
  | _ => True













end Lax263307Proofs.NativeProjectionResult

end

-- Solutions.RAM_Lax263307Proofs_NativeRestrictionOrder
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRestrictionOrder

open Lax263307








def words {n : ℕ} (R : Finset (Fin n)) : List ℕ :=
  List.ofFn fun i : Fin R.card => (ComputedSeparators.label R i).val











end Lax263307Proofs.NativeRestrictionOrder

end

-- Solutions.RAM_Lax263307Proofs_NativeRestrictionRead
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeRestrictionRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic

structure Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (σ : Env) : Prop where
  labels : Prefix (NativeRestrictionOrder.words R) "restrict.vertices" σ
  graph : Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  costs : Prefix (encodeVector x) "near.costs" σ
  count : σ.vars "restrict.count"=R.card
  order : σ.vars "graph.n"=n













end Lax263307Proofs.NativeRestrictionRead

end

-- Solutions.RAM_Lax263307Proofs_NativeRoundedTrace
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRoundedTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment

def StoredState {n : ℕ} (k : ℕ) (state : State n) (σ : Env) : Prop :=
  Prefix (NativeRoundedQuery.shape state) "round.shape" σ ∧
    Prefix (NativeRoundedQuery.center state) "round.center" σ ∧
    σ.vars "vec.n"=n ∧ σ.vars "round.i"=k


end Lax263307Proofs.NativeRoundedTrace

end

-- Solutions.RAM_Lax263307Proofs_NativeCollectionAnchor
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeCollectionAnchor

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeCoreMachine

/-- Only the parent's actual local work is excluded. Child activation is
not excluded: its changes must be undone by the checked stack restoration. -/
def workScalars : List String := excludedScalars++component.wvars++
  (Com.ite (.eq (.var "component.active") (.lit 1)) (go 11) (NativeComponentControl.advance 9)).wvars++
  (Com.seq NativeChildGraph.command (go 12)).wvars++(NativeComponentControl.childReply 9 13).wvars

def workArrays : List String := ["recursion.frames"]++component.warrs++
  (Com.ite (.eq (.var "component.active") (.lit 1)) (go 11) (NativeComponentControl.advance 9)).warrs++
  (Com.seq NativeChildGraph.command (go 12)).warrs++(NativeComponentControl.childReply 9 13).warrs

def Anchor (base σ : Env) : Prop :=
  (∀ s,s∉workScalars → σ.vars s=base.vars s) ∧
    (∀ a,a∉workArrays → σ.arrs a=base.arrs a)











end Lax263307Proofs.NativeCollectionAnchor

end

-- Solutions.RAM_Lax263307Proofs_NativeCollectionContext
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCollectionContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeMasks

/-- The actual parent data held fixed while collecting components. The
array extents and stack prefix are included, so this context can be used
at the next child call as well as at the final failed-component cut. -/
structure Context {n : ℕ} (B D k r fuel stride : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (parts : List (Finset (Fin n))) (A : Finset (Fin n))
    (extent : String → ℕ) (front : List ℕ) (σ : Env) : Prop where
  order : σ.vars "graph.n"=n
  graph : Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  costs : Prefix (encodeVector (fun v => (x v : ℚ))) "near.costs" σ
  pieces : Prefix (parts.map mask) "separator.pieces" σ
  count : σ.vars "component.count"=parts.length
  denominator : σ.vars "algorithm.D"=D
  target : σ.vars "conditioning.k"=k
  dimension : σ.vars "catalog.count"=NativeCatalogMetadata.N n r
  catalog : Prefix (NativeCatalog.words n r) "catalog.mask" σ
  conditioning : σ.vars "conditioning.choice"=mask A
  bounded : NativeStateBounds.Bounded B σ
  lengths : ∀ a,(σ.arrs a).length=extent a
  stack : Prefix front "recursion.frames" σ
  cursor : σ.vars "stack.words"=front.length
  width : σ.vars "recursion.stride"=stride
  depth : σ.vars "recursion.fuel"=fuel+1














end Lax263307Proofs.NativeCollectionContext

end

-- Solutions.RAM_Lax263307Proofs_NativeCollectionExecution
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCollectionExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedRounding NativeCoreMachine NativeMachineSegment NativeMasks NativeCollectionContext

/-- Collection context together with all untouched parent data. -/
def Invariant {n : ℕ} (B D k r fuel S : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (parts : List (Finset (Fin n))) (A : Finset (Fin n))
    (extent : String → ℕ) (front : List ℕ) (base σ : Env) : Prop :=
  Context B D k r fuel S G x parts A extent front σ ∧ NativeCollectionAnchor.Anchor base σ











end Lax263307Proofs.NativeCollectionExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeOracleContext
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment













/-- The fixed parent data shared by all branches of one oracle execution.
The evolving rounded state is kept separately. -/
structure Context {n : ℕ} (B D k r p b load F fuel S v limit : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent : String → ℕ) (front : List ℕ) (σ : Env) : Prop where
  moments : NativeMomentAccess.Data G r σ
  target : σ.vars "conditioning.k"=k
  sparsity : σ.vars "conditioning.p"=p
  denominator : σ.vars "algorithm.D"=D
  classB : σ.vars "class.B"=b
  loadValue : σ.vars "algorithm.load"=load
  nodeD : σ.vars "node.D"=D
  floorPower : σ.vars "node.floorPower"=F
  program : Prefix (encodeProgram (MomentLP.program G k r)) "moment.program" σ
  programLength : σ.vars "node.programLength"=(encodeProgram (MomentLP.program G k r)).length
  roundLimit : σ.vars "round.limit"=limit
  roundWidth : σ.vars "algorithm.roundWidth"=v
  bounded : NativeStateBounds.Bounded B σ
  lengths : ∀ a,(σ.arrs a).length=extent a
  stack : Prefix front "recursion.frames" σ
  cursor : σ.vars "stack.words"=front.length
  stride : σ.vars "recursion.stride"=S
  depth : σ.vars "recursion.fuel"=fuel+1
  frameLength : σ.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length















end Lax263307Proofs.NativeOracleContext

end

-- Solutions.RAM_Lax263307Proofs_NativeNearExecution
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNearExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning ComputedSeparators
open NativeCoreMachine NativeMachineSegment NativeOracleContext



















/-- All requirements consumed by the actual near execution theorem. The
recursive field refers only to smaller-fuel child execution. -/
structure Setup {n r : ℕ} (D k p b load fuel S v M h T w space flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (flow : List ℕ → List ℕ) (x : Fin (NativeCatalogMetadata.N n r) → ℚ)
    (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) : Prop where
  bounds : Bounds n r D k p M h T fuel S w cfg extent front
  hx : ∀ i,NativeSignedArithmetic.Bounded M (x i)
  hselected : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A → A.card≤ r
  htarget : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
      ∀ C,ComputedRounding.target (1/(D : ℚ)) (∑ v∈C,(NearOracle.costs (MomentLP.decode x) A v : ℚ))≤ T
  hspace : ∀ a∈NativeSeparatorContext.workspace,space≤ extent a
  flowCall : ∀ A,let costs := NearOracle.costs (MomentLP.decode x) A
      let cs := cuts (step flow G costs b load k) n Finset.univ
      Spec (2^w) (fun σ => NativeSeparatorContext.Context G costs b load k space σ ∧
          n+1≤(σ.arrs "separator.pieces").length)
        (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
        (fun _ τ => NativeSeparatorContext.Context G costs b load k space τ ∧
          τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
          τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
          Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧ τ.vars "separator.position"=2*cs.length ∧
          Prefix (NativeCutPieces.words cs) "separator.pieces" τ) flowTime
  recursive : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
      let costs := NearOracle.costs (MomentLP.decode x) A
      let cs := cuts (step flow G costs b load k) n Finset.univ
      ∀ i∈NearOracle.order cs.length,
      (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈pieces cs i,(costs v : ℚ)) → ∀ base σ,
      Protocol (2^w) D S v cfg extent front σ →
      NativeCollectionExecution.Invariant (2^w) D k r fuel S G costs
        ((NearOracle.order cs.length).map (pieces cs)) A extent front base σ →
      NativeRestrictionRead.Data G (fun v => (costs v : ℚ)) (pieces cs i) σ →
      σ.vars "component.mask"=NativeMasks.mask (pieces cs i) →
      σ.vars "component.target"=ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ)) →
      σ.vars "machine.running"=1 → σ.vars "machine.phase"=11 →
      NativeCollectionChild.Recursive (2^w) S fuel childSteps childTime cfg G (pieces cs i)
        (ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ))) front σ
        (child (pieces cs i) (ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ))))

end Lax263307Proofs.NativeNearExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeOracleExecution
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeOracleExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment NativeOracleContext





def Output {N n : ℕ} : RoundedOracleSearch.Reply N (Finset (Fin n)) → Env → Prop
  | .reject,σ => NativeRoundTrace.Stopped (none : Option (Finset (Fin n))) σ
  | .found I,σ => NativeRoundTrace.Stopped (some I) σ
  | .cut a,σ => σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=13 ∧
      Prefix (NativeRoundedQuery.normal a) "round.normal" σ













/-- Numerical requirements, actual selected solver specifications, and the
smaller-fuel induction premise consumed by the full oracle composition. -/
structure Setup {n r : ℕ} (D k p b load F fuel S v w M farM nearM h T space
    oracleTime callCost flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (state : RoundedOracleSearch.State (MomentLP.dimension n r)) : Prop where
  bounds : ProjectionBounds D k r F M w oracleTime G extent
  hcenter : ∀ i,NativeSignedArithmetic.Bounded M (state.2 i)
  hquery : (encodeProgram (DistanceProjection.distanceProgram (MomentLP.program G k r)
      (ProjectedOracle.raw state.2))).length< extent "vm.input"
  call : Spec (2^w) (NativeProjectionTrace.InvocationInput (MomentLP.program G k r)
      (ProjectedOracle.raw state.2) (NativeNodeTolerance.tolerance n D F) oracleTime)
      (NativeProjectionOracle.command cfg.lp cfg.lpWidth)
      (fun _ τ => NativeProjectionResult.Output (projection lp G k D F state.2) τ ∧
        τ.vars "projection.n"=MomentLP.dimension n r) callCost
  farBounds : ∀ a β,projection lp G k D F state.2=.far a β →
      (∀ i,NativeSignedArithmetic.Bounded farM (a i)) ∧
      farM*RationalCutBuffer.denominator a+farM+RationalCutBuffer.denominator a+
        3*MomentLP.dimension n r+23<2^w
  nearSetup : ∀ x,projection lp G k D F state.2=.near x →
      NativeNearExecution.Setup D k p b load fuel S v nearM h T w space flowTime childSteps childTime
        cfg G flow x extent front child

end Lax263307Proofs.NativeOracleExecution

end

-- Solutions.RAM_Lax263307Proofs_NativeOracleRounds
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeOracleRounds

open Matrix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment NativeOracleContext























/-- Requirements for the complete search, with no assumed Steps contract. -/
structure Setup {n r : ℕ} (D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
 : Prop where
  program : Program cfg.rounded c
  setup : ∀ j,j< limit → NativeOracleExecution.Setup
      D k p b load F fuel S v w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
      cfg G lp flow extent front child (trajectory (oracle (r:=r) lp flow G D k p b load F child) j)
  rounded : ∀ j,j< limit → ∀ a,
      oracle (r:=r) lp flow G D k p b load F child j
        (trajectory (oracle (r:=r) lp flow G D k p b load F child) j).2=.cut a →
      Bounds (2^w) c roundH v n j limit cfg.rounded extent
        (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a
  hcost : (16*(Lax109476.RationalEncoding.encodeProgram (MomentLP.program G k r)).length+
      (36*M.size+124)*MomentLP.dimension n r+135+callCost+2)+14+(193*MomentLP.dimension n r+48)+
      NativeNearExecution.timeBound cfg n r nearM S costH childTime flowTime+6≤ oracleCost
  hround : ∀ j,j< limit → NativeRoundedUpdate.timeBound cfg.rounded c (MomentLP.dimension n r) roundH j+16≤ roundCost



end Lax263307Proofs.NativeOracleRounds

end


