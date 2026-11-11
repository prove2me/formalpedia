-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T02:15:17.082537+00:00
-- url     : https://prove2.me/theorems/0d0ccee3-db8c-40b8-9312-5dc64b0c9f5d
-- title:
--   RXIncidence Hull Retained Growth
-- statement:
--   Definitions and structural lemmas for RXIncidence Hull Retained Growth, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullRetainedGrowth.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRZ
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGrowth_SharedZPath_symm
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
open QEC.Coding.MultiscaleDecoder QEC.Coding.BDL26IndexedDecoder
open scoped Classical
namespace QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RXIncidenceHullGrowth BDL26RXIncidenceHullSuccessors
open BDL26QuantitativeBounds BDL26RXDifferentialMasks
def Retained : Nat → Type
  | 0 => BaseQubit
  | n+1 => Retained n × BDL26FiniteTannerSquare.Two
instance retainedFintype (n : Nat) : Fintype (Retained n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype BaseQubit)
  | succ n ih =>
      letI : Fintype (Retained n) := ih
      change Fintype (Retained n × BDL26FiniteTannerSquare.Two)
      infer_instance
instance retainedDecidableEq (n : Nat) : DecidableEq (Retained n) := Classical.decEq _
def retainedZero : (n : Nat) → Retained n
  | 0 => (0 : BaseQubit)
  | n+1 => (retainedZero n,0)
def nextRoots (S : OddScale) (n : Nat) (C : ConstructionState) :
    C.presentation.Q × BDL26FiniteTannerSquare.Two ↪ (nextState S n C).presentation.Q :=
  if h : n % 2 = 0 then
    let E := Equiv.cast (congrArg (fun D : ConstructionState => D.presentation.Q)
      (show rxState S C = nextState S n C from (if_pos h).symm))
    { toFun := fun qt => E (rxQubitRoots C.presentation S qt)
      inj' := fun _ _ he => (rxQubitRoots C.presentation S).injective (E.injective he) }
  else
    let E := Equiv.cast (congrArg (fun D : ConstructionState => D.presentation.Q)
      (show rzState S C = nextState S n C from (if_neg h).symm))
    { toFun := fun qt => E (rzQubitRoots C.presentation S qt)
      inj' := fun _ _ he => (rzQubitRoots C.presentation S).injective (E.injective he) }
def retainedRoots (S : OddScale) : (n : Nat) → Retained n ↪ (state S n).presentation.Q
  | 0 => ⟨id,Function.injective_id⟩
  | n+1 =>
      { toFun := fun a => nextRoots S n (state S n) (retainedRoots S n a.1,a.2)
        inj' := by
          intro a b he
          have hp := (nextRoots S n (state S n)).injective he
          have hfirst : a.1 = b.1 :=
            (retainedRoots S n).injective
              (congrArg (fun v : (state S n).presentation.Q × BDL26FiniteTannerSquare.Two => v.1) hp)
          have hsecond : a.2 = b.2 :=
            congrArg (fun v : (state S n).presentation.Q × BDL26FiniteTannerSquare.Two => v.2) hp
          exact Prod.ext hfirst hsecond }
def seed (S : OddScale) (n : Nat) : Finset (state S n).presentation.Q :=
  {retainedRoots S n (retainedZero n)}
end QEC.Coding.BDL26RXIncidenceHullRetainedGrowth
end


