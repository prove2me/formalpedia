-- Prove2me | Definitions.Def_QEC_Distillation_Injection_PhaseRetry
-- name    : QEC_Distillation_Injection_PhaseRetry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:35:37.776804+00:00
-- url     : https://prove2.me/theorems/4b65a219-6d6c-49f1-bcf3-36ce1e04e905
-- title:
--   Phase Retry
-- statement:
--   Definitions and structural lemmas for Phase Retry, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Injection/PhaseRetry.lean

import Mathlib.Probability.Distributions.Uniform
set_option autoImplicit false
namespace QEC
namespace Distillation
namespace PhaseRetry
noncomputable section
def signedIncrement (coin : Bool) {q : Nat} : ZMod q :=
  if coin then 1 else -1
def positions {q : Nat} (start : ZMod q) : List Bool → List (ZMod q)
  | [] => [start]
  | coin :: coins => start :: positions (start + signedIncrement coin) coins
def endpoint {q : Nat} (start : ZMod q) : List Bool → ZMod q
  | [] => start
  | coin :: coins => endpoint (start + signedIncrement coin) coins
def visitsTarget {q : Nat} (start target : ZMod q) (coins : List Bool) : Prop :=
  target ∈ positions start coins
def positiveBlock (q : Nat) : List Bool :=
  List.replicate q true
abbrev CoinBlock (q : Nat) := Fin q → Bool
def allPositiveBlock (q : Nat) : CoinBlock q := fun _ => true
def blockCoins {q : Nat} (block : CoinBlock q) : List Bool :=
  List.ofFn block
def isPositiveBlock {q : Nat} (block : CoinBlock q) : Bool :=
  decide (block = allPositiveBlock q)
abbrev NonpositiveBlock (q : Nat) := { block : CoinBlock q // isPositiveBlock block = false }
abbrev BlockTrace (q blocks : Nat) := Fin blocks → CoinBlock q
abbrev NoPositiveTrace (q blocks : Nat) := Fin blocks → NonpositiveBlock q
def blockEndpoint {q : Nat} (start : ZMod q) (block : CoinBlock q) : ZMod q :=
  endpoint start (blockCoins block)
def traceVisitsTarget {q : Nat} (start target : ZMod q) :
    (blocks : Nat) → BlockTrace q blocks → Prop
  | 0, _ => start = target
  | blocks + 1, trace =>
      visitsTarget start target (blockCoins (trace 0)) ∨
        traceVisitsTarget (blockEndpoint start (trace 0)) target blocks
          (fun index => trace index.succ)
abbrev TargetMissTrace (q blocks : Nat) (start target : ZMod q) :=
  { trace : BlockTrace q blocks // ¬ traceVisitsTarget start target blocks trace }
@[reducible] noncomputable def targetMissTraceFintype (q blocks : Nat) (start target : ZMod q) :
    Fintype (TargetMissTrace q blocks start target) :=
  Fintype.ofFinite _
noncomputable def targetMissProbability (q blocks : Nat) (start target : ZMod q) : Real :=
  @Fintype.card (TargetMissTrace q blocks start target)
    (targetMissTraceFintype q blocks start target) /
    Fintype.card (BlockTrace q blocks)
def FiniteCyclicRetryHitsTarget (q : Nat) (start target : ZMod q) : Prop :=
  ∀ history : List Bool, visitsTarget start target (history ++ positiveBlock q)
def certificateFailureTail (q blocks : Nat) : Real :=
  (1 - ((2 : Real)⁻¹) ^ q) ^ blocks
def certificateFailureProbability (q blocks : Nat) : Real :=
  Fintype.card (NoPositiveTrace q blocks) /
    Fintype.card (BlockTrace q blocks)
noncomputable def targetHitProbability (q blocks : Nat) (start target : ZMod q) : Real :=
  1 - targetMissProbability q blocks start target
def AlmostSureTargetHit (failure : Nat → Real) : Prop :=
  Filter.Tendsto failure Filter.atTop (nhds 0)
end
end PhaseRetry
end Distillation
end QEC


