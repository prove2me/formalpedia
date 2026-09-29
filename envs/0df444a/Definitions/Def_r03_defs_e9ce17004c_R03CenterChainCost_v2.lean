-- Prove2me | Definitions.Def_r03_defs_e9ce17004c_R03CenterChainCost_v2
-- name    : r03_defs_e9ce17004c_R03CenterChainCost_v2
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:33.942834+00:00
-- url     : https://prove2.me/theorems/589cd249-77f6-49a9-b6e5-1d017222eb36
-- title:
--   R03 candidate definition: r03 defs e9ce17004c R03CenterChainCost v2
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_e9ce17004c_R03CenterChainCost_v2.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Mathlib.Data.Fin.VecNotation

/- Candidate scalar certificate only. Its hypotheses encode the separate
   four-square graph argument; no arbitrary-graph projector is asserted. -/
set_option Elab.async false
namespace R03CenterChainCost

def debt (b : Bool) : Int := if b then 1 else 0

def PairCertificate (a b : Bool) (w : Nat) : Prop :=
  1 ≤ w ∧ (w=1 → b=true) ∧ (a=true → 3 ≤ w)

inductive CostChain : Bool → Bool → Nat → Nat → Prop where
  | empty (a : Bool) : CostChain a a 0 0
  | prepend {a b c : Bool} {steps total : Nat} (w : Nat)
      (hpair : PairCertificate a b w) (tail : CostChain b c steps total) :
      CostChain a c (steps+1) (w+total)

end R03CenterChainCost


