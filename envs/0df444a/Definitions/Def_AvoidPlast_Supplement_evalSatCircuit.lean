-- Prove2me | Definitions.Def_AvoidPlast_Supplement_evalSatCircuit
-- name    : AvoidPlast_Supplement_evalSatCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:53:41.486752+00:00
-- url     : https://prove2.me/theorems/338578e0-f270-4fe2-a325-98d5fc1f6d75
-- title:
--   Output of a SAT-oracle circuit
-- statement:
--   On input $x\in\{0,1\}^n$, wires $0,\dots,n-1$ carry the input bits and each gate, in order, adds one wire; the output is the last wire. The *size* of the circuit is its number of gates.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.9, p.25

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_SatGate
import Definitions.Def_AvoidPlast_Supplement_SatGate_eval

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The output of a SAT-oracle circuit on `x` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.9, p.25): wires `0, …, |x|-1`
carry the input bits, each gate adds one wire, and the output is the last wire. The size of the
circuit is its number of gates. -/
noncomputable def evalSatCircuit (gates : List SatGate) (x : List Bool) : Bool :=
  (gates.foldl (fun v g => v ++ [g.eval v]) x).getLast?.getD false

end AvoidPlast.Supplement


