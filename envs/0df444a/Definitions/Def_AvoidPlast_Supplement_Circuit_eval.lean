-- Prove2me | Definitions.Def_AvoidPlast_Supplement_Circuit_eval
-- name    : AvoidPlast_Supplement_Circuit_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:11:38.57241+00:00
-- url     : https://prove2.me/theorems/f3e4a04b-b441-4d14-b5e4-ef9ca7ebe539
-- title:
--   Evaluation of a Boolean circuit
-- statement:
--   On input $z$, wires $0,\dots,|z|-1$ carry $z$, each gate adds one wire computed from earlier wires (a missing wire reads $0$), and the output is the list of values of the output wires.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 7.2, p.40

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_Circuit

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The output of a circuit on `z` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 7.2, p.40): wires `0, …, |z|-1` carry `z`,
each gate adds one wire computed from earlier wires (a wire that does not exist reads `0`), and the
output lists the output wires. -/
def Circuit.eval (c : Circuit) (z : List Bool) : List Bool :=
  let v := c.gates.foldl (fun v g =>
    v ++ [match g.1 with
      | 0 => v.getD g.2.1 false && v.getD g.2.2 false
      | 1 => v.getD g.2.1 false || v.getD g.2.2 false
      | _ => !v.getD g.2.1 false]) z
  c.outs.map fun o => v.getD o false

end AvoidPlast.Supplement


