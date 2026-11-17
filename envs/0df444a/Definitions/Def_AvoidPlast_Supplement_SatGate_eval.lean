-- Prove2me | Definitions.Def_AvoidPlast_Supplement_SatGate_eval
-- name    : AvoidPlast_Supplement_SatGate_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:52:59.819199+00:00
-- url     : https://prove2.me/theorems/beef2d0f-f2ef-4c3c-a9aa-4604b5546195
-- title:
--   Value of a SAT-oracle gate
-- statement:
--   Given the values of the wires before it, an AND, OR or NOT gate computes the Boolean function of its arguments, and a SAT gate outputs $1$ iff the string formed by its argument wires is in SAT. A reference to a wire that does not exist yet reads $0$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.9, p.25

import Mathlib
import Definitions.Def_AvoidPlast_Supplement_satLang
import Definitions.Def_AvoidPlast_Supplement_SatGate

namespace AvoidPlast.Supplement

open AvoidPlast

open Classical in
/-- The value of a gate given the values `v` of the wires before it (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.9,
p.25). A reference to a wire that does not exist yet reads `false`; a SAT gate outputs whether
the string of its input wires is in `satLang`. -/
noncomputable def SatGate.eval (v : List Bool) : SatGate → Bool
  | .and a b => v.getD a false && v.getD b false
  | .or a b => v.getD a false || v.getD b false
  | .not a => !v.getD a false
  | .sat args => decide (args.map (fun a => v.getD a false) ∈ satLang)

end AvoidPlast.Supplement


