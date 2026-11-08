-- Prove2me | Definitions.Def_AvoidPlast_decodeMachine
-- name    : AvoidPlast_decodeMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:50.330338+00:00
-- url     : https://prove2.me/theorems/f30b15de-7a01-4c84-afee-d344eba495fa
-- title:
--   Parsing a machine description
-- statement:
--   A description $d=0^j1e$ decodes to the machine with binary code $e$, and a string without a $1$ decodes to nothing. So every machine has a description of every length at least $|\mathrm{code}(M)|+1$, which is what universality needs.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 5.13, p.29

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_UniqueOptScores_decodeNat

namespace AvoidPlast

/-- Parsing a description (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 5.13, p.29, "parses `d` as the description of a
deterministic machine", reading R4): `d = 0^j 1 e` decodes to the machine with binary code `e`.
Every machine therefore has a description of every length at least `|encodeMachine M| + 1`. -/
def decodeMachine (d : List Bool) : Option (Machine 1) :=
  match d.dropWhile (fun b => b == false) with
  | [] => none
  | _ :: e => Encodable.decode (UniqueOptScores.decodeNat e)

end AvoidPlast


