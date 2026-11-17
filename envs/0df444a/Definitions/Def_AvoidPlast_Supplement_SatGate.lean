-- Prove2me | Definitions.Def_AvoidPlast_Supplement_SatGate
-- name    : AvoidPlast_Supplement_SatGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:52:28.347013+00:00
-- url     : https://prove2.me/theorems/95c18afc-426d-42c4-9274-24a53a25a9b5
-- title:
--   Gates of SAT-oracle circuits
-- statement:
--   A gate of a SAT-oracle circuit is an AND or OR of two earlier wires, a NOT of an earlier wire, or a SAT gate of any fan-in applied to a list of earlier wires.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.9, p.25

import Mathlib

namespace AvoidPlast.Supplement

/-- A gate of a SAT-oracle circuit (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 5.9, p.25, `SIZE^SAT`): AND, OR, NOT of
earlier wires, or a SAT gate of any fan-in applied to a list of earlier wires. -/
inductive SatGate
  | and (a b : ℕ)
  | or (a b : ℕ)
  | not (a : ℕ)
  | sat (args : List ℕ)

end AvoidPlast.Supplement


