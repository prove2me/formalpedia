-- Prove2me | Definitions.Def_AvoidPlast_Supplement_Circuit
-- name    : AvoidPlast_Supplement_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:11:07.651203+00:00
-- url     : https://prove2.me/theorems/a3f89460-17da-4ceb-af51-bda5527a001f
-- title:
--   Boolean circuits
-- statement:
--   A Boolean circuit with $n_{in}$ input wires, a list of AND, OR and NOT gates on earlier wires, and a list of output wires: a map $\{0,1\}^{n_{in}}\to\{0,1\}^{k}$ with $k$ the number of output wires.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 7.2, p.40

import Mathlib

namespace AvoidPlast.Supplement

/-- A Boolean circuit `C : {0,1}^{nIn} → {0,1}^{|outs|}` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 7.2, p.40): `nIn`
input wires, a list of gates (operation `0` = AND, `1` = OR, `2` = NOT of the first argument,
and two argument wires), and the list of output wires. -/
structure Circuit where
  /-- number of input wires -/
  nIn : ℕ
  /-- the gates, in order -/
  gates : List (Fin 3 × ℕ × ℕ)
  /-- the output wires -/
  outs : List ℕ

end AvoidPlast.Supplement


