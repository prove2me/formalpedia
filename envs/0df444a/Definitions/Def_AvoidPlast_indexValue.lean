-- Prove2me | Definitions.Def_AvoidPlast_indexValue
-- name    : AvoidPlast_indexValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:01.14668+00:00
-- url     : https://prove2.me/theorems/d284bfab-020f-4e00-9798-b69c058f7b78
-- title:
--   The number on an index tape
-- statement:
--   The number written on an index tape: binary, least significant bit first, from cell $0$ up to the first blank.
--
--   **Formalization Note** A tape in a run has finitely many non-blank cells, so the first blank exists; the junk value on a blank-free function never occurs in a run.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib

namespace AvoidPlast

/-- The number written on an index tape (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine model): binary, least
significant bit first, read from cell `0` up to the first blank.

**Formalization Note** A tape in a run has finitely many non-blank cells, so a first blank exists;
on a blank-free function `sInf ∅ = 0` gives the junk value `0`, which never occurs in a run. -/
noncomputable def indexValue (t : ℕ → Option Bool) : ℕ :=
  ∑ i ∈ Finset.range (sInf {i | t i = none}), if t i = some true then 2 ^ i else 0

end AvoidPlast


