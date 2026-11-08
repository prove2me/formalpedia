-- Prove2me | Definitions.Def_AvoidPlast_relHamming
-- name    : AvoidPlast_relHamming
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:27.72954+00:00
-- url     : https://prove2.me/theorems/a1797ac1-032a-43ef-a314-cede595f838d
-- title:
--   Relative Hamming distance
-- statement:
--   The relative Hamming distance of two bit strings: the fraction of positions where they differ.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 4.2, p.20

import Mathlib

namespace AvoidPlast

/-- The relative Hamming distance of two bit strings (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §4.2, p.20): the fraction of positions
where they differ. -/
noncomputable def relHamming (y y' : List Bool) : ℝ :=
  ((List.zipWith (fun a b => a != b) y y').count true : ℝ) / y.length

end AvoidPlast


