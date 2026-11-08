-- Prove2me | Definitions.Def_AvoidPlast_relDist
-- name    : AvoidPlast_relDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:39.490029+00:00
-- url     : https://prove2.me/theorems/55190096-58da-4a4c-9b38-08aefc7634a3
-- title:
--   Relative distance of indexed bit strings
-- statement:
--   The relative Hamming distance of two bit strings indexed by a finite type: the fraction of indices where they differ.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Claim 4.5.1, p.20

import Mathlib

namespace AvoidPlast

open Classical in
/-- The relative Hamming distance of two bit strings indexed by a finite type (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Claim 4.5.1,
p.20): the fraction of positions where they differ. -/
noncomputable def relDist {A : Type} [Fintype A] (u v : A → Bool) : ℝ :=
  ((Finset.univ.filter fun a => u a ≠ v a).card : ℝ) / Fintype.card A

end AvoidPlast


