-- Prove2me | Definitions.Def_Freiman_lowerInitialStage
-- name    : Freiman_lowerInitialStage
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-09-12T13:03:12.558012+00:00
-- url     : https://prove2.me/theorems/61ef1610-a65b-420d-b01d-f086f8299b28
-- title:
--   Freiman lower construction: one initial gluing stage
-- statement:
--   For a fixed period index n, collect the A and B limiting values, all C limiting values, every A/B/C initial H interval at that index, and the auxiliary B interval. This is the natural stage used to separate the topological gluing argument from the arithmetic seam certificates.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, proof of prop:lc-H-contacts; derived helper for the initial connectedness gluing.

import Definitions.Def_Freiman_lowerCertificates

namespace Freiman

noncomputable def lowerInitialStage (n : ℕ) : Set ℝ := {t |
  t = lowerFamilyLimitValue .A n 0 ∨
  t = lowerFamilyLimitValue .B n 0 ∨
  (∃ k : ℕ, t = lowerFamilyLimitValue .C n k) ∨
  (∃ k : ℕ, t ∈ lowerFamilyH .A n k 0) ∨
  (∃ k : ℕ, t ∈ lowerFamilyH .B n k 0) ∨
  (∃ k p : ℕ, t ∈ lowerFamilyH .C n k p) ∨
  t ∈ lowerFamilyH .auxB n 0 0}

end Freiman


