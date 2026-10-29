-- Prove2me | Definitions.Def_IntMul_Oppbank_GroundTruth
-- name    : IntMul_Oppbank_GroundTruth
-- status  : Definition
-- author  : @darkhipo
-- created : 2026-10-28T20:41:22.753714+00:00
-- url     : https://prove2.me/theorems/81574cd6-ca0a-42e6-8d74-1322f117d037

import Definitions.Def_IntMul_KappaFramework
import Mathlib

/-!
# Corrected per-pass rank histogram of the Oppbank chunk programs

**Corrects the MomPack `CN1_*`/`CN2_*` defect**: those packs decode to
values in the billions and do NOT give the real rank histograms. This
definition carries the CORRECT per-pass child-width histogram.

Method: exact `genF` replication anchored to Lean `#eval` (recs=54290,
W1F=237921, touch=536840). Both `NB.cs1` and `NB.cs2` produce identical
histograms. Total count 119262, total rank 774109.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank

/-- The corrected per-pass child-width rank histogram (both stages identical). -/
def groundTruthDC : List (ℕ × ℕ) := [(0, 13016), (1, 25510), (2, 25258), (3, 2987), (4, 10042), (5, 3871), (6, 2463), (7, 2257), (8, 1427), (9, 5371), (10, 1114), (11, 1660), (12, 941), (13, 482), (14, 715), (15, 296), (16, 331), (17, 347), (18, 851), (19, 512), (20, 7), (21, 4915), (22, 4184), (23, 10705)]

/-- Total moves per pass (both stages). -/
def groundTruthMoves : ℕ := 119262

theorem groundTruth_count :
    (groundTruthDC.map fun p => p.2).sum = 119262 := by rfl

theorem groundTruth_rank :
    histRankSum groundTruthDC = 774109 := by rfl

end IntMul.Kappa.R8.Bit.Oppbank


