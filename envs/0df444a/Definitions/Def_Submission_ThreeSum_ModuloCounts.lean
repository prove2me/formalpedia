-- Prove2me | Definitions.Def_Submission_ThreeSum_ModuloCounts
-- name    : Submission_ThreeSum_ModuloCounts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:27:45.61102+00:00
-- url     : https://prove2.me/theorems/e5becb6b-1ab5-4d9f-abd1-ed135e934d34
-- title:
--   Modulo Counts
-- statement:
--   Definitions and structural lemmas for Modulo Counts, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCounts.lean

import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_Arithmetic
set_option autoImplicit false
namespace ThreeSum.ModuloCounts
open Finset LightResidueHistogram
open scoped BigOperators
def triples (nA nB nC : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  range nA ×ˢ (range nB ×ˢ range nC)
def difference (a b c : ℕ → ℤ) (t : ℕ × ℕ × ℕ) : ℤ :=
  c t.2.2 - b t.2.1 - a t.1
def count (p nA nB nC : ℕ) (a b c : ℕ → ℤ) : ℕ :=
  Arithmetic.modCount (triples nA nB nC) (difference a b c) (p : ℤ)
end ThreeSum.ModuloCounts


