-- Prove2me | Definitions.Def_Section5Verified_Section5PhaseRecovery
-- name    : Section5Verified_Section5PhaseRecovery
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:36:57.668345+00:00
-- url     : https://prove2.me/theorems/f83385a7-a4b6-5a60-bd7a-61de35fbc1c8
-- title:
--   Section5PhaseRecovery — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5PhaseRecovery; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

noncomputable def section5_real_part {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => (v i).re

noncomputable def section5_imag_part {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun i => (v i).im

noncomputable def section5_complexify {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 fun i => (w i : ℂ)









end


