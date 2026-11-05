-- Prove2me | Definitions.Def_SelectedProfileReal
-- name    : SelectedProfileReal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.131245+00:00
-- url     : https://prove2.me/theorems/53c42cbc-db0d-4544-80c6-0caa354487d3
-- title:
--   SelectedProfileReal definitions
-- statement:
--   Real analytic contraction inequalities derived from the selected PR64 rational profile. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileReal.lean). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/next-proof/analytic/SelectedProfileReal.lean | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_SelectedProfileCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
namespace SelectedProfileReal
open AnalyticEnclosures SelectedProfileCertificate
noncomputable def exponentialCharacteristic : ℝ :=
  (rows.map (fun r => (weight r : ℝ) *
    Real.exp ((saving : ℝ) * Real.log ((m : ℝ) / r.width)))).sum
noncomputable def powerCharacteristic : ℝ :=
  (rows.map (fun r => (r.multiplicity : ℝ) / W *
    ((r.width : ℝ) / m) ^ (1 - (saving : ℝ)))).sum
end SelectedProfileReal


