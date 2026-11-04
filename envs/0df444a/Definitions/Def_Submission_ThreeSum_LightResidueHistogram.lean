-- Prove2me | Definitions.Def_Submission_ThreeSum_LightResidueHistogram
-- name    : Submission_ThreeSum_LightResidueHistogram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:24:06.823347+00:00
-- url     : https://prove2.me/theorems/270272f5-afed-45f6-92e8-5d74578ae28c
-- title:
--   Light Residue Histogram
-- statement:
--   Definitions and structural lemmas for Light Residue Histogram, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidueHistogram.lean

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_CyclicFold
import Theorems.Thm_Light_Ends_call

set_option autoImplicit false
namespace ThreeSum.LightResidueHistogram
open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba
variable {lim : Limits} {P : Program} {d : ℕ}
def signedHistogram (p : ℕ) (c : ℤ) (values : ℕ → ℤ) (n : ℕ) (z : ZMod p) : ℕ :=
  Histograms.histogram (Finset.range n) (fun i => ((c * values i : ℤ) : ZMod p))
    (fun _ => 1) z
def body (pResidues pHistogram : ℕ) : Stmt :=
  .call pResidues [v 0, v 5, v 2, v 3, v 6, v 7] 8 ;;
  .call pHistogram [v 5, v 1, v 2, v 4] 8
def time (n cap U : ℕ) : ℕ := residuesTime n U + histogramTime n cap + 30
def program : Program :=
  [body 1 3, residuesBody 2, emodBody, histogramBody 4, fillBody]
end ThreeSum.LightResidueHistogram


