-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossData
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:33.143906+00:00
-- url     : https://prove2.me/theorems/ac135581-20d3-484b-8bd4-ab9aff7c9a69
-- title:
--   Literal phase-zero baseline recipe and profiles
-- statement:
--   This bundle fixes the baseline-loss numerical recipe for the unary phase-zero gate. It has $1329$ physical guard sockets and $1329$ singleton checks. For ranks $0,\ldots,11$, the soft cutoffs, hard cutoffs, and allowances are
--   $$
--   (5,5,5,5,5,5,4,4,3,3,2,2),\qquad
--   (12,12,12,12,12,5,5,4,4,3,3,2),
--   $$
--   $$
--   (5,4,3,2,1,1,1,1,1,1,1,1).
--   $$
--   The two target arrays coincide, as required for a unary gate. Their literal entries encode the phase-zero target function, with the failure index capped at seven. The input and output profile arrays are the stored initial ray and its first image.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossData.lean lines 6–19; SHA256 12ca39ffb5deee80f3db8a9ac09f18a5355b10100c45d0edc026bb8e6d5ddcc3; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LiteralProfileData
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric



namespace SensitivityBaselineLossNumeric

 def scalarEntry (v : Array ℕ) (j : Fin 12) : ℕ := v[j.val]?.getD 0
 def targetEntry (v : Array ℕ) (j : Fin 12) (f : ℕ) : Fin 12 :=
  Fin.ofNat 12 (v[j.val * 8 + min f 7]?.getD 0)

def phase0 : Recipe :=
  ⟨true,1329,1329,
    scalarEntry #[5,5,5,5,5,5,4,4,3,3,2,2],
    scalarEntry #[12,12,12,12,12,5,5,4,4,3,3,2],
    scalarEntry #[5,4,3,2,1,1,1,1,1,1,1,1],
    targetEntry #[7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,8,8,8,8,8,8,8,8,10,10,10,10,10,10,10,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11],
    targetEntry #[7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,8,8,8,8,8,8,8,8,10,10,10,10,10,10,10,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11]⟩

def input0 : Array ℕ := SensitivityLiteralRay.rayData
def output0 : Array ℕ := SensitivityLiteralRay.image0Data





















end SensitivityBaselineLossNumeric


