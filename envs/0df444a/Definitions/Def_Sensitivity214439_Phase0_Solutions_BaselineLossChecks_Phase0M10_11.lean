-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M10_11
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M10_11
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:05:58.430136+00:00
-- url     : https://prove2.me/theorems/38ffc656-68e3-4fa9-bac1-f34f2d19bc12
-- title:
--   Integer dual table for unary loss at ranks $(10,11)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(10,11)$, this bundle defines the fixed total lookup table
--
--   $$D_{10,11}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M10_11.lean lines 8–12; SHA256 f5e7b17bedbfe6d614b02afff3d194b248c7294eb64d8a90b33d61064d1af35b; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range

namespace SensitivityBaselineLossNumeric
end SensitivityBaselineLossNumeric



namespace SensitivityBaselineLossNumeric
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option Elab.async false

def phase0_mdual_10_11 (key : ℕ) : Dual :=
  if key < 18322 then
    if key = 18304 then ⟨1,234183527351972922681792104170103027600982016,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key = 18322 then ⟨1,4539902224270754060275300887301988149847130112,0,-5722300148205060131861773172782275327465130819584,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


