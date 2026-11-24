-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M11_11
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M11_11
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:06:15.098468+00:00
-- url     : https://prove2.me/theorems/59f7c56e-254b-4016-87e1-020045effa99
-- title:
--   Integer dual table for unary loss at ranks $(11,11)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(11,11)$, this bundle defines the fixed total lookup table
--
--   $$D_{11,11}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M11_11.lean lines 8–12; SHA256 e33badefc8c7f769ed034ccc5d44d1b9eb6188ac593da949e001442130dfab87; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def phase0_mdual_11_11 (key : ℕ) : Dual :=
  if key < 18322 then
    if key = 18304 then ⟨1,4539902224270754060275300887301988149847130112,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key = 18322 then ⟨1,4539902224270754060275300887301988149847130112,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


