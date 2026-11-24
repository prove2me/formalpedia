-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M07_07
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M07_07
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:04:36.289061+00:00
-- url     : https://prove2.me/theorems/0c448197-789f-4281-9471-8519f804356d
-- title:
--   Integer dual table for unary loss at ranks $(7,7)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(7,7)$, this bundle defines the fixed total lookup table
--
--   $$D_{7,7}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M07_07.lean lines 8–42; SHA256 5c1f35b5a4817760d5287f5ff97e574dd1233e13429a9e350336a7ddc7e9c6c7; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def phase0_mdual_7_7 (key : ℕ) : Dual :=
  if key < 16658 then
    if key < 14977 then
      if key < 13313 then
        if key = 13312 then ⟨1,1313065500647836196265761805263898474006446080,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 14976 then
          if key = 13313 then ⟨1,1313065500647836196265761805263898474006446080,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 14976 then ⟨1,1313065500647836196265761805263898474006446080,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 16640 then
        if key = 14977 then ⟨1,1313065500647836196265761805263898474006446080,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 16641 then
          if key = 16640 then ⟨1,1313065500647836196265761805263898474006446080,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 16641 then ⟨1,1313065500647836196265761805263898474006446080,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key < 18305 then
      if key < 16659 then
        if key = 16658 then ⟨1,1313065500647836196265761805263898474006446080,0,-109704349155712448104621627180605962780634251264,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18304 then
          if key = 16659 then ⟨1,1313065500647836196265761805263898474006446080,0,-109704349155712448104621627180605962780634251264,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 18304 then ⟨1,1313065500647836196265761805263898474006446080,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 18322 then
        if key = 18305 then ⟨1,1313065500647836196265761805263898474006446080,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18323 then
          if key = 18322 then ⟨1,1313065500647836196265761805263898474006446080,0,81469117116780382646444887692046634896588800000,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 18323 then ⟨1,1313065500647836196265761805263898474006446080,0,81469117116780382646444887692046634896588800000,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


