-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M03_10
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M03_10
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:02:44.588895+00:00
-- url     : https://prove2.me/theorems/b4d40497-5e18-4356-a659-5566577887eb
-- title:
--   Integer dual table for unary loss at ranks $(3,10)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(3,10)$, this bundle defines the fixed total lookup table
--
--   $$D_{3,10}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M03_10.lean lines 8–24; SHA256 34a76e75fa99454d6b6132b18728f13137b2f341fec9718c538bade9811a6191; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def phase0_mdual_3_10 (key : ℕ) : Dual :=
  if key < 18307 then
    if key < 18305 then
      if key = 18304 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 18306 then
        if key = 18305 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key = 18306 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key < 18322 then
      if key = 18307 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 18323 then
        if key = 18322 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key = 18323 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


