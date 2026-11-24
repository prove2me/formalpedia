-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M04_11
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M04_11
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:03:01.675786+00:00
-- url     : https://prove2.me/theorems/ff7999ab-1dfd-4ae3-9643-773d949886d4
-- title:
--   Integer dual table for unary loss at ranks $(4,11)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(4,11)$, this bundle defines the fixed total lookup table
--
--   $$D_{4,11}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M04_11.lean lines 8–15; SHA256 c832dcf7c15c98bae2b21a5978318b7c08de47aa8b09ccae134891f5a5231932; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def phase0_mdual_4_11 (key : ℕ) : Dual :=
  if key < 18306 then
    if key = 18304 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key < 18322 then
      if key = 18306 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key = 18322 then ⟨1,95039991749840130854986779666376877408256,0,-126308149035537533906277430176614870075572224,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


