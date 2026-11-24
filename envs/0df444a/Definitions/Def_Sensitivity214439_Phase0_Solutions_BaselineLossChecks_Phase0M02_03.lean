-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M02_03
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M02_03
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:01:17.516792+00:00
-- url     : https://prove2.me/theorems/4de38bed-8e01-4369-aa8f-3574acaa8ff8
-- title:
--   Integer dual table for unary loss at ranks $(2,3)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(2,3)$, this bundle defines the fixed total lookup table
--
--   $$D_{2,3}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M02_03.lean lines 8–96; SHA256 12c88e08f534faa9fc78337ef2ec1f52740dd3925a428bd2e917c7293672bfee; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def phase0_mdual_2_3 (key : ℕ) : Dual :=
  if key < 14995 then
    if key < 13313 then
      if key < 11667 then
        if key < 11649 then
          if key = 11648 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 11666 then
            if key = 11649 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 11666 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 11685 then
          if key < 11684 then
            if key = 11667 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 11684 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 13312 then
            if key = 11685 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 13312 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 13349 then
        if key < 13331 then
          if key < 13330 then
            if key = 13313 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 13330 then ⟨1,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 13348 then
            if key = 13331 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 13348 then ⟨1,0,0,31117410720604522956934869042362031999884984320,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 14977 then
          if key < 14976 then
            if key = 13349 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 14976 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 14994 then
            if key = 14977 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 14994 then ⟨1,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key < 16676 then
      if key < 16640 then
        if key < 15012 then
          if key = 14995 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 15013 then
            if key = 15012 then ⟨1,0,0,31117410720604522956934869042362031999884984320,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 15013 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 16658 then
          if key < 16641 then
            if key = 16640 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 16641 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 16659 then
            if key = 16658 then ⟨1,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 16659 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 18322 then
        if key < 18304 then
          if key < 16677 then
            if key = 16676 then ⟨1,0,0,31117410720604522956934869042362031999884984320,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 16677 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 18305 then
            if key = 18304 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 18305 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18340 then
          if key < 18323 then
            if key = 18322 then ⟨1,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 18323 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 18341 then
            if key = 18340 then ⟨1,0,0,31117410720604522956934869042362031999884984320,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 18341 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


