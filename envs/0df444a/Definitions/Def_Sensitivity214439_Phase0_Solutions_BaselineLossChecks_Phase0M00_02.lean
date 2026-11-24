-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M00_02
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M00_02
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:59:58.162056+00:00
-- url     : https://prove2.me/theorems/6cd78747-9161-4b14-9ec0-1335dd0e90fc
-- title:
--   Integer dual table for unary loss at ranks $(0,2)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(0,2)$, this bundle defines the fixed total lookup table
--
--   $$D_{0,2}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M00_02.lean lines 8–126; SHA256 1a39e4783a0462e88f4866a0f71cd878a358a8e42c96631bbf69894c4e1f1a4d; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def phase0_mdual_0_2 (key : ℕ) : Dual :=
  if key < 15012 then
    if key < 13330 then
      if key < 11685 then
        if key < 11666 then
          if key < 11649 then
            if key = 11648 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 11649 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 11667 then
            if key = 11666 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key < 11684 then
              if key = 11667 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
            else
              if key = 11684 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 11703 then
          if key < 11702 then
            if key = 11685 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 11702 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 13312 then
            if key = 11703 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key < 13313 then
              if key = 13312 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
            else
              if key = 13313 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 13367 then
        if key < 13348 then
          if key < 13331 then
            if key = 13330 then ⟨1,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 13331 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 13349 then
            if key = 13348 then ⟨1,0,0,31117410720604522956934869042362031999884984320,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key < 13366 then
              if key = 13349 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
            else
              if key = 13366 then ⟨3,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 14977 then
          if key < 14976 then
            if key = 13367 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 14976 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 14994 then
            if key = 14977 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key < 14995 then
              if key = 14994 then ⟨1,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
            else
              if key = 14995 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key < 16694 then
      if key < 16641 then
        if key < 15030 then
          if key < 15013 then
            if key = 15012 then ⟨1,0,0,31117410720604522956934869042362031999884984320,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 15013 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 15031 then
            if key = 15030 then ⟨3,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key < 16640 then
              if key = 15031 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
            else
              if key = 16640 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 16659 then
          if key < 16658 then
            if key = 16641 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 16658 then ⟨1,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 16676 then
            if key = 16659 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key < 16677 then
              if key = 16676 then ⟨1,0,0,31117410720604522956934869042362031999884984320,0,0⟩ else ⟨1,0,0,0,0,0⟩
            else
              if key = 16677 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 18323 then
        if key < 18304 then
          if key < 16695 then
            if key = 16694 then ⟨3,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 16695 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 18305 then
            if key = 18304 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key < 18322 then
              if key = 18305 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
            else
              if key = 18322 then ⟨1,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18341 then
          if key < 18340 then
            if key = 18323 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 18340 then ⟨1,0,0,31117410720604522956934869042362031999884984320,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 18358 then
            if key = 18341 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key < 18359 then
              if key = 18358 then ⟨3,0,0,62234821441209045913869738084724063999769968640,0,0⟩ else ⟨1,0,0,0,0,0⟩
            else
              if key = 18359 then ⟨1,0,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


