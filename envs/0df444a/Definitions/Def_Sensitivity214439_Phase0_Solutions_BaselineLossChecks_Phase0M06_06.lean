-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M06_06
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M06_06
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:04:02.540044+00:00
-- url     : https://prove2.me/theorems/fada887d-0796-44ef-bb57-b886f33a310e
-- title:
--   Integer dual table for unary loss at ranks $(6,6)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(6,6)$, this bundle defines the fixed total lookup table
--
--   $$D_{6,6}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M06_06.lean lines 8–60; SHA256 994a94da5be7285216aaec93a0e6b2b35d2354c4869f65ec2934d3e389f282e6; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def phase0_mdual_6_6 (key : ℕ) : Dual :=
  if key < 14995 then
    if key < 13330 then
      if key < 13312 then
        if key < 11649 then
          if key = 11648 then ⟨1329,1812307499199631128589994838747193027567982477312,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 11649 then ⟨1,1313065500647836196265761805263898474006446080,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 13313 then
          if key = 13312 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 13313 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 14976 then
        if key < 13331 then
          if key = 13330 then ⟨1,1313065500647836196265761805263898474006446080,0,-889529621487025589622724345206205247897206784,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 13331 then ⟨1,1313065500647836196265761805263898474006446080,0,-889529621487025589622724345206205247897206784,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 14977 then
          if key = 14976 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 14994 then
            if key = 14977 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 14994 then ⟨83,116622173757723201312359727480917350902755491840,0,-81468695787375920960987618296128813135688630272,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key < 16659 then
      if key < 16641 then
        if key < 16640 then
          if key = 14995 then ⟨83,116622173757723201312359727480917350902755491840,0,-81468695787375920960987618296128813135688630272,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 16640 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 16658 then
          if key = 16641 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 16658 then ⟨1,1313065500647836196265761805263898474006446080,0,121397968732704086479058682495903824663604625408,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 18305 then
        if key < 18304 then
          if key = 16659 then ⟨83,116627405200907348794350817764472950212003889152,0,-81473927230560068442978708579684412444937027584,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 18304 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18322 then
          if key = 18305 then ⟨1,95039991749840130854986779666376877408256,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key < 18323 then
            if key = 18322 then ⟨1,1313065500647836196265761805263898474006446080,0,121397968732704086479058682495903824663604625408,0,0⟩ else ⟨1,0,0,0,0,0⟩
          else
            if key = 18323 then ⟨83,116627405200907348794350817764472950212003889152,0,-81473927230560068442978708579684412444937027584,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


