-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M08_08
-- name    : Sensitivity214439_Phase0_Solutions_BaselineLossChecks_Phase0M08_08
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:04:36.489864+00:00
-- url     : https://prove2.me/theorems/2a17745b-0eec-47f7-a9f7-83a5847ad9ec
-- title:
--   Integer dual table for unary loss at ranks $(8,8)$
-- statement:
--   For the unary Paley recipe and rank pair $(i,j)=(8,8)$, this bundle defines the fixed total lookup table
--
--   $$D_{8,8}:\mathbb{N}\longrightarrow\mathbb{N}\times\mathbb{Z}^5.$$
--
--   An entry consists of a denominator and five integer weights for socket multiplicity, guard checks, weak failures, strong failures, and the extra branch constraint. A local state with own heights $a,b$, failure counts $f_i,f_j$, and branch $b_0$ selects its entry using
--
--   $$\kappa(a,b,f_i,f_j,b_0)=2\bigl(8(8(12a+b)+f_i)+f_j\bigr)+b_0.$$
--
--   The table records the exact integer data for the baseline-loss certificate. Companion validity lemmas check the required signs, column domination, and total-cost inequality at every admissible state.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/BaselineLossChecks/Phase0M08_08.lean lines 8–42; SHA256 10842c12b0e1233137a442edc2d06a95afb8f5db2da2b0470070f22aa8cf4ac3; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

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

def phase0_mdual_8_8 (key : ℕ) : Dual :=
  if key < 16658 then
    if key < 14995 then
      if key < 14977 then
        if key = 14976 then ⟨1329,3597236414879081506238112220155007248511967166464,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 14994 then
          if key = 14977 then ⟨1,78156215775740827794926531246432453211979776,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 14994 then ⟨1,2707773606459663908164041007793481438281596928,0,-1394708105811827711898279202529582964275150848,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 16640 then
        if key = 14995 then ⟨1,2707773606459663908164041007793481438281596928,0,-1394708105811827711898279202529582964275150848,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 16641 then
          if key = 16640 then ⟨1,78156215775740827794926531246432453211979776,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 16641 then ⟨1,78156215775740827794926531246432453211979776,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
  else
    if key < 18305 then
      if key < 16659 then
        if key = 16658 then ⟨1,2707773606459663908164041007793481438281596928,0,-1394708105811827711898279202529582964275150848,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18304 then
          if key = 16659 then ⟨83,238405766328728191838992318730267909224025554944,0,-129421329774957787548934088893364335881490530304,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 18304 then ⟨1,78156215775740827794926531246432453211979776,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
    else
      if key < 18322 then
        if key = 18305 then ⟨1,78156215775740827794926531246432453211979776,0,0,0,0⟩ else ⟨1,0,0,0,0,0⟩
      else
        if key < 18323 then
          if key = 18322 then ⟨1,2707773606459663908164041007793481438281596928,0,-1394708105811827711898279202529582964275150848,0,0⟩ else ⟨1,0,0,0,0,0⟩
        else
          if key = 18323 then ⟨83,238405766328728191838992318730267909224025554944,0,-129421329774957787548934088893364335881490530304,0,0⟩ else ⟨1,0,0,0,0,0⟩





end SensitivityBaselineLossNumeric


