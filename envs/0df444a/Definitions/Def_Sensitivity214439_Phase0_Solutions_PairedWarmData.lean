-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_PairedWarmData
-- name    : Sensitivity214439_Phase0_Solutions_PairedWarmData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T13:19:46.266932+00:00
-- url     : https://prove2.me/theorems/8ec53fdc-03e6-4b9f-bc1f-2f6a570cf5fe
-- title:
--   Directional prices inherited from the unary phase
-- statement:
--   For the output of phase zero, let $g(a)$ be the phase-zero effective forbidden guard rank and let $t(n)$ be its zero-failure target rank. Define the directional prices
--   $$
--   R_1(a,n)=A_{p_0}(g(a),t(n)),\qquad
--   D_1(a,n)=B_{p_0}(g(n),t(a)).
--   $$
--   The functions use the exact initial profile and literal phase-zero recipe. Natural rank arguments are converted to the twelve-rank type as specified by the definitions.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/PairedWarmData.lean lines 7–21; SHA256 db80f9c119bc75a3991b6c379eb30fc8f6be4fd34b7a3bf34da8d4f04d26c4bc; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_BaselineLossNumeric
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericData
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Range

namespace SensitivityPairedWarmData
end SensitivityPairedWarmData



namespace SensitivityPairedWarmData

def phase1Guard (a : ℕ) : ℕ :=
  let r := SensitivityBaselineLossNumeric.phase0
  let i : Fin 12 := Fin.ofNat 12 a
  if r.hard i < 12 then r.hard i else r.soft i

def phase1Target (n : ℕ) : ℕ :=
  (SensitivityBaselineLossNumeric.phase0.lo (Fin.ofNat 12 n) 0).val

def phase1Rise (a n : ℕ) : ℕ :=
  SensitivityLocalNumeric.entry SensitivityLocalNumeric.input0.profile 0
    (phase1Guard a) (phase1Target n)

def phase1Fall (a n : ℕ) : ℕ :=
  SensitivityLocalNumeric.entry SensitivityLocalNumeric.input0.profile 1
    (phase1Guard n) (phase1Target a)



































































































































































































































































































































































end SensitivityPairedWarmData


