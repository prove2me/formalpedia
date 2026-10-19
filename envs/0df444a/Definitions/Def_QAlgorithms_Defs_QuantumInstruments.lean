-- Prove2me | Definitions.Def_QAlgorithms_Defs_QuantumInstruments
-- name    : QAlgorithms_Defs_QuantumInstruments
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:14:32.260769+00:00
-- url     : https://prove2.me/theorems/34c56713-a417-4594-9418-007d0da9d227
-- title:
--   QuantumInstruments
-- statement:
--   QuantumInstruments
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\QuantumInstruments.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix

namespace QAlgorithms.CopyMeasurements

variable {n m d k b w M K N c out : ℕ}

/-- Finite Kraus instrument (2011.10908 pp.9–10; 1711.01053 pp.12–13).
Branches retain subnormalized states, and their sum is trace preserving. -/
structure QuantumInstrument (I O : Type*) [Fintype I] [DecidableEq I] [Fintype O] where
  multiplicity : O → ℕ
  kraus : (o : O) → Fin (multiplicity o) → Matrix I I ℂ
  complete : ∑ o, ∑ j, (kraus o j)ᴴ * kraus o j = 1

/-- Actual branch transformation (2011.10908 p.10), including zero branches. -/
def instrumentBranch {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (M : QuantumInstrument I O) (o : O) : Superop I I :=
  krausApply (M.kraus o)

/-- Deterministic identity instrument, the no-measurement case of
2011.10908 pp.9–10. -/
abbrev identityInstrument (I : Type*) [Fintype I] [DecidableEq I] : QuantumInstrument I Unit where
  multiplicity := fun _ => 1
  kraus := fun _ _ => 1
  complete := by simp

/-- Sanity check for the modeled source objects (arxiv-2011.10908v4, PDF pp.9,10,22; arxiv-1711.01053v2, PDF pp.2,12,13,16). -/
example {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) :
    instrumentBranch (identityInstrument I) () X = X := by
  simp [instrumentBranch, krausApply, identityInstrument]

/-- Sanity check for the modeled source objects (arxiv-2011.10908v4, PDF pp.9,10,22; arxiv-1711.01053v2, PDF pp.2,12,13,16). -/
example {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    (M : QuantumInstrument I O) (o : O) : instrumentBranch M o 0 = 0 := by
  simp [instrumentBranch, krausApply]

end QAlgorithms.CopyMeasurements


