-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarDegree_ScalDegMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:17.766702+00:00
-- url     : https://prove2.me/theorems/233405e6-2299-473d-96cc-9de4d7bf80d4
-- title:
--   Scal Deg Main
-- statement:
--   Definitions and structural lemmas for Scal Deg Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarDegree/ScalDegMain.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScalDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScalDeg
open MvPolynomial PI.ScalDeg
def gv {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ) (k : FrV T N) :
    MvPolynomial (Idx T N N') ℂ :=
  ∑ b : Fin N', C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
    X ((k.1, b, k.2.1) : Idx T N N')
end PI.UnitaryGroupMassFormula.ScalDeg


