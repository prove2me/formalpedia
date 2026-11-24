-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
-- name    : Formalism_PeriodIntegrals_ScPsiExists
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:34.342214+00:00
-- url     : https://prove2.me/theorems/d1f01e7f-7477-4869-95bf-4364ac17daf5
-- title:
--   Sc Psi Exists
-- statement:
--   Definitions and structural lemmas for Sc Psi Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ScPsiExists.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S
open scoped TensorProduct
namespace PI.ScPsiExists
def psiEinf (I : Formalism.MainNotions.S.AutInst) (x : I.E) : ℂ :=
  ∏ v, Complex.exp (2 * Real.pi * Complex.I * (I.φ v x + star (I.φ v x)))
def Target : Prop :=
  ∀ I : Formalism.MainNotions.S.AutInst, ∃ psiEf : I.E ⊗[I.F] Af I.F → ℂ,
    (∀ x y, psiEf (x + y) = psiEf x * psiEf y) ∧
    (∀ x ∈ IntAf I.F I.E, psiEf x = 1) ∧
    ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Af I.F) x) * psiEinf I x = 1
end PI.ScPsiExists


