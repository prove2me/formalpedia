-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiCoord
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_PiCoord
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T07:56:14.27532+00:00
-- url     : https://prove2.me/theorems/6bbfea26-edd8-4004-85b3-bf6b4b1ee5db
-- title:
--   Pi Coord
-- statement:
--   Definitions and structural lemmas for Pi Coord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/PiCoord.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.AprimeInfG
open MeasureTheory Set
open scoped ENNReal
def piProdEquiv {V : Type} (A B : V → Type) [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSpace (B v)] :
    (∀ v, A v × B v) ≃ᵐ (∀ v, A v) × (∀ v, B v) where
  toFun z := (fun v => (z v).1, fun v => (z v).2)
  invFun p v := (p.1 v, p.2 v)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_pi_lambda _ fun v => measurable_fst.comp (measurable_pi_apply v)).prodMk
    (measurable_pi_lambda _ fun v => measurable_snd.comp (measurable_pi_apply v))
  measurable_invFun := measurable_pi_lambda _ fun v =>
    ((measurable_pi_apply v).comp measurable_fst).prodMk ((measurable_pi_apply v).comp measurable_snd)
end PI.AprimeInfG


