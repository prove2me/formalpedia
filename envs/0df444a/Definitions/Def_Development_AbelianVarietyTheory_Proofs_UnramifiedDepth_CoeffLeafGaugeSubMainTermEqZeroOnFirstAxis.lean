-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:24.456469+00:00
-- url     : https://prove2.me/theorems/882ab6f5-9d77-438e-98dd-d758c02075a8
-- title:
--   Coeff Leaf Gauge Sub Main Term Eq Zero On First Axis
-- statement:
--   Definitions and structural lemmas for Coeff Leaf Gauge Sub Main Term Eq Zero On First Axis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
namespace GlobalTheory.MainTerm.Axis
variable {C : Type} [Field C] {ι ι' : Type}
def VanishesOnFirstAxis (F : MvPowerSeries (ι ⊕ ι') C) : Prop :=
  ∀ μ : ι ⊕ ι' →₀ ℕ, (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ F = 0
end GlobalTheory.MainTerm.Axis


