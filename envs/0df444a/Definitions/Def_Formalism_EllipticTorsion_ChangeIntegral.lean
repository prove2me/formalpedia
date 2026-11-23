-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_ChangeIntegral
-- name    : Formalism_EllipticTorsion_ChangeIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:49.217173+00:00
-- url     : https://prove2.me/theorems/ba534af8-17fa-49c2-8a46-ce75be8b7690
-- title:
--   Change Integral
-- statement:
--   Definitions and structural lemmas for Change Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/ChangeIntegral.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace Formalism.ELL
def ChangeIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (C : WeierstrassCurve.VariableChange K),
    IntegralModel W → IntegralModel (C • W) → W.Δ ≠ 0 → ‖(C • W).Δ‖ = ‖W.Δ‖ →
      ‖(C.u : K)‖ = 1 ∧ ‖C.r‖ ≤ 1 ∧ ‖C.s‖ ≤ 1 ∧ ‖C.t‖ ≤ 1
end Formalism.ELL


