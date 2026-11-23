-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
-- name    : Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_DifferentiableUpdate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:02.508897+00:00
-- url     : https://prove2.me/theorems/6a9c586e-ac24-43d5-b9c9-60bcdf13e5e7
-- title:
--   Differentiable Update
-- statement:
--   Definitions and structural lemmas for Differentiable Update, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/SobolevIteration/DifferentiableUpdate.lean

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
open scoped ContDiff
namespace Formalism.IndefR.Tow.OrbStPf
variable {N : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
def pd (i : Fin N) (f : (Fin N → ℝ) → H) : (Fin N → ℝ) → H :=
  fun p => fderiv ℝ f p (Pi.single i 1)
def pds (L : List (Fin N)) (f : (Fin N → ℝ) → H) : (Fin N → ℝ) → H := L.foldr pd f
end Formalism.IndefR.Tow.OrbStPf
end


