-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
-- name    : Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:22.660261+00:00
-- url     : https://prove2.me/theorems/30106b02-bdf4-4ce8-9158-2f59e31960cc
-- title:
--   Iter Symm R
-- statement:
--   Definitions and structural lemmas for Iter Symm R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/LevelTypeEquivalence/IterSymmR.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.IndefR.Eqv
open scoped ContDiff
def IterSymmR : Prop :=
  ∀ (E H : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H] (g : E → H),
    ContDiff ℝ ∞ g → ∀ (n : ℕ) (x : E) (v : Fin n → E) (σ : Equiv.Perm (Fin n)),
      iteratedFDeriv ℝ n g x (v ∘ σ) = iteratedFDeriv ℝ n g x v
end Formalism.IndefR.Eqv


