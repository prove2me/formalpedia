-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_AdaptiveSubstitutionBound
-- name    : Formalism_CyclotomicNorms_NonsquarefreeBounds_AdaptiveSubstitutionBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:34.105141+00:00
-- url     : https://prove2.me/theorems/1e977ffe-6c1e-4fe3-b77a-6fa6ef705d90
-- title:
--   Adaptive Substitution Bound
-- statement:
--   Definitions and structural lemmas for Adaptive Substitution Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/AdaptiveSubstitutionBound.lean

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SubstitutionBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.CyclotomicNorms
namespace AdaptiveSubstitution
def step (ℓ A : ℕ) (B : List ℕ → ℕ) (L : List ℕ) : ℕ :=
  B L + A * (L.map (ℓ ^ ·)).sum + L.sum + 1
def pre (ℓ A : ℕ) (B : List ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre ℓ A B n ++ [step ℓ A B (pre ℓ A B n)]
end AdaptiveSubstitution
end Formalism.CyclotomicNorms


