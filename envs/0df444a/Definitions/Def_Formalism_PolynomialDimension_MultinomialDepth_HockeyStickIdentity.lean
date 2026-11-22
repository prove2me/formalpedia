-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity
-- name    : Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:16.207514+00:00
-- url     : https://prove2.me/theorems/756ec570-255a-42dd-a7a1-703760694699
-- title:
--   Hockey Stick Identity
-- statement:
--   Definitions and structural lemmas for Hockey Stick Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/HockeyStickIdentity.lean

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.CountingSumsFrames
def digitSum {m P : ℕ} (τ : Fin m → Fin P) : ℕ := ∑ i, (τ i : ℕ)
end Formalism.CountingSumsFrames


