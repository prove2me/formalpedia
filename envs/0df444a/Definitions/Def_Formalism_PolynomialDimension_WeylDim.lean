-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_WeylDim
-- name    : Formalism_PolynomialDimension_WeylDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:30.019059+00:00
-- url     : https://prove2.me/theorems/bebca62f-dae4-4b11-a5d0-3aa839be833b
-- title:
--   Weyl Dim
-- statement:
--   Definitions and structural lemmas for Weyl Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/WeylDim.lean

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
open scoped BigOperators
namespace Formalism.CountingSumsFrames
def weylDim (n : ℕ) (lam : Fin n → ℤ) : ℚ :=
  ∏ i : Fin n, ∏ j : Fin n,
    if i < j then (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))
    else 1
end Formalism.CountingSumsFrames


