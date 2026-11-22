-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadRoots
-- name    : Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadRoots
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:54.937534+00:00
-- url     : https://prove2.me/theorems/199fb63b-ddc6-4e76-8906-87fef26ac51f
-- title:
--   Quad Roots
-- statement:
--   Definitions and structural lemmas for Quad Roots, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/QuadRoots.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
open Polynomial
def qrGood (p n : ℕ) (W : Type) [CommRing W] (b c : W) : Prop :=
  ((X ^ 2 + C (Ideal.Quotient.mk (Ideal.span {(p : W)}) b) * X + C (Ideal.Quotient.mk (Ideal.span {(p : W)}) c) :
      (W ⧸ Ideal.span {(p : W)})[X]) ∣ X ^ ((p ^ n) ^ 2) - X) ∧
    ∀ x : W ⧸ Ideal.span {(p : W)},
      x ^ 2 + Ideal.Quotient.mk (Ideal.span {(p : W)}) b * x + Ideal.Quotient.mk (Ideal.span {(p : W)}) c ≠ 0
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis


