-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_BadShare
-- name    : Development_AutomorphicArithmetic_MeanSquareBounds_BadShare
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:57.80586+00:00
-- url     : https://prove2.me/theorems/9b4fe10d-091e-45de-9cce-b771fd98af82
-- title:
--   Bad Share
-- statement:
--   Definitions and structural lemmas for Bad Share, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/BadShare.lean

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open scoped ArithmeticFunction.vonMangoldt
open Filter MeasureTheory
namespace QH
noncomputable def bsD (Z v : ℝ) (q : ℕ) (κ : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Icc 1 ⌊Z⌋₊,
    if v < (m : ℝ) then ((Λ m : ℝ) : ℂ) * κ m * ((jacobiSym (m : ℤ) q : ℤ) : ℂ) / m else 0
end QH


