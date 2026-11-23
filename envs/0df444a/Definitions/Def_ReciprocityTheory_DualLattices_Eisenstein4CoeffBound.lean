-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
-- name    : ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:41.159696+00:00
-- url     : https://prove2.me/theorems/db965e7c-16c0-4303-b768-243a58c82c60
-- title:
--   Eisenstein4 Coeff Bound
-- statement:
--   Definitions and structural lemmas for Eisenstein4 Coeff Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/Eisenstein4CoeffBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.PGsh
open ModularForm EisensteinSeries ArithmeticFunction PowerSeries UpperHalfPlane
open scoped ArithmeticFunction.sigma
def e4Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)
def e6Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)
def CoeffBd (P : PowerSeries ℤ) (A e : ℕ) : Prop := ∀ n, |P.coeff n| ≤ (A : ℤ) * ((n : ℤ) + 1) ^ e
end ReciprocityTheory.PGsh


