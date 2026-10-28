-- Prove2me | Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
-- name    : D1Bound5_MixedRootMatrixSigns_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:05:45.198582+00:00
-- url     : https://prove2.me/theorems/9cd65c20-da3f-4af4-a0c8-4089b6dbf06a
-- title:
--   Mixed Root Matrix Signs
-- statement:
--   Two scalar perturbation bounds for an integral root and chosen complex square roots. The named objects in this bundle include `SignedEntryBounds`, `MixedSignedEntryGood`.
-- source:
--   D1Bound5/MixedRootMatrixSigns.lean, lines 6-10, SHA-256 2e004ca5529f8e5abf67259e26a8270075f09b04d9c8093e81458a83e3680457; D1Bound5/MixedRootMatrixSigns.lean, lines 82-90, SHA-256 2e004ca5529f8e5abf67259e26a8270075f09b04d9c8093e81458a83e3680457. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- Two scalar perturbation bounds for an integral root and chosen complex square roots. -/
def SignedEntryBounds {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a b : R) (u v : ℂ) (r : R) (rho eta : ℝ) : Prop :=
  ‖u * f r * v - f a * f b‖ < rho ∧
  ‖(u * f r * v - f a * f b) - (1/2 : ℂ)‖ < eta









/-- Row-dependent estimates: pairs meeting zero use the three-bound;
all other pairs use the nine-bound, yielding the tighter later constants. -/
def MixedSignedEntryGood {R : Type*} [CommRing R]
    (f : R →+* ℂ) (a : Fin 4 → R) (u : Fin 4 → ℂ)
    (i j : Fin 4) (r : R) : Prop :=
  if i = 0 ∨ j = 0 then
    SignedEntryBounds f (a i) (a j) (u i) (u j) r (5/9) (25/486)
  else
    SignedEntryBounds f (a i) (a j) (u i) (u j) r (7/13) (1/64)





end D1Bound5
namespace D1Bound5





end D1Bound5
end


