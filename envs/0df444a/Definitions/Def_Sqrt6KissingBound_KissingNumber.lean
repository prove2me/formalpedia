-- Prove2me | Definitions.Def_Sqrt6KissingBound_KissingNumber
-- name    : Sqrt6KissingBound_KissingNumber
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:09:52.26721+00:00
-- url     : https://prove2.me/theorems/2847b85f-5e9d-5114-93ab-40d50e719a24
-- title:
--   Kissing Number
-- statement:
--   Definitions and structural lemmas for Kissing Number, from Sébastien Palcoux (sebastienpalcoux/sqrt6-kissing-bound; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned The universal square-root-of-six exponential base bound for Euclidean kissing numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingNumber.lean

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
set_option autoImplicit true
namespace Sqrt6KissingBound
noncomputable section
def RealizableKissingCard (n m : ℕ) : Prop :=
  ∃ X : Finset (EuclideanSpace ℝ (Fin n)),
    IsKissingConfiguration X ∧ X.card = m
def kissingNumberCeiling (n : ℕ) : ℕ :=
  ⌊(Real.sqrt 6) ^ n⌋₊
def kissingNumber (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest (RealizableKissingCard n) (kissingNumberCeiling n)
end
end Sqrt6KissingBound


