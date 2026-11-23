-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_AlgebraTools_IsCplAtSelf
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_AlgebraTools_IsCplAtSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:50.426219+00:00
-- url     : https://prove2.me/theorems/959d8ffc-18a2-4bb5-87e9-93cd074388fc
-- title:
--   Is Cpl At Self
-- statement:
--   Definitions and structural lemmas for Is Cpl At Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/AlgebraTools/IsCplAtSelf.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
namespace UpperTheory.V.AlgebraTools
structure IsCplAt (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B]
    [Algebra R B] : Prop where
  noeth : IsNoetherianRing B
  complete : IsAdicComplete (maximalIdeal B) B
  comap_eq : (maximalIdeal B).comap (algebraMap R B) = p
  dense : ∀ (n : ℕ) (b : B), ∃ a s : R, s ∉ p ∧
    algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n
  strict : ∀ (n : ℕ) (a : R), algebraMap R B a ∈ maximalIdeal B ^ n → ∃ s : R, s ∉ p ∧ s * a ∈ p ^ n
abbrev CplAt (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime] : Type :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)
end UpperTheory.V.AlgebraTools


