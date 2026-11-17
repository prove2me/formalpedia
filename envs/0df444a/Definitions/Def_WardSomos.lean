-- Prove2me | Definitions.Def_WardSomos
-- name    : WardSomos
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:11.727207+00:00
-- url     : https://prove2.me/theorems/b74958ad-ce4c-489e-97a1-148c55d1c312
-- title:
--   The adjacent Somos-4 relation
-- statement:
--   For a normalized elliptic divisibility sequence $W_n$, the file defines the adjacent recurrence predicate $$W_{m+2}W_{m-2}=b^2W_{m+1}W_{m-1}-cW_m^2.$$ This relation is the local Somos-4 identity from which the conservation and invariant modules are built.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The adjacent Somos relation at an integer index. -/
@[expose] public def AdjRel (b c d : R) (m : ℤ) : Prop :=
  normEDS b c d (m + 2) * normEDS b c d (m - 2)
    = b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
        - c * normEDS b c d m ^ 2

end FLT.EDS


