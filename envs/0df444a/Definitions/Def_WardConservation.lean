-- Prove2me | Definitions.Def_WardConservation
-- name    : WardConservation
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:12.052012+00:00
-- url     : https://prove2.me/theorems/d6369e4d-5b51-42de-b093-578589375aba
-- title:
--   The conserved numerator and denominator of a Somos-4 sequence
-- statement:
--   For the normalized elliptic divisibility sequence $W_n$, the file defines $$N_n=W_{n+2}W_{n-1}^2+W_{n+1}^2W_{n-2}+b^2W_n^3$$ and $$D_n=W_{n+1}W_nW_{n-1}.$$ Their ratio is the Ward–Somos conserved quantity. These definitions provide the numerator and denominator used to propagate the elliptic divisibility sequence identities.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The Somos-4 numerator `N_n` and denominator `D_n`; `N_n / D_n` is the conserved quantity. -/
@[expose] public def Nseq (b c d : R) (n : ℤ) : R :=
  normEDS b c d (n+2) * normEDS b c d (n-1)^2
    + normEDS b c d (n+1)^2 * normEDS b c d (n-2) + b^2 * normEDS b c d n ^ 3

@[expose] public def Dseq (b c d : R) (n : ℤ) : R :=
  normEDS b c d (n+1) * normEDS b c d n * normEDS b c d (n-1)

end FLT.EDS


