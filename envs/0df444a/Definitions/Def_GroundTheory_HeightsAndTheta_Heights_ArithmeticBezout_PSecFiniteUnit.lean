-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecFiniteUnit
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSecFiniteUnit
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:29.854369+00:00
-- url     : https://prove2.me/theorems/73b2fa25-3df8-49a8-aa8a-10b51d58c517
-- title:
--   PSec Finite Unit
-- statement:
--   Definitions and structural lemmas for PSec Finite Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSecFiniteUnit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSecFiniteUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_AssemblyPartial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial Vertical
noncomputable section
namespace SecFiniteUnit
variable {k R : Type} [Field k] [CommRing R] [Algebra k R] {n e : ℕ}
def lineSub (y : Par e n → R) (m : Fin n) (ij : Fin (e + 1) × Fin n) : Polynomial R :=
  Fin.cases (motive := fun _ => Polynomial R)
    (Polynomial.C (y (.inr ij.2)) * Polynomial.X - if ij.2 = m then 1 else 0)
    (fun i => Polynomial.C (y (.inl (i, ij.2)))) ij.1
def lineTop (y : Par e n → R) (ij : Fin (e + 1) × Fin n) : R :=
  Fin.cases (motive := fun _ => R) (y (.inr ij.2)) (fun i => y (.inl (i, ij.2))) ij.1
end SecFiniteUnit
end
end GroundTheory.Heights₂.Heights


