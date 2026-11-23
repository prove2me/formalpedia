-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:44.878303+00:00
-- url     : https://prove2.me/theorems/c6d5ebdb-542e-422f-96b8-e26e01f135b2
-- title:
--   WSeries
-- statement:
--   Definitions and structural lemmas for WSeries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WSeries.lean

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
namespace WeierstrassSeriesLimit
section Series
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
def T (v : PowerSeries R) : PowerSeries R :=
  X ^ 3 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * X * v ^ 2
      + C W.a₆ * v ^ 3
def E (a b : PowerSeries R) : PowerSeries R :=
  C W.a₁ * X + C W.a₂ * X ^ 2 + C W.a₃ * (a + b) + C W.a₄ * X * (a + b)
    + C W.a₆ * (a ^ 2 + a * b + b ^ 2)
def seq : ℕ → PowerSeries R
  | 0 => 0
  | k + 1 => T W (seq k)
def lim : PowerSeries R := PowerSeries.mk fun n => coeff n (seq W (n + 1))
end Series
section Subst
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
end Subst
end WeierstrassSeriesLimit
end Formalism.ELL


