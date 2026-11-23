-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:53:38.722989+00:00
-- url     : https://prove2.me/theorems/4bd5b697-739c-4d13-842c-22ee75434481
-- title:
--   Norm EDS
-- statement:
--   Definitions and structural lemmas for Norm EDS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/NormEDS.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
section Step
variable {R : Type*} [CommRing R] [IsDomain R]
end Step
def SomosAt {R : Type*} [CommRing R] (w : ℤ → R) (b c : R) (n : ℤ) : Prop :=
  w (n + 2) * w (n - 2) = b ^ 2 * w (n + 1) * w (n - 1) - c * w n ^ 2
def InvAt {R : Type*} [CommRing R] (w : ℤ → R) (b c d : R) (n : ℤ) : Prop :=
  c * (w (n + 2) * w (n - 1) ^ 2 + w (n - 2) * w (n + 1) ^ 2) =
    (b ^ 4 + d) * w (n - 1) * w n * w (n + 1) - b ^ 2 * c * w n ^ 3
section Induction
variable {R : Type*} [CommRing R] [IsDomain R] (b c d : R)
end Induction
section Universal
open MvPolynomial
noncomputable def uw (n : ℤ) : MvPolynomial (Fin 3) ℤ :=
  normEDS (X 0) (X 1) (X 2) n
end Universal
variable {R : Type*} [CommRing R] (b c d : R)
end GroundTheory.Arith.Abelian


