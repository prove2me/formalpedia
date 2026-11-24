-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:03.705458+00:00
-- url     : https://prove2.me/theorems/48f825dc-3739-42be-9c62-86e35c8f5222
-- title:
--   Cartier
-- statement:
--   Definitions and structural lemmas for Cartier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Cartier.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
section Local
variable {A : Type*} [CommRing A]
end Local
section Divisors
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
end Divisors
section Vertical
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end Vertical
section Graded
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R] {τ : Type*}
end Graded
section BlowUp
variable {O : Type*} [CommRing O]
abbrev TwoByTwo : Fin 2 → Type := fun _ => Fin 2
def blowUpParam (ϖ : O) : (Σ k : Fin 2, TwoByTwo k) → MvPolynomial (Fin 4) O :=
  fun v => ![![C ϖ * X 0 * X 2, X 1 * X 2], ![X 0 * X 3, X 1 * X 3]] v.1 v.2
def blowUpWeight : Fin 4 → Fin 2 → ℕ := ![0, 0, Pi.single 0 1, Pi.single 1 1]
def blowUpIdeal (ϖ : O) : Ideal (MRing TwoByTwo O) := RingHom.ker (aeval (blowUpParam ϖ))
end BlowUp
section BlowUpModel
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end BlowUpModel
section Nodal
variable {O : Type*} [CommRing O] [IsDomain O]
abbrev TwoByThree : Fin 2 → Type := fun _ => Fin 3
def nodalParam (ϖ : O) : (Σ k : Fin 2, TwoByThree k) → MvPolynomial (Fin 3) O :=
  fun v => ![![X 1 * X 0, X 1 * X 0 ^ 2, X 1 * (1 - C ϖ * X 0 ^ 3)],
    ![X 2 * (C ϖ * X 0 ^ 2), X 2 * X 0, X 2 * (C ϖ ^ 2 * X 0 ^ 3 - 1)]] v.1 v.2
def nodalWeight : Fin 3 → Fin 2 → ℕ := ![0, Pi.single 0 1, Pi.single 1 1]
def nodalIdeal (ϖ : O) : Ideal (MRing TwoByThree O) := RingHom.ker (aeval (nodalParam ϖ))
def nodeParam : (Σ k : Fin 2, TwoByThree k) → MvPolynomial (Fin 3) O :=
  fun v => ![![0, 0, X 1], ![0, 0, -X 2]] v.1 v.2
end Nodal
end
end GroundTheory.Heights₂.Heights.NumbersDVR


