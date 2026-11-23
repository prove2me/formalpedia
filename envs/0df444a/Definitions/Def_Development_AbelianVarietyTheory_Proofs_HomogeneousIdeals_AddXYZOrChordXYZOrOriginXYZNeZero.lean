-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:21.385473+00:00
-- url     : https://prove2.me/theorems/76a28a27-ffc7-4607-b0d9-250d934b1da4
-- title:
--   Add XYZOr Chord XYZOr Origin XYZNe Zero
-- statement:
--   Definitions and structural lemmas for Add XYZOr Chord XYZOr Origin XYZNe Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddXYZOrChordXYZOrOriginXYZNeZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
namespace GlobalTheory.AddLaw
section Ring
variable {R S : Type*} [CommRing R] [CommRing S]
def Proportional (T U : Fin 3 → R) : Prop :=
  ∀ i j, T i * U j = T j * U i
variable {W : Projective R}
variable (W) in

def chordN (x₁ y₁ x₂ : R) : R :=
  x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁
variable (W) in

def chordD (y₁ x₂ y₂ : R) : R :=
  y₁ + y₂ + W.a₁ * x₂ + W.a₃
variable (W) in

def slopeXYZ (x₁ y₁ x₂ n d : R) : Fin 3 → R :=
  W.neg ![d * (n ^ 2 + W.a₁ * n * d - (W.a₂ + x₁ + x₂) * d ^ 2),
    n * (n ^ 2 + W.a₁ * n * d - (W.a₂ + x₁ + x₂) * d ^ 2 - x₁ * d ^ 2) + y₁ * d ^ 3, d ^ 3]
variable (W) in

def chordXYZ (x₁ y₁ x₂ y₂ : R) : Fin 3 → R :=
  slopeXYZ W x₁ y₁ x₂ (chordN W x₁ y₁ x₂) (chordD W y₁ x₂ y₂)
variable (W) in

def thirdXYZ (s n v d : R) : Fin 3 → R :=
  ![d * (-lineQuadCoeff W n v d - lineCubicCoeff W n d * s), -(d * lineCubicCoeff W n d),
    n * (-lineQuadCoeff W n v d - lineCubicCoeff W n d * s) + v * lineCubicCoeff W n d]
variable (W) in

def originXYZ (z₁ w₁ z₂ w₂ : R) : Fin 3 → R :=
  W.neg (thirdXYZ W (z₁ + z₂) (originN W z₁ w₁ z₂)
    (w₁ * originD W w₁ z₂ w₂ - originN W z₁ w₁ z₂ * z₁) (originD W w₁ z₂ w₂))
end Ring
section Field
variable {F : Type*} [Field F] {W : Projective F}
variable (W) in

def Represents (T : Fin 3 → F) (p : W.toAffine.Point) : Prop :=
  W.Nonsingular T ∧ Point.toAffine W T = p
variable [DecidableEq F]
end Field
end GlobalTheory.AddLaw


