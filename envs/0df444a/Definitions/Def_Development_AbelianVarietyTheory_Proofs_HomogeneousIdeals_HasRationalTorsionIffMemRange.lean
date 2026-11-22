-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasRationalTorsionIffMemRange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:45.22463+00:00
-- url     : https://prove2.me/theorems/90aea885-c633-48ba-bebe-17368c7bf1c8
-- title:
--   Has Rational Torsion Iff Mem Range
-- statement:
--   Definitions and structural lemmas for Has Rational Torsion Iff Mem Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasRationalTorsionIffMemRange.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsLineOfAddAddEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
section Def
variable {K : Type*} [Field K]
open scoped Classical in

def HasRationalTorsion (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L] (n : ℕ) :
    Prop :=
  ∀ (x y : L) (h : (W.baseChange L).toAffine.Nonsingular x y), n • Point.some x y h = 0 →
    x ∈ (algebraMap K L).range ∧ y ∈ (algebraMap K L).range
variable {W : WeierstrassCurve K} {L : Type*} [Field L] [Algebra K L] {m n : ℕ}
end Def
def splitCurve {R : Type*} [CommRing R] (A B : R) : WeierstrassCurve R :=
  ⟨0, -(A + B), 0, A * B, 0⟩
def legendreCurve {R : Type*} [CommRing R] (l : R) : WeierstrassCurve R :=
  ⟨0, -(1 + l), 0, l, 0⟩
def deuringCurve {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R :=
  ⟨a, 0, b, 0, 0⟩
section Invariants
variable {R : Type*} [CommRing R]
end Invariants
section Roots
variable {L : Type*} [Field L] [IsAlgClosed L]
end Roots
section Flex
variable {F : Type*} [Field F] {W : WeierstrassCurve F}
end Flex
section Forms
variable {K : Type*} [Field K] [CharZero K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]
end Forms
end GlobalTheory


