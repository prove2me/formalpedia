-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_KoszulImageInIdeal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_KoszulImageInIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:51.638936+00:00
-- url     : https://prove2.me/theorems/8e199a04-b2bc-4d1e-82d4-cde7514d0184
-- title:
--   Koszul Image In Ideal
-- statement:
--   Definitions and structural lemmas for Koszul Image In Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/KoszulExactness/KoszulImageInIdeal.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KoszulExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace PI.KEX
open PI.KoszulExact
def P {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) : Prop :=
  ∀ (j : ℕ) (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ (j + 1) →
    dK s x = 0 → ∃ y ∈ Li R D i ^ (j + 2), dK s y = x
def F1 : Prop :=
  ∀ (R : Type u) [CommRing R] (D j : ℕ), ⋀[R]^j (Fin D → R) = Li R D D ^ j
def KoszulLowersPower : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (i j : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ (j + 1) → dK s x ∈ Li R D i ^ j
def KoszulImageInIdeal : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (i : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D i ^ 1 →
      ∃ r ∈ Ii s i, dK s x = algebraMap R _ r
def secondLeviFamily : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (i : ℕ) (r : R), r ∈ Ii s i →
      ∃ y ∈ Li R D i ^ 1, dK s y = algebraMap R _ r
def F3 : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (i : Fin D) (j : ℕ)
    (x : ExteriorAlgebra R (Fin D → R)), x ∈ Li R D ((i : ℕ) + 1) ^ (j + 1) →
      ∃ a ∈ Li R D i ^ (j + 1), ∃ b ∈ Li R D i ^ j, x = a + eb R i * b
def F4 : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (i : Fin D) (m n : ℕ)
    (u v : ExteriorAlgebra R (Fin D → R)), u ∈ Li R D i ^ m → v ∈ Li R D i ^ n →
      u + eb R i * v = 0 → v = 0
def W : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
    ∀ (i : Fin D) (r : R), s i * r ∈ Ii s i → r ∈ Ii s i
def Step : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R),
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s) →
    ∀ i : Fin D, P s i → P s ((i : ℕ) + 1)
def Sec : Prop :=
  ∀ (R : Type u) [CommRing R] (D : ℕ) (s : Fin D → R) (r : R),
    (∃ y ∈ ⋀[R]^1 (Fin D → R), dK s y = algebraMap R _ r) ↔ r ∈ Ideal.span (Set.range s)
end PI.KEX


