-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_EagonNorthcott
-- name    : Formalism_PeriodIntegrals_EagonNorthcott
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:08.88445+00:00
-- url     : https://prove2.me/theorems/94b54b68-a17d-4097-87ca-e72e2df8e1be
-- title:
--   Eagon Northcott
-- statement:
--   Definitions and structural lemmas for Eagon Northcott, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/EagonNorthcott.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EagonNorthcott
def lin {R : Type*} [CommRing R] {D : ℕ} (x : Fin D → R) (c : Fin D → ℤ) : R :=
  ∑ i, (c i : R) * x i
def dmap {R : Type*} [CommRing R] {D m n : ℕ} (x : Fin D → R) (C : Matrix (Fin m) (Fin n) (Fin D → ℤ)) :
    (Fin n → R) →ₗ[R] (Fin m → R) :=
  Matrix.mulVecLin (C.map (lin x))
def aug {R : Type*} [CommRing R] {D m : ℕ} (x : Fin D → R) (e : Fin m → Fin D → ℕ) : (Fin m → R) →ₗ[R] R :=
  ∑ k, (∏ i, x i ^ e k i) • (LinearMap.proj k : (Fin m → R) →ₗ[R] R)
def Shape (D a : ℕ) (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ)
    (_C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)) : Prop :=
  (∀ j, max D 1 ≤ j → n j = 0) ∧ Function.Injective e ∧ ∀ α : Fin D → ℕ, α ∈ Set.range e ↔ ∑ i, α i = a
def Resolves {R : Type*} [CommRing R] {D : ℕ} (x : Fin D → R) (a : ℕ) {n : ℕ → ℕ} (e : Fin (n 0) → Fin D → ℕ)
    (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)) : Prop :=
  LinearMap.range (aug x e) = Ideal.span (Set.range x) ^ a ∧
    LinearMap.ker (aug x e) = LinearMap.range (dmap x (C 0)) ∧
    ∀ j, LinearMap.ker (dmap x (C j)) = LinearMap.range (dmap x (C (j + 1)))
end PI.EagonNorthcott
namespace PI
open EagonNorthcott in

def EagonNorthcott.{u} : Prop :=
  ∀ D a : ℕ, ∃ (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)),
    Shape D a n e C ∧
      ∀ (R : Type u) [CommRing R] (x : Fin D → R),
        RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) → Resolves x a e C
end PI


