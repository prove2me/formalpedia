-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
-- name    : Formalism_UnipotentAdelicQuotients_GordanCones
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:01.989008+00:00
-- url     : https://prove2.me/theorems/491f6d49-197c-43d1-b587-e7ecf1a297a9
-- title:
--   Gordan Cones
-- statement:
--   Definitions and structural lemmas for Gordan Cones, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/GordanCones.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
namespace GordanCones
def toQ {n : ℕ} (v : Fin n → ℤ) : Fin n → ℚ := fun i => (v i : ℚ)
def cone {n : ℕ} (s : Finset (Fin n → ℤ)) : Set (Fin n → ℚ) :=
  {x | ∃ c : (Fin n → ℤ) → ℚ, (∀ v ∈ s, 0 ≤ c v) ∧ x = ∑ v ∈ s, c v • toQ v}
def dualCone {n : ℕ} (A : Finset (Fin n → ℤ)) : Set (Fin n → ℚ) :=
  {x | ∀ a ∈ A, 0 ≤ ∑ i, (a i : ℚ) * x i}
def Lattice : Prop :=
  ∀ (n : ℕ) (s : Finset (Fin n → ℤ)), ∃ t : Finset (Fin n → ℤ),
    {x : Fin n → ℤ | toQ x ∈ cone s} = {x | ∃ d : (Fin n → ℤ) → ℕ, x = ∑ v ∈ t, d v • v}
def GenIneq : Prop :=
  (∀ (n : ℕ) (A : Finset (Fin n → ℤ)), ∃ s : Finset (Fin n → ℤ), dualCone A = cone s) ∧
  (∀ (n : ℕ) (s : Finset (Fin n → ℤ)), ∃ A : Finset (Fin n → ℤ), cone s = dualCone A)
def Alternative : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
    (¬ ∃ x : Fin n → ℚ, ∀ i, ∑ j, A i j * x j < b i) ↔
      ∃ y : Fin m → ℚ, (∀ i, 0 ≤ y i) ∧ y ≠ 0 ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ ∑ i, y i * b i ≤ 0
end GordanCones


