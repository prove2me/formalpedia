-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DualFockLinear_OpBound
-- name    : Formalism_SharpRestriction_GrowthBounds_DualFockLinear_OpBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:23.977654+00:00
-- url     : https://prove2.me/theorems/0ccf1a2f-0f08-49d6-8230-d21bde1005e0
-- title:
--   Op Bound
-- statement:
--   Definitions and structural lemmas for Op Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/DualFockLinear/OpBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.MainNotions.TestSideCounting
def Ed (K : Type) [Field K] (k d : ℕ) (a b : Fin k) :
    ↥(homogeneousSubmodule (Fin k) K d) →ₗ[K] ↥(homogeneousSubmodule (Fin k) K d) where
  toFun F := ⟨X a * pderiv b (F : MvPolynomial (Fin k) K), by
    have hF : (F : MvPolynomial (Fin k) K).IsHomogeneous d := (mem_homogeneousSubmodule d _).1 F.2
    rw [mem_homogeneousSubmodule]
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      have : (F : MvPolynomial (Fin k) K) = C (coeff 0 (F : MvPolynomial (Fin k) K)) :=
        (totalDegree_eq_zero_iff_eq_C).1 (Nat.le_zero.1 hF.totalDegree_le)
      rw [this, pderiv_C, mul_zero]
      exact isHomogeneous_zero _ _ _
    · have h1 := hF.pderiv (i := b)
      have h2 := (isHomogeneous_X K a).mul h1
      have e : 1 + (d - 1) = d := by omega
      rw [e] at h2
      exact h2⟩
  map_add' F G := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' t F := by
    apply Subtype.ext
    simp [mul_smul_comm]
def EdWord (K : Type) [Field K] (k d : ℕ) (l : List (Fin k × Fin k)) :
    Module.End K ↥(homogeneousSubmodule (Fin k) K d) :=
  (l.map fun y => Ed K k d y.1 y.2).prod
def OpBound : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k d c : ℕ)
    (WW : Submodule K (Module.End K ↥(homogeneousSubmodule (Fin k) K d)))
    (Sg : Set (Module.End K ↥(homogeneousSubmodule (Fin k) K d))),
    (∀ A ∈ WW, ∀ a b : Fin k, Ed K k d a b * A - A * Ed K k d a b ∈ WW) →
    WW = Submodule.span K Sg →
    (∀ A ∈ Sg, ∃ ω : Fin k → ℤ, (∀ a, Ed K k d a a * A - A * Ed K k d a a = (ω a : K) • A) ∧ ∀ a, ω a ≤ c) →
    ∀ A ∈ WW, A ∈ Submodule.span K {B | ∃ l : List (Fin k × Fin k), l.length ≤ c ∧ B = EdWord K k d l}
def JacobiMinor : Prop :=
  ∀ (n s t : ℕ), 1 ≤ s → s + t = n → ∀ (I J : Fin s → Fin n) (Ic Jc : Fin t → Fin n),
    StrictMono I → StrictMono J → StrictMono Ic → StrictMono Jc →
    (∀ x, (x ∈ Set.range I) ↔ x ∉ Set.range Ic) → (∀ x, (x ∈ Set.range J) ↔ x ∉ Set.range Jc) →
    ∃ e : ℕ, ∀ (R : Type) [CommRing R] (A : Matrix (Fin n) (Fin n) R),
      (A.adjugate.submatrix I J).det = (-1) ^ e * A.det ^ (s - 1) * (A.submatrix Jc Ic).det
end Formalism.MainNotions.TestSideCounting


