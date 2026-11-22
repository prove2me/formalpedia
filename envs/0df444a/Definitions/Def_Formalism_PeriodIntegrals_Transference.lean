-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_Transference
-- name    : Formalism_PeriodIntegrals_Transference
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:06.195117+00:00
-- url     : https://prove2.me/theorems/b908cec6-4e4e-4ee1-9f95-5df0457cb134
-- title:
--   Transference
-- statement:
--   Definitions and structural lemmas for Transference, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/Transference.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped InnerProductSpace
noncomputable section
namespace PI
def TransferenceCover : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ), 0 < lam →
    (∀ y : E, y ≠ 0 → (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) → lam ≤ ‖y‖) →
    ∀ x : E, ∃ l ∈ Λ, ‖x - l‖ * lam ≤ (finrank ℝ E : ℝ) / 2
def succMin {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin i → EuclideanSpace ℝ (Fin N),
    (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}
def dualZ {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Submodule ℤ (EuclideanSpace ℝ (Fin N)) where
  carrier := {x | ∀ y ∈ M, ∃ z : ℤ, ⟪x, y⟫_ℝ = z}
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨z1, h1⟩ := ha y hy
    obtain ⟨z2, h2⟩ := hb y hy
    exact ⟨z1 + z2, by rw [inner_add_left, h1, h2]; push_cast; ring⟩
  zero_mem' := fun y _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha y hy
    obtain ⟨z, h⟩ := ha y hy
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, real_inner_smul_left, h]; push_cast; ring⟩
def TransferenceMinima : Prop :=
  ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))),
    DiscreteTopology M → Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ →
    ∀ i, 1 ≤ i → i ≤ N → succMin M i * succMin (dualZ M) (N + 1 - i) ≤ N
end PI


