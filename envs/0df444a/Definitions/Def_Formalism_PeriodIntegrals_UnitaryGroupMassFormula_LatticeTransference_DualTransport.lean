-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_DualTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:41.132168+00:00
-- url     : https://prove2.me/theorems/63597b07-fd40-476f-bcb0-d349d99043ac
-- title:
--   Dual Transport
-- statement:
--   Definitions and structural lemmas for Dual Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeTransference/DualTransport.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped Real
noncomputable section
namespace PI.Tr
def dualLat {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (Λ : Submodule ℤ E) :
    Submodule ℤ E where
  carrier := {y | ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z1, h1⟩ := ha x hx
    obtain ⟨z2, h2⟩ := hb x hx
    exact ⟨z1 + z2, by rw [inner_add_right, h1, h2]; push_cast; ring⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha x hx
    obtain ⟨z, h⟩ := ha x hx
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, real_inner_smul_right, h]; push_cast; ring⟩
def PoissonGauss : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    (∀ t : ℝ, 0 < t → ∀ v : E, Summable fun x : Λ => Real.exp (-π * t * ‖(x : E) + v‖ ^ 2)) ∧
    (∀ t : ℝ, 0 < t → Summable fun y : dualLat Λ => Real.exp (-π * ‖(y : E)‖ ^ 2 / t)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → ∀ v : E,
      ∑' x : Λ, Real.exp (-π * t * ‖(x : E) + v‖ ^ 2) =
        c * t ^ (-(finrank ℝ E : ℝ) / 2) *
          ∑' y : dualLat Λ, Real.exp (-π * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * π * inner ℝ (y : E) v)
def PoissonBasis : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ι : Type) [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ E) (b' : ι → E),
    (∀ i j, inner ℝ (b i) (b' j) = if i = j then (1 : ℝ) else 0) →
    (∀ t : ℝ, 0 < t → ∀ v : E,
      Summable fun k : ι → ℤ => Real.exp (-π * t * ‖(∑ i, (k i : ℝ) • b i) + v‖ ^ 2)) ∧
    (∀ t : ℝ, 0 < t → Summable fun m : ι → ℤ => Real.exp (-π * ‖∑ i, (m i : ℝ) • b' i‖ ^ 2 / t)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → ∀ v : E,
      ∑' k : ι → ℤ, Real.exp (-π * t * ‖(∑ i, (k i : ℝ) • b i) + v‖ ^ 2) =
        c * t ^ (-(finrank ℝ E : ℝ) / 2) *
          ∑' m : ι → ℤ, Real.exp (-π * ‖∑ i, (m i : ℝ) • b' i‖ ^ 2 / t) *
            Real.cos (2 * π * inner ℝ (∑ i, (m i : ℝ) • b' i) v)
def DualTransport : Prop := PoissonBasis → PoissonGauss
def KeyDim (P : ℕ → Prop) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ) (u : E), P (finrank ℝ E) →
    0 < lam →
    (∀ y : E, (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) → ‖y‖ < lam →
      ∃ m : ℤ, inner ℝ u y = (m : ℝ)) →
    ∃ l ∈ Λ, ‖u - l‖ * lam ≤ (finrank ℝ E : ℝ) / 2
def KeyLarge : Prop := KeyDim (fun n => 2 ≤ n)
def KeySmall : Prop := KeyDim (fun n => n ≤ 1)
def GaussStep : Prop := PoissonGauss → KeyLarge
end PI.Tr


