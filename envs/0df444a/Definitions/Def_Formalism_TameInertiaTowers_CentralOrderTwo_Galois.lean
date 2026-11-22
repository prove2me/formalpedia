-- Prove2me | Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
-- name    : Formalism_TameInertiaTowers_CentralOrderTwo_Galois
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:21.779835+00:00
-- url     : https://prove2.me/theorems/218a068f-9758-4819-9332-622027791c29
-- title:
--   Galois
-- statement:
--   Definitions and structural lemmas for Galois, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TameInertiaTowers/CentralOrderTwo/Galois.lean

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
namespace Formalism.TwoAdicCyclotomicDecomposition
section Signs
variable {L : Type} [Field L] [NumberField L]
theorem ne_neg_self {x : L} (hx0 : x ≠ 0) : x ≠ -x := by
  intro h
  have : (2 : L) * x = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h2 | h2
  · exact two_ne_zero h2
  · exact hx0 h2
theorem sgn_of_eq {x : L} {ρ : Gal(L/ℚ)} (h : ρ x = x) : sgn ρ x = 1 := by
  simp [sgn, h]
theorem sgn_of_neg {x : L} (hx0 : x ≠ 0) {ρ : Gal(L/ℚ)} (h : ρ x = -x) : sgn ρ x = -1 := by
  have : ρ x ≠ x := by rw [h]; exact fun e => ne_neg_self hx0 e.symm
  simp [sgn, this]
theorem sgn_mul {x : L} (hx0 : x ≠ 0) (hpm : ∀ σ : Gal(L/ℚ), σ x = x ∨ σ x = -x)
    (σ τ : Gal(L/ℚ)) : sgn (σ * τ) x = sgn σ x * sgn τ x := by
  rcases hpm τ with hτ | hτ <;> rcases hpm σ with hσ | hσ
  · rw [sgn_of_eq hσ, sgn_of_eq hτ, sgn_of_eq (by rw [AlgEquiv.mul_apply, hτ, hσ])]; rfl
  · rw [sgn_of_neg hx0 hσ, sgn_of_eq hτ, sgn_of_neg hx0 (by rw [AlgEquiv.mul_apply, hτ, hσ])]; rfl
  · rw [sgn_of_eq hσ, sgn_of_neg hx0 hτ,
      sgn_of_neg hx0 (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ])]; rfl
  · rw [sgn_of_neg hx0 hσ, sgn_of_neg hx0 hτ,
      sgn_of_eq (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ, neg_neg])]; rfl
def sgnHom (x : L) (hx0 : x ≠ 0) (hpm : ∀ σ : Gal(L/ℚ), σ x = x ∨ σ x = -x) :
    Gal(L/ℚ) →* ℤˣ where
  toFun σ := sgn σ x
  map_one' := sgn_of_eq (by simp)
  map_mul' := sgn_mul hx0 hpm
end Signs
section Layer
variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}
end Layer
end Formalism.TwoAdicCyclotomicDecomposition


