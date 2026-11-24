-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:43:26.373372+00:00
-- url     : https://prove2.me/theorems/e73c50be-357c-4d94-a959-107515a45edb
-- title:
--   Equivariant Parts Of Finite Type
-- statement:
--   Definitions and structural lemmas for Equivariant Parts Of Finite Type, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/EquivariantPartsOfFiniteType.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace PI.KLW
section conj
variable {K E : Type} [Field K] [Field E] [CharZero E] [Algebra K E]
def conjK (cj : E ≃ₐ[ℚ] E) (h : ∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') :
    K →+* K where
  toFun k := Classical.choose (h k)
  map_one' := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h 1)) = algebraMap K E 1
    rw [← Classical.choose_spec (h 1)]; simp
  map_mul' x y := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h (x * y))) =
      algebraMap K E (Classical.choose (h x) * Classical.choose (h y))
    have hs : ∀ k, algebraMap K E (Classical.choose (h k)) = cj (algebraMap K E k) :=
      fun k => (Classical.choose_spec (h k)).symm
    rw [hs (x * y), map_mul (algebraMap K E) (Classical.choose (h x)), hs x, hs y, map_mul, map_mul]
  map_zero' := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h 0)) = algebraMap K E 0
    rw [← Classical.choose_spec (h 0)]; simp
  map_add' x y := by
    apply (algebraMap K E).injective
    show algebraMap K E (Classical.choose (h (x + y))) =
      algebraMap K E (Classical.choose (h x) + Classical.choose (h y))
    have hs : ∀ k, algebraMap K E (Classical.choose (h k)) = cj (algebraMap K E k) :=
      fun k => (Classical.choose_spec (h k)).symm
    rw [hs (x + y), map_add (algebraMap K E) (Classical.choose (h x)), hs x, hs y, map_add, map_add]
end conj
section rp
variable {K : Type} [Field K] [NumberField K] {p : ℕ}
end rp
section main
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
def Lset {n : Type} [Fintype n] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ)
    (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : Set (Fin 4 × n → K) :=
  {v | ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : E) * g₀.symm v a ∈ I}
end main
end PI.KLW


