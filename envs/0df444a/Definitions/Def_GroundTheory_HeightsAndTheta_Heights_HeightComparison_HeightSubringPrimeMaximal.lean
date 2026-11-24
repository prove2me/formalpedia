-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:38.561227+00:00
-- url     : https://prove2.me/theorems/0d69b986-599a-4739-a431-150b64183b2d
-- title:
--   Height Subring Prime Maximal
-- statement:
--   Definitions and structural lemmas for Height Subring Prime Maximal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightSubringPrimeMaximal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField
def SubringPrimeMaximal.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : Subalgebra ℤ K) (q : Ideal O),
    q.IsPrime → q ≠ ⊥ → q.IsMaximal
example : ∃ q : Ideal (⊥ : Subalgebra ℤ ℚ), q.IsPrime ∧ q ≠ ⊥ := by
  let e := Algebra.botEquivOfInjective (R := ℤ) (A := ℚ) Int.cast_injective
  have : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  refine ⟨Ideal.comap (e : (⊥ : Subalgebra ℤ ℚ) →+* ℤ) (Ideal.span {2}), Ideal.comap_isPrime _ _, ?_⟩
  intro h
  have hm : (2 : (⊥ : Subalgebra ℤ ℚ)) ∈
      Ideal.comap (e : (⊥ : Subalgebra ℤ ℚ) →+* ℤ) (Ideal.span {2}) := by
    rw [Ideal.mem_comap, map_ofNat]
    exact Ideal.mem_span_singleton_self 2
  rw [h, Ideal.mem_bot] at hm
  have := congrArg Subtype.val hm
  norm_num at this
end GroundTheory.Heights₂.Heights


