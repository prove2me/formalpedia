-- Prove2me | solution 1 for AutomorphicForm.AdelicTracePushforward.trace_traceFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9c56807a-bfa1-5198-933a-c21ae07bdbb0

import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_AdelicTracePushforward_trace_traceFibre

set_option autoImplicit false

open NumberField

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (r : AdeleRing (𝓞 K) K) (w : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) :
    letI := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toAlgebra
    Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L)
      (AutomorphicForm.AdelicTracePushforward.traceFibre K L r w) = r := by
  letI alg : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toAlgebra
  have hβ : ∀ a : AdeleRing (𝓞 K) K,
      M4aHerbrand.Bridge.genuineβ K L a = algebraMap (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) a := fun a => rfl
  have htr : ∀ ℓ : L, Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) (algebraMap L (AdeleRing (𝓞 L) L) ℓ) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.trace K L ℓ) := by
    intro ℓ
    rw [← (M4aHerbrand.GenuineDescent.genuineBaseChange K L).tensorEquiv_one_tmul ℓ, Algebra.trace_eq_of_algEquiv,
      Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]
  have hn : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have h1 : Algebra.trace K L ((Module.finrank K L : L)⁻¹) = 1 := by
    rw [show ((Module.finrank K L : L)⁻¹) = algebraMap K L ((Module.finrank K L : K)⁻¹) by simp,
      Algebra.trace_algebraMap, nsmul_eq_mul, mul_inv_cancel₀ hn]
  have h2 : ∀ i, Algebra.trace K L
      (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L) = 0 :=
    fun i => LinearMap.mem_ker.mp (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i).2
  show Algebra.trace (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L)
    (M4aHerbrand.Bridge.genuineβ K L r * algebraMap L (AdeleRing (𝓞 L) L) (Module.finrank K L : L)⁻¹ +
      ∑ i, M4aHerbrand.Bridge.genuineβ K L (w i) *
        algebraMap L (AdeleRing (𝓞 L) L) (Module.finBasis K (LinearMap.ker (Algebra.trace K L)) i : L)) = r
  simp_rw [hβ, ← Algebra.smul_def, map_add, map_sum, map_smul, htr, h1, h2, map_one, map_zero, smul_zero,
    Finset.sum_const_zero, add_zero, smul_eq_mul, mul_one]

end S_AutomorphicForm_AdelicTracePushforward_trace_traceFibre
end P2MW
export P2MW.S_AutomorphicForm_AdelicTracePushforward_trace_traceFibre (solution)
