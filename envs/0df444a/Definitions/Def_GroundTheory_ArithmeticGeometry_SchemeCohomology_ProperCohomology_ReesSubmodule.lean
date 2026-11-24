-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:32.134082+00:00
-- url     : https://prove2.me/theorems/f5cf2224-6063-4b4a-bfd5-3700ce392d01
-- title:
--   Rees Submodule
-- statement:
--   Definitions and structural lemmas for Rees Submodule, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ReesSubmodule.lean

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
namespace GroundTheory.Arith.SchemeCoh
open Polynomial
universe u v w
variable {A : Type u} [CommRing A] (I : Ideal A)
section
variable (M : Type v) [AddCommGroup M] [Module A M]
def reesSubmodule : Submodule (reesAlgebra I) (PolynomialModule A M) where
  carrier := {p | ∀ n, p.coeff n ∈ I ^ n • (⊤ : Submodule A M)}
  zero_mem' := fun n => by simp
  add_mem' := fun {p q} hp hq n => by
    simp only [Set.mem_ofPred_eq, PolynomialModule.coeff_add, Finsupp.add_apply] at hp hq ⊢
    exact add_mem (hp n) (hq n)
  smul_mem' := fun r p hp n => by
    simp only [Set.mem_ofPred_eq] at hp ⊢
    change ((r : A[X]) • p).coeff n ∈ _
    rw [PolynomialModule.smul_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hx : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hr : (r : A[X]).coeff x.1 ∈ I ^ x.1 := (mem_reesAlgebra_iff I _).1 r.2 x.1
    have h := Submodule.smul_mem_smul hr (hp x.2)
    rw [smul_smul, ← pow_add, hx] at h
    · exact h
variable {I M}
variable (I M)
end
section Map
variable {M : Type v} [AddCommGroup M] [Module A M] {N : Type w} [AddCommGroup N] [Module A N]
end Map
end GroundTheory.Arith.SchemeCoh


