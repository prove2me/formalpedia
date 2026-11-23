-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProductFirstParts
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProductFirstParts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:25.968845+00:00
-- url     : https://prove2.me/theorems/58eb0451-84a8-49e4-b27a-1da3d724144c
-- title:
--   Product First Parts
-- statement:
--   Definitions and structural lemmas for Product First Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ProductFirstParts.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.product_first_partition.blockEmb.{u_1, u_2} :
    (K : Type u_1) →
      [inst : CommRing K] →
        {S : Type u_2} → {k n : ℕ} → S → MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (S × Fin k × Fin n) K :=
    fun (K : Type u_1) [CommRing K] {S : Type u_2} {k n : ℕ} (s : S) ↦ MvPolynomial.rename fun (v : Fin k × Fin n) ↦ (s, v)
noncomputable def UpperTheory.Reformulated.B.product_first_partition.tensorLat.{u_1, u_2, u_3} :
    (R : Type u_1) →
      (K : Type u_2) →
        [inst : CommRing R] →
          [inst_1 : CommRing K] →
            [inst_2 : Algebra R K] →
              {S : Type u_3} →
                [Fintype S] →
                  {k n : ℕ} →
                    (S → Submodule R (MvPolynomial (Fin k × Fin n) K)) → Submodule R (MvPolynomial (S × Fin k × Fin n) K) :=
    fun (R : Type u_1) (K : Type u_2) [CommRing R] [CommRing K] [Algebra R K] {S : Type u_3} [Fintype S] {k n : ℕ}
        (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) ↦
      Submodule.span R
        {P : MvPolynomial (S × Fin k × Fin n) K |
          ∃ (F : S → MvPolynomial (Fin k × Fin n) K),
            (∀ (s : S), F s ∈ M s) ∧
              P =
                ∏ s : S,
                  (UpperTheory.Reformulated.B.product_first_partition.blockEmb K s : MvPolynomial (Fin k × Fin n) K → MvPolynomial (S × Fin k × Fin n) K)
                    (F s)}


