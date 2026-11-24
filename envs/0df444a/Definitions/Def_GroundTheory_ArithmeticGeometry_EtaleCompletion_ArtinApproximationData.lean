-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ArtinApproximationData
-- name    : GroundTheory_ArithmeticGeometry_EtaleCompletion_ArtinApproximationData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:40:28.506948+00:00
-- url     : https://prove2.me/theorems/d496b7a7-cb53-44ff-9add-f64be983127b
-- title:
--   Artin Approximation Data
-- statement:
--   Definitions and structural lemmas for Artin Approximation Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/ArtinApproximationData.lean

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
namespace GroundTheory.Arith.Etale
open IsLocalRing
noncomputable def jacobianMinor {R : Type*} [CommRing R] {m n : ℕ}
    (g : Fin m → MvPolynomial (Fin n) R) (ι : Fin m → Fin n) : MvPolynomial (Fin n) R :=
  (Matrix.of fun i j ↦ MvPolynomial.pderiv (ι j) (g i)).det
structure IsAdicCompletionMap {A : Type*} [CommRing A] [IsLocalRing A] {C : Type*} [CommRing C]
    (φ : A →+* C) : Prop where
  isAdicComplete : IsAdicComplete ((maximalIdeal A).map φ) C
  bijective : ∀ n : ℕ, Function.Bijective
    (Ideal.quotientMap ((maximalIdeal A ^ n).map φ) φ Ideal.le_comap_map)
end GroundTheory.Arith.Etale


