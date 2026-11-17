-- Prove2me | Definitions.Def_N25_CanonicalProjectiveGenericPoint
-- name    : N25_CanonicalProjectiveGenericPoint
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:15.977183+00:00
-- url     : https://prove2.me/theorems/475a4d61-58b9-4ef7-b99d-59a0740ab4ee
-- title:
--   A generic point of the canonical projective curve
-- statement:
--   For a domain-valued canonical cone with nonzero positive-degree form $A$, defines the zero homogeneous prime as a point of the projective spectrum. This supplies an explicit generic point and a nonemptiness witness for the projective function-field construction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_CanonicalProjectiveCone
import Mathlib.AlgebraicGeometry.Properties
/-! The generic point of the literal canonical Proj: the zero homogeneous prime of the cone. -/

noncomputable section

universe u

namespace N25

open AlgebraicGeometry HomogeneousLocalization

variable (K : Type u) [Field K]

/-- The zero homogeneous prime is a generic point because A is a nonzero positive-degree element. -/
def canonicalProjectiveGenericPoint25 [IsDomain (CanonicalConeRing25 K)]
    (ha : canonicalConeA25 K ≠ 0) : ProjectiveSpectrum (canonicalConePiece25 K) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (CanonicalConeRing25 K)).IsPrime
    infer_instance
  not_irrelevant_le := by
    intro h
    have hm := HomogeneousIdeal.mem_irrelevant_of_mem (canonicalConePiece25 K)
      (by decide : 0 < (1 : ℕ)) (canonicalConeA25_mem K)
    have hz := h hm
    exact ha (Ideal.mem_bot.mp (show canonicalConeA25 K ∈ (⊥ : Ideal (CanonicalConeRing25 K)) from hz))

end N25


