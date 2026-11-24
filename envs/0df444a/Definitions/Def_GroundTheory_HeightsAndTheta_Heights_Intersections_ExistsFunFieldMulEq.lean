-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:49.768732+00:00
-- url     : https://prove2.me/theorems/06f93fe1-1cd8-47e1-b2ca-e5425658e2b2
-- title:
--   Exists Fun Field Mul Eq
-- statement:
--   Definitions and structural lemmas for Exists Fun Field Mul Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExistsFunFieldMulEq.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SameOrbitOneSpecZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def funField {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u v : MRing ι) (a : K → ℕ)
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)),
    IsMultiHomog u a ∧ IsMultiHomog v a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩}
def regularityEmbedding_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar P 1 → (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    ∃ e : R ≃ (funField P →+* ℂ), ∀ (t : R) (u v : MRing ι) (a : K → ℕ),
      IsMultiHomog u a → IsMultiHomog v a → v ∉ P → ∀ x : funField P,
      (x : FractionRing (MRing ι ⧸ P)) *
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
      e t x * eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) v) =
        eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) u)
end
end GroundTheory.Heights₂.Heights.Inter


