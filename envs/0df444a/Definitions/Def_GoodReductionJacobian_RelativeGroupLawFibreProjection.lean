-- Prove2me | Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibreProjection
-- name    : GoodReductionJacobian_RelativeGroupLawFibreProjection
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:25.380115+00:00
-- url     : https://prove2.me/theorems/62531123-adaa-4c2e-bc07-31edc44ac85e
-- title:
--   Base compatibility of a division-fibre projection
-- statement:
--   Records the compatibility of the first projection from the fibre of multiplication by $n$ on a relative group law with the structural map to the base: the two natural composites from the pullback agree. This is a small technical carrier ensuring that division fibres and their projections are morphisms over the base in the good-reduction construction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
/-! The first projection of a division fibre lies over the base. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

theorem fibre_projection_over
    {R : Type} [CommRing R] {B : Scheme.{0}} {f : B ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ)
    (S : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    pullback.fst (L.schemeNsmul n) S.1 ≫ f = pullback.snd (L.schemeNsmul n) S.1 := by
  calc
    _ = pullback.fst (L.schemeNsmul n) S.1 ≫ L.schemeNsmul n ≫ f := by
      rw [L.schemeNsmul_over]
    _ = pullback.snd (L.schemeNsmul n) S.1 ≫ S.1 ≫ f := by
      rw [pullback.condition_assoc]
    _ = _ := by rw [S.2]; simp

end GoodReductionJacobian.RelativeGroupLaw


