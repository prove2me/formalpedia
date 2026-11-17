-- Prove2me | Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame
-- name    : AlgebraicGeometry_SymmetricFiniteFrame
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:18.249229+00:00
-- url     : https://prove2.me/theorems/a1c7b19e-674a-44a6-a30e-7e7280d10571
-- title:
--   Symmetric finite projective frames on an abelian scheme
-- statement:
--   The file defines $K$-points over a structure morphism, the subtraction morphism on a relative commutative group, and a symmetric finite frame. Such a frame contains an invertible symmetric line bundle $L$, a finite projective presentation, and chosen isomorphism classes $$[2]^*L≃L^{⊗4},   m^*L⊗d^*L≃pr_1^*(L^{⊗2})⊗pr_2^*(L^{⊗2}).$$ This package is the geometric input for bounded doubling, the parallelogram law, and Northcott finiteness.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
set_option autoImplicit false
noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
abbrev AlgebraicGeometry.Scheme.KPoint {K : Type} [CommRing K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) := SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f
def AlgebraicGeometry.Polarisation.subMor {K : Type} [CommRing K] {A : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of K)) (G : RelativeGroupLaw K f) : pullback f f ⟶ A :=
  pullback.lift (pullback.fst f f) (pullback.snd f f ≫ Polarisation.negMor f G)
      (by rw [Category.assoc, Polarisation.negMor_over]; exact pullback.condition) ≫ Polarisation.addMor f G

structure AlgebraicGeometry.SymmetricFiniteFrame (K : Type) [Field K] [NumberField K]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K)) (G : RelativeGroupLaw K f) where
  line : A.Modules
  line_isInvertible : Scheme.Modules.IsInvertible line
  N : ℕ
  presentation : line.ProjPresentation f N
  presentation_finite : IsFinite presentation.toProj
  symmetric : Polarisation.IsSymmetric f G line
  doubleIso : Nonempty ((Scheme.Modules.pullback (G.schemeNsmul 2)).obj line ≅ line.tensorPow 4)
  parallelogramIso : Nonempty
    (((Scheme.Modules.pullback (Polarisation.addMor f G)).obj line ⊗
        (Scheme.Modules.pullback (Polarisation.subMor f G)).obj line) ≅
      ((Scheme.Modules.pullback (pullback.fst f f)).obj (line.tensorPow 2) ⊗
        (Scheme.Modules.pullback (pullback.snd f f)).obj (line.tensorPow 2)))


