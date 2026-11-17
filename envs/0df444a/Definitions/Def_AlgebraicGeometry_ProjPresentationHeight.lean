-- Prove2me | Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
-- name    : AlgebraicGeometry_ProjPresentationHeight
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:52.347502+00:00
-- url     : https://prove2.me/theorems/98953b53-6561-4f0e-a4b0-d67d9dd8fd6d
-- title:
--   Projective coordinates and heights from a line-bundle presentation
-- statement:
--   For a projective presentation $P$ of a line bundle on a $K$-scheme, the file sends each $K$-point $x$ to its projective coordinate class and defines $$h_P(x)=h([s_0(x):⋯:s_N(x)]).$$ It then defines the height of a symmetric finite frame to be the height attached to its chosen presentation. These are the height functions used for Northcott finiteness and the quadratic-height argument.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
set_option autoImplicit false
noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace Scheme.Modules.ProjPresentation
noncomputable def pointProjectivization
    {K : Type} [Field K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) (x : Scheme.KPoint f) :
    Projectivization K (Fin (N + 1) → K) :=
  ProjSpace.kPointEquivProjectivization K N
    ⟨x.1 ≫ P.toProj, by
      rw [Category.assoc, P.toProj_π]
      exact x.2⟩

noncomputable def pointLogHeight
    {K : Type} [Field K] [NumberField K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) : Scheme.KPoint f → ℝ :=
  fun x => Projectivization.logHeight (P.pointProjectivization x)


end Scheme.Modules.ProjPresentation
namespace SymmetricFiniteFrame
noncomputable def height
    {K : Type} [Field K] [NumberField K]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)}
    {G : RelativeGroupLaw K f} (F : SymmetricFiniteFrame K f G) :
    Scheme.KPoint f → ℝ :=
  F.presentation.pointLogHeight


end SymmetricFiniteFrame
end AlgebraicGeometry


