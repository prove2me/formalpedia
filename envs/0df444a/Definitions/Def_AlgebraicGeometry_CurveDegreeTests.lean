-- Prove2me | Definitions.Def_AlgebraicGeometry_CurveDegreeTests
-- name    : AlgebraicGeometry_CurveDegreeTests
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-13T15:43:12.551251+00:00
-- url     : https://prove2.me/theorems/f47916ab-fc1a-44df-8381-a2bbf2379ef2
-- title:
--   Smooth-curve degree tests and actual line-bundle fibres
-- statement:
--   For a scheme $X$ over a field $K$, a curve test records a smooth proper integral curve $C$, a morphism $f:C\to X$ over $K$, and two affine charts covering $C$. Its value on a sheaf $L$ is
--
--   $$d_{C,f}(L)=\chi(C,f^*L)-\chi(C,\mathcal O_C),$$
--
--   computed using the existing Cech section modules. Numerical triviality means that every such test vanishes. The module also defines the actual fibre of a line-bundle family at a rational parameter point by pullback. These are data and definitions only; no boundedness, finite rank, or finite generation is assumed.
-- source:
--   Cheng, Ji, Larson and Olander, Theorem of the Base, Definition 2.6(i), p. 6, and Definition 4.1, p. 13; https://mattlarson2399.github.io/Papers/theorem-of-the-base.pdf. The curve-morphism presentation is the normalization-compatible version of the usual integral-curve degree test.

import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option autoImplicit false
noncomputable section

namespace AlgebraicGeometry.CurveDegreeTests
open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K))

/-- A smooth proper integral curve over the base field, mapping to the
given scheme, with two affine charts for its actual Čech Euler characteristic. -/
structure Probe where
  curve : Scheme.{u}
  toBase : curve ⟶ Spec (.of K)
  integral : IsIntegral curve
  proper : IsProper toBase
  smooth : SmoothOfRelativeDimension 1 toBase
  toScheme : curve ⟶ X
  over_base : toScheme ≫ π = toBase
  cover : curve.TwoAffineOpenCover

attribute [instance] Probe.integral Probe.proper Probe.smooth

variable {π}

/-- Euler characteristic on the chosen two affine charts. -/
def Probe.euler (t : Probe π) (M : t.curve.Modules) : ℤ :=
  (Module.finrank K (t.cover.sectionsOf t.toBase M).H0 : ℤ) -
    Module.finrank K (t.cover.sectionsOf t.toBase M).H1

/-- The actual degree of the pulled-back sheaf, without any finiteness premise. -/
def Probe.degree (t : Probe π) (M : X.Modules) : ℤ :=
  t.euler ((Scheme.Modules.pullback t.toScheme).obj M) -
    t.euler (𝟙_ t.curve.Modules)

/-- Vanishing of all smooth-curve degree tests. -/
def NumericallyTrivial (π : X ⟶ Spec (.of K)) (M : X.Modules) : Prop :=
  ∀ t : Probe π, t.degree M = 0

/-- The actual rational fibre of a parameter-family sheaf, viewed on `X`. -/
def fibre {T : Scheme.{u}} (h : T ⟶ Spec (.of K))
    (M : (pullback π h).Modules)
    (t : SchemeHomOver (𝟙 (Spec (.of K))) h) : X.Modules :=
  (Scheme.Modules.pullback
    (pullback.lift (𝟙 X) (π ≫ t.1) (by simp [t.2]))).obj M

end AlgebraicGeometry.CurveDegreeTests


