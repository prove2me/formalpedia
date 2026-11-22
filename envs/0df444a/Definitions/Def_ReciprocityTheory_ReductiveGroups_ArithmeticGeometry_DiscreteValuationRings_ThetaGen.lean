-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:11:22.095787+00:00
-- url     : https://prove2.me/theorems/512f4da5-7a6e-4beb-96b5-797cc1e75850
-- title:
--   Theta Gen
-- statement:
--   Definitions and structural lemmas for Theta Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGen.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
def SecIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {L : LB Y} (a : R)
    (σ τ : LB.Sec L) : Prop :=
  ∀ j, σ.f j = resTop _ (scal p a) * τ.f j
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
def SecBGenerates (k : ℕ) (α : D.toPre.X) (s : D.toPre.SecB k α) : Prop :=
  ∀ s' : D.toPre.SecB k α, ∃! a : R, SecIsMul D.toPre.P.A.hom a s' s
def IsTheta (U : Unif I D A G) (ϑ : H0 U.LG.L 1) : Prop :=
  ∀ e : ℕ, ∃ f : ∀ α : D.toPre.X, D.toPre.SecB 1 α, U.ExpandsAt e 1 ϑ f ∧ SecBGenerates 1 0 (f 0)
def NonzeroOnSpecial (U : Unif I D A G) (σ : H0 U.LG.L 1) : Prop :=
  ∃ j, ((fstG (maximalIdeal R) 0 G).left.app _).hom (σ.f j) ≠ 0
end ReciprocityTheory.ChartRestriction.G.DVR
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
end ReciprocityTheory.ChartRestriction.G.DVR


