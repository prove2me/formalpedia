-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:52.129785+00:00
-- url     : https://prove2.me/theorems/4da74aa9-543d-49b0-91b4-c5cb259bf818
-- title:
--   Pull Exp
-- statement:
--   Definitions and structural lemmas for Pull Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PullExp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
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
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
abbrev gK : pullback G.hom (jK V) ⟶ G.left := pullback.fst G.hom (jK V)
def endK (f : G ⟶ G) : pullback G.hom (jK V) ⟶ pullback G.hom (jK V) :=
  pullback.map G.hom (jK V) G.hom (jK V) f.left (𝟙 _) (𝟙 _) (by simp) (by simp)
def unitK : Spec (CommRingCat.of (FractionRing V)) ⟶ pullback G.hom (jK V) :=
  pullback.lift (jK V ≫ eSec G) (𝟙 _) (by simp [eSec])
def IsPullByEnd (U : Unif (maximalIdeal V) D A G) (f : G ⟶ G) (k N : ℕ) (s : U.SecK k) (s' : U.SecK (k * N)) : Prop :=
  ∃ u : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)]), u.IsGen ∧
    LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u unitK)
      (LB.pullGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig (k * (N - 1))) (jK V)) ∧
    GeneratorPullback.SecRel U.LG.L (fun _ : Fin 1 => gK) (fun _ => ((k * N : ℕ) : ℤ)) s'
      (fun _ : Fin 1 => gK) (fun _ => (k : ℤ)) s (endK f)
      ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)] u
end ReciprocityTheory.ChartRestriction.G.DVR


