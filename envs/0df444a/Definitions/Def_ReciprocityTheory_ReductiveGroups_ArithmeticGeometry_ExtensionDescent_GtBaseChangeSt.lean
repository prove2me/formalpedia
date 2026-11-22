-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:25.636981+00:00
-- url     : https://prove2.me/theorems/423ea248-5437-4ce1-9ecb-49c93e6b9992
-- title:
--   Gt Base Change St
-- statement:
--   Definitions and structural lemmas for Gt Base Change St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/GtBaseChangeSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
def GtBaseChangeSt : Prop :=
  ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G], E.IsGt G →
    ∃ (E' : SplitExt S') (φ : E.X ≃+ E'.X) (e : E'.B ≅ (Over.pullback f).obj E.B),
      IsMonHom e.hom ∧
      (∀ χ : E.X, ∃ w : LB.Iso ((E.O χ).L.pull (e.hom.left ≫ pullback.fst E.B.hom f))
          (E'.O (φ χ)).L, w.IsGen) ∧
      E'.IsGt ((Over.pullback f).obj G)
def CubePullSt : Prop :=
  ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (m : CubeMap G' G) (L : RigLB G) (c : CubicalStr G L),
    ∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen),
      (∃ c' : CubicalStr G' (m.rigLB L hL hr), m.IsPullCubical c' c) ∧
      (L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric)
structure Laws3 : Prop where
  gtBaseChange : GtBaseChangeSt
  cubePull : CubePullSt
end ReciprocityTheory.ChartRestriction.G.Out


