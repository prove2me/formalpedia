-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:20.63048+00:00
-- url     : https://prove2.me/theorems/f2555878-eaff-40f5-b551-65cbb77d4129
-- title:
--   Deg OUnif
-- statement:
--   Definitions and structural lemmas for Deg OUnif, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/DegOUnif.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
def TorusEndOf {S : Scheme.{0}} (X : Type) [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : Prop :=
  ∀ χ : X, res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) = charUnit S X (h χ)
structure UnifPre.OLinear (O : Type) [Ring O] [StarRing O] {D : DegData R I}
    [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O) : Prop where
  ext : ∀ a : O, (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a
  q_lin : ∀ (e : ℕ) (a : O), (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
    (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a)
  i_lin : ∀ (e : ℕ) (a : O), ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶
      splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X,
    TorusEndOf D.toPre.X (fun χ => star a • χ) t ∧
      (U.gt e).i ≫ (Over.pullback (thick R I e)).map (ιG.act a) = t ≫ (U.gt e).i
end ReciprocityTheory.ChartRestriction.G.Out


