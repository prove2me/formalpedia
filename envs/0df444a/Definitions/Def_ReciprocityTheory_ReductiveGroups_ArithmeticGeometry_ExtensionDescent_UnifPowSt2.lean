-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowSt2
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowSt2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:52.90498+00:00
-- url     : https://prove2.me/theorems/d740a44e-e0c8-4f7f-a11a-ebb3225d9329
-- title:
--   Unif Pow St2
-- statement:
--   Definitions and structural lemmas for Unif Pow St2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/UnifPowSt2.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
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
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
structure UnifPowOf2 {j : ℕ} {D D' : DegData R I}
    {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j)
    (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G)
    extends UnifPowOf pD pA pG U' U where

  t_pr : ∀ (e : ℕ) (x : D'.toPre.X),
    ∃ hψ : ∀ (i : Fin j) (k : Fin 4),
        D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫
          (pD.pw.pr i).left =
        ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫
          D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k,
      LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x)
        (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i =>
          GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left
            ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i)
            ((U.gt e).t (pD.xe x i))))
def UnifPowSt2 : Prop :=
  ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (j : ℕ)
    (D' : DegData R I) (A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j),
    ∃ U' : Unif I D' A' G', Nonempty (UnifPowOf2 pD pA pG U' U)
end ReciprocityTheory.ChartRestriction.G.Out


