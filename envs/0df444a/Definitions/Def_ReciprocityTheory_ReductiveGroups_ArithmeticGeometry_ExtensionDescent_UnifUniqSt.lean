-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:13.698907+00:00
-- url     : https://prove2.me/theorems/baca20b2-8fd6-4eb8-91ad-500bff35e524
-- title:
--   Unif Uniq St
-- statement:
--   Definitions and structural lemmas for Unif Uniq St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/UnifUniqSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
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
def UnifUniqSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
  ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
  ∀ (U : Unif I D A G) (U' : Unif I D' A' G) (wL : LB.Iso U'.LG.L U.LG.L), wL.IsGen →
    LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig U.LG.rig →
  ∃ hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre,
    (∀ n : ℕ,
      (U'.gt n).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
        (U.gt n).pG.left ∧
      (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
          D'.toPre.Oφ ((U'.gt n).pG) x k ≫ hD.e.hom.left ≫
              pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
            𝟙 _ ≫ D.toPre.Oφ ((U.gt n).pG) (hD.xe x) k,
        LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt n).t x)
          (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫
                            pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) (𝟙 _) _
            Oinvε _ hψ ((U.gt n).t (hD.xe x)))) ∧
      ∀ (jM : PUnit → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jL : U.LG.L.ι),
        res (X := (thickObj R I n G).left) (inf_le_left.trans (inf_le_left.trans inf_le_left) :
            (U'.gt n).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
                pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) D'.toPre.P.L).U (jM, jM') ⊓
              (LB.div (D'.toPre.P.L.pull (U'.gt n).pG.left) (U'.LG.L.pull (fstG I n G).left)).U
                (fun _ => jM', fun _ => jL') ⊓
              (LB.div (D.toPre.P.L.pull (U.gt n).pG.left) (U.LG.L.pull (fstG I n G).left)).U
                (jM, fun _ => jL) ⊓
              (fstG I n G).left ⁻¹ᵁ (LB.div U.LG.L U'.LG.L).U (jL, jL') ≤
            (U'.gt n).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
                pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))) D'.toPre.P.L).U (jM, jM'))
          (pullU (U'.gt n).pG.left _ (hD.w.s (jM, jM'))) *
        res (X := (thickObj R I n G).left) (inf_le_left.trans (inf_le_left.trans inf_le_right))
          ((U'.w n).s (fun _ => jM', fun _ => jL')) =
        res (X := (thickObj R I n G).left) (inf_le_left.trans inf_le_right)
          ((U.w n).s (jM, fun _ => jL)) *
        res (X := (thickObj R I n G).left) inf_le_right
          (pullU (fstG I n G).left _ (wL.s (jL, jL')))) ∧
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X]
      (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O)
      (ιG : RingAct G O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG →
      (∀ (a : O) (y : D'.toPre.X), hD.xe (a • y) = a • hD.xe y) ∧
      ∀ a, ιD'.onB.act a ≫ hD.e.hom =
        hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιD.onB.act a)
structure Laws6 : Prop where
  unifUniq : UnifUniqSt
end ReciprocityTheory.ChartRestriction.G.Out


