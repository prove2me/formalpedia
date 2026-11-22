-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:14:07.008803+00:00
-- url     : https://prove2.me/theorems/209efe95-9bd9-4c0f-9b4d-7c89333e3b8d
-- title:
--   OLin Base Change St
-- statement:
--   Definitions and structural lemmas for OLin Base Change St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/OLinBaseChangeSt.lean

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
def IsPullGtF (φ : R →+* R') {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D')
    (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (g : GtPtF D F) (g' : GtPtF D' F) : Prop :=
  g'.b.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = g.b.left ∧
  ∀ χ : D'.X, ∃ hψ : ∀ k : Fin 4,
      DegPre.gtφ D' F g'.b χ k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        𝟙 _ ≫ DegPre.gtφ D F g.b (hD.xe χ) k,
    LB.Gen.Maps (LB.linCombIso hD.w _ DegPre.gtε) (g'.s χ)
      (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (𝟙 _) _
        DegPre.gtε _ hψ (g.s (hD.xe χ)))
def OLinBaseChangeSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom →
    ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I')
    (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O)
      (ιG : RingAct G O), U.OLinear O ιD ιA ιG →
    ∀ (ιG' : RingAct G' O),
      (∀ a, (ιG'.act a) ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf φ)).map (ιG.act a)) →
    ∀ (ιA' : A'.OAct O),
      (∀ a, (Over.pullback (jK R')).map (ιG'.act a) ≫ U'.gen.hom = U'.gen.hom ≫ ιA'.act a) →
    ∃ (_ : Module O D'.toPre.X) (ιD' : D'.toPre.OAct O),
      (∀ (a : O) (y : D'.toPre.X), hD.xe (a • y) = a • hD.xe y) ∧
      (∀ a, ιD'.onB.act a ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map (ιD.onB.act a)) ∧
      U'.OLinear O ιD' ιA' ιG' ∧
      ∀ w0 : O, ReciprocityTheory.ChartRestriction.G.Geo.Tor.TraceFormTwistIso D.toPre ιD w0 →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.TraceFormTwistIso D'.toPre ιD' w0
def QkBaseChangeSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ (φ : R →+* R') (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom →
    ∀ (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (D' : DegData R' I')
    (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'), IsPullUnif φ hD bc U U' →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F],
      (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) →
    ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A)
      (p' : QkPt D'.toPre F k) (x' : TFK (R := R') F ⟶ A'.A),
      p'.y = hD.xe.symm p.y → IsPullGtF φ hD F p.g p'.g →
      x'.left ≫ U'.gen.inv.left ≫ pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫
          pullback.fst G.hom (specOf φ) =
        x.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) →
      QkToAkU U.toUnifPre F k p x → QkToAkU U'.toUnifPre F k p' x'
def PsiOnExistsSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ D : DegData R I,
    ∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧
      Nonempty (PsiOn D.toPre W)
structure Laws5 : Prop where
  oLinBaseChange : OLinBaseChangeSt
  qkBaseChange : QkBaseChangeSt
  psiOnExists : PsiOnExistsSt
end ReciprocityTheory.ChartRestriction.G.Out


