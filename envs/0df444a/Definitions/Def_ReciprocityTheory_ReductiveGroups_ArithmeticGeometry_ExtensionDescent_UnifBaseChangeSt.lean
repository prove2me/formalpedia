-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:07:50.984588+00:00
-- url     : https://prove2.me/theorems/a78d3fd2-8c7b-4e32-9bd1-86963b6aaae6
-- title:
--   Unif Base Change St
-- statement:
--   Definitions and structural lemmas for Unif Base Change St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/UnifBaseChangeSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
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
abbrev specOf (φ : R →+* R') : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)
structure IsPullDeg (φ : R →+* R') (D : DegPre R) (D' : DegPre R') where
  e : D'.P.A ≅ (Over.pullback (specOf φ)).obj D.P.A
  e_hom : IsMonHom e.hom
  w : LB.Iso D'.P.L (D.P.L.pull (e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  w_gen : w.IsGen
  he : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A
  w_rig : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
    (rigPullOf (e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (specOf φ) he D.P.L D.rig)
  xe : D'.X ≃+ D.X
  c_pr : ∀ x : D'.X, (D'.c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
    specOf φ ≫ (D.c (xe x)).left
  W : (Spec (CommRingCat.of R)).Opens
  psiW : PsiOn D W
  g : (TK R').left ⟶ (TW W).left
  g_comm : g ≫ W.ι = jK R' ≫ specOf φ
  psi_pr : ∀ x : D'.X, ∃ b : LB.Gen (LB.LinComb D.P.L (K := PUnit)
      (fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (fun _ => -1)),
    GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit)
      (fun _ => e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) w (D'.xK x) (-1) (D'.psi x) b ∧
    LB.Gen.Corr D.P.L _ _ _ _ b (LB.pullGen D.P.L _ _ (psiW.psi (xe x)) g)
structure IsPullUnif {I : Ideal R} {I' : Ideal R'} (φ : R →+* R') {D : DegData R I}
    {D' : DegData R' I'} (hD : IsPullDeg φ D.toPre D'.toPre)
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G)
    (U : Unif I D A G) (U' : Unif I' D' A' G') : Prop where
  lg : ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))),
    wL.IsGen ∧
    ∃ he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G,
      LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U'.LG.rig
        (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) ∧
    ∀ e : ℕ, ∃ h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left,
      h ≫ (fstG I e G).left =
        (fstG I' e G').left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      (U'.gt e).pG.left ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) =
        h ≫ (U.gt e).pG.left ∧
      (∀ x : D'.toPre.X, ∃ hψ : ∀ k : Fin 4,
          D'.toPre.Oφ ((U'.gt e).pG) x k ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) =
            h ≫ D.toPre.Oφ ((U.gt e).pG) (hD.xe x) k,
        LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) ((U'.gt e).t x)
          (GeneratorPullback.pullAlong D.toPre.P.L (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) h _
            Oinvε _ hψ ((U.gt e).t (hD.xe x)))) ∧
      ∀ (jM : PUnit → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι)
        (jL : PUnit → U.LG.L.ι),
        res (X := (thickObj R' I' e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) :
            (U'.gt e).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
                pullback.fst D.toPre.P.A.hom (specOf φ))) D'.toPre.P.L).U (jM, jM') ⊓
              (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I' e G').left)).U
                (fun _ => jM', fun _ => jL') ⊓
              h ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U
                (jM, jL) ⊓
              (fstG I' e G').left ⁻¹ᵁ (LB.div (U.LG.L.pull (bc.hom.left ≫
                pullback.fst G.hom (specOf φ))) U'.LG.L).U (jL, jL') ≤
            (U'.gt e).pG.left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (hD.e.hom.left ≫
                pullback.fst D.toPre.P.A.hom (specOf φ))) D'.toPre.P.L).U (jM, jM'))
          (pullU (U'.gt e).pG.left _ (hD.w.s (jM, jM'))) *
        res (X := (thickObj R' I' e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right))
          ((U'.w e).s (fun _ => jM', fun _ => jL')) =
        res (X := (thickObj R' I' e G').left) (inf_le_left.trans inf_le_right)
          (pullU h _ ((U.w e).s (jM, jL))) *
        res (X := (thickObj R' I' e G').left) inf_le_right
          (pullU (fstG I' e G').left _ (wL.s (jL, jL')))
def UnifBaseChangeSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ φ : R →+* R', I.map φ ≤ I' →
    ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
      (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif I D A G) (W : (Spec (CommRingCat.of R)).Opens), Nonempty (PsiOn D.toPre W) →
      (specOf φ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W →
    ∀ (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G']
      (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom →
    ∀ A' : PolAV (Spec (CommRingCat.of (FractionRing R'))), A'.g = A.g →
    ∀ eA : (Over.pullback (jK R')).obj G' ≅ A'.A, IsMonHom eA.hom →
      (∃ wA : LB.Iso (A'.L.pull eA.hom.left)
          (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))),
          wA.IsGen) →
    ∀ (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))))
      (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G),
      wL.IsGen →
      LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
        (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) →
    ∃ (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : Unif I' D' A' G'),
      U'.LG = L' ∧ U'.gen = eA ∧ IsPullUnif φ hD bc U U'
def WeightIndepSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α, D.toPre.SecB k α), (∀ j, ((fstG I e G).left.app _).hom (σ.f j) = 0) →
    U.ExpandsAt e k σ f → ∀ α j, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0
def TLinSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (O : Type) [Ring O] [StarRing O]
    (D : DegData R I) [Module O D.toPre.X] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG →
    ∀ (e : ℕ) (a : O)
      (u : LB.Gen (LB.LinComb D.toPre.P.L
        (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε)),
      u.IsGen →
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (zero2 D.toPre.P.A))
        (LB.oneGen D.toPre.P.L) →
      ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _
        (LB.mulGen D.toPre.P.L _ _ _ _ ((U.gt e).t (star a • χ))
          (LB.pullGen D.toPre.P.L _ _ u (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left))
        (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ)
          ((Over.pullback (thick R I e)).map (ιG.act a)).left)
structure Laws4 : Prop where
  unifBaseChange : UnifBaseChangeSt
  weightIndep : WeightIndepSt
  tLin : TLinSt
end ReciprocityTheory.ChartRestriction.G.Out


