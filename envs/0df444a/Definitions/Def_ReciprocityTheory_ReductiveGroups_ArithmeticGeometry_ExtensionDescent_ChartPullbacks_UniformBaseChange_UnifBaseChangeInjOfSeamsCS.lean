-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:05.590776+00:00
-- url     : https://prove2.me/theorems/18ff86a7-186d-4fe2-962f-4f46af477acb
-- title:
--   Unif Base Change Inj Of Seams CS
-- statement:
--   Definitions and structural lemmas for Unif Base Change Inj Of Seams CS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/UnifBaseChangeInjOfSeamsCS.lean

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
section Rel
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
def IsPullUnifPre {I : Ideal R} {I' : Ideal R'} (φ : R →+* R') {D : DegData R I}
    {D' : DegData R' I'} (hD : IsPullDeg φ D.toPre D'.toPre)
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G)
    (U : UnifPre I D A G) (U' : UnifPre I' D' A' G') : Prop :=
  ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ))),
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
end Rel
def UnifBaseChangeInjSt : Prop :=

  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ φ : R →+* R', I.map φ ≤ I' → Function.Injective φ →
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
def PullDegInjSt : Prop :=

  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ φ : R →+* R', I.map φ ≤ I' → Function.Injective φ →
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
    ∃ D' : DegData R' I', Nonempty (IsPullDeg φ D.toPre D'.toPre)
def PullPreInjSt : Prop :=

  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ φ : R →+* R', I.map φ ≤ I' → Function.Injective φ →
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
    ∀ (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre),
      ∃ U' : UnifPre I' D' A' G', U'.LG = L' ∧ U'.gen = eA ∧ IsPullUnifPre φ hD bc U.toUnifPre U'
def ExpPullInjSt : Prop :=

  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ φ : R →+* R', I.map φ ≤ I' → Function.Injective φ →
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
    ∀ (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (U' : UnifPre I' D' A' G'),
      U'.LG = L' → U'.gen = eA → IsPullUnifPre φ hD bc U.toUnifPre U' →
      ∀ k : ℕ, 1 ≤ k → U'.ExpBij k
section CS
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
def IsPullDegCS {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') : Prop :=
  (∀ (F3 : (G3 D'.P.A).left ⟶ (G3 D.P.A).left)
      (hψ : ∀ k, thφ D'.P.A (x3 D'.P.A) k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        F3 ≫ thφ D.P.A (x3 D.P.A) k),
      LB.Gen.Maps (LB.linCombIso hD.w (thφ D'.P.A (x3 D'.P.A)) thε) D'.cub.t
        (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) F3
          (thφ D.P.A (x3 D.P.A)) thε (thφ D'.P.A (x3 D'.P.A)) hψ D.cub.t)) ∧
  ∀ hψ : ∀ k, (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → (D'.P.A.left ⟶ D'.P.A.left)) k ≫
        hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫
        (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → (D.P.A.left ⟶ D.P.A.left)) k,
    LB.Gen.Maps (LB.linCombIso hD.w
        (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → (D'.P.A.left ⟶ D'.P.A.left)) ![1, -1])
      D'.sym
      (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
        (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
        (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → (D.P.A.left ⟶ D.P.A.left)) ![1, -1]
        (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → (D'.P.A.left ⟶ D'.P.A.left)) hψ D.sym)
end CS
def PullDegCSInjSt : Prop :=

  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ φ : R →+* R', I.map φ ≤ I' → Function.Injective φ →
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
    ∃ (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre), IsPullDegCS hD
def PullPreCSInjSt : Prop :=

  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R'), AdmBase R I → AdmBase R' I' → ∀ φ : R →+* R', I.map φ ≤ I' → Function.Injective φ →
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
    ∀ (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre), IsPullDegCS hD →
      ∃ U' : UnifPre I' D' A' G', U'.LG = L' ∧ U'.gen = eA ∧ IsPullUnifPre φ hD bc U.toUnifPre U'
end ReciprocityTheory.ChartRestriction.G.Out


