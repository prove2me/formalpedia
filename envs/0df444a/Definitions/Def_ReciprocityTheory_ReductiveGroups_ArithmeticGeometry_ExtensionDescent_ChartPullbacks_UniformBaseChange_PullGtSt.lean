-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGtSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGtSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:27:02.537268+00:00
-- url     : https://prove2.me/theorems/93bce300-7c1d-4be0-97e6-35e62a5de97c
-- title:
--   Pull Gt St
-- statement:
--   Definitions and structural lemmas for Pull Gt St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullGtSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
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
structure IsPullGt {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {I : Ideal R} {I' : Ideal R'} (φ : R →+* R') {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg φ D D') {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) {e : ℕ} (g : GtCoord I D e G)
    (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) : Prop where
  h_fst : h ≫ (fstG I e G).left = (fstG I' e G').left ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)
  h_pG : g'.pG.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ g.pG.left
  h_t : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4,
      D'.Oφ g'.pG x k ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) =
        h ≫ D.Oφ g.pG (hD.xe x) k,
    LB.Gen.Maps (LB.linCombIso hD.w _ Oinvε) (g'.t x)
      (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ Oinvε _ hψ
        (g.t (hD.xe x)))
def PullGtSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R)
    (I' : Ideal R') (φ : R →+* R'), I.map φ ≤ I' →
    ∀ (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D')
      (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
      (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G']
      (bc : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom →
    ∀ (e : ℕ) (g : GtCoord I D e G),
      ∃ (g' : GtCoord I' D' e G') (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left),
        IsPullGt φ hD bc g g' h
end ReciprocityTheory.ChartRestriction.G.Out


