-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_UniformizationBaseChange
-- name    : Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_UniformizationBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:50.400401+00:00
-- url     : https://prove2.me/theorems/ef30afe3-0a0d-4bb4-a91c-2286d74af755
-- title:
--   Uniformization Base Change
-- statement:
--   Definitions and structural lemmas for Uniformization Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/UniformizationBaseChange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_RigidPullbackIdentification
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification
section Carries
variable {X X' Y : Scheme.{0}} (L : LB X) (L' : LB X') (F : X' ⟶ X) {K : Type} [Fintype K]
def CarriesFam (w : LB.Iso L' (L.pull F)) (p' : K → (Y ⟶ X')) (p : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L' p' ε)) (b : LB.Gen (LB.LinComb L p ε)) : Prop :=
  (∀ k, p' k ≫ F = p k) ∧
  ∀ (j : K → L.ι) (j' : K → L'.ι) (V : Y.Opens) (hb : V ≤ LB.wchart L p j)
    (ha : V ≤ LB.wchart L' p' j')
    (hw : ∀ k, V ≤ p' k ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j k, j' k)),
    res hb (b.s j) =
      (∏ k, res (hw k) (pullU (p' k) _ (w.s (fun _ => j k, j' k))) ^ ε k) * res ha (a.s j')
end Carries
section Pull
open scoped CategoryTheory.Obj
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
structure GrpPull (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] where
  F : G'.left ⟶ G.left
  cart : IsPullback F G'.hom G.hom (specOf φ)
  F_one : eSec G' ≫ F = specOf φ ≫ eSec G
  F_mul : (μ[G']).left ≫ F =
    pullback.map G'.hom G'.hom G.hom G.hom F F (specOf φ) cart.w.symm cart.w.symm ≫ (μ[G]).left
structure RigPull {φ : R →+* R'} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] (pG : GrpPull φ G G')
    (L : RigLB G) (L' : RigLB G') where
  w : LB.Iso L'.L (L.L.pull pG.F)
  w_gen : w.IsGen
  w_rig : CarriesAt L.L L'.L pG.F w (eSec G') (specOf φ ≫ eSec G) pG.F_one 1 L'.rig
    (LB.pullGen L.L _ _ L.rig (specOf φ))
variable {I : Ideal R} {I' : Ideal R'}
omit [IsDomain R] [IsDomain R'] in
lemma pow_le_comap {φ : R →+* R'} (hI : I ≤ I'.comap φ) (n : ℕ) :
    I ^ n ≤ (I' ^ n).comap φ :=
  (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow φ n)
abbrev thickSpec {φ : R →+* R'} (hI : I ≤ I'.comap φ) (e : ℕ) :
    Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I' ^ (e + 1)) φ (pow_le_comap hI (e + 1))))
omit [IsDomain R] [IsDomain R'] in
lemma thickSpec_comp {φ : R →+* R'} (hI : I ≤ I'.comap φ) (e : ℕ) :
    thick R' I' e ≫ specOf φ = thickSpec hI e ≫ thick R I e := by
  simp only [thick, thickSpec, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Ideal.quotientMap_comp_mk]
def GrpPull.thickF {φ : R →+* R'} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] (pG : GrpPull φ G G')
    (hI : I ≤ I'.comap φ) (e : ℕ) : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left :=
  pullback.map G'.hom (thick R' I' e) G.hom (thick R I e) pG.F (thickSpec hI e) (specOf φ)
    pG.cart.w.symm (thickSpec_comp hI e)
structure UnifPull {φ : R →+* R'} (hI : I ≤ I'.comap φ) {D : DegData R I} {D' : DegData R' I'}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']
    (pD : PullIdent φ D.toPre D'.toPre) (pG : GrpPull φ G G')
    (U : Unif I D A G) (U' : Unif I' D' A' G') where
  bundle : RigPull pG U.LG U'.LG
  q_eq : ∀ e : ℕ, (U'.gt e).pG.left ≫ pD.F = pG.thickF hI e ≫ (U.gt e).pG.left
  t_eq : ∀ (e : ℕ) (χ : D'.toPre.X),
    CarriesFam D.toPre.P.L D'.toPre.P.L pD.F pD.w
      (D'.toPre.Oφ (U'.gt e).pG χ)
      (fun k => pG.thickF hI e ≫ D.toPre.Oφ (U.gt e).pG (pD.xe χ) k) Oinvε
      ((U'.gt e).t χ)
      (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t (pD.xe χ)) (pG.thickF hI e))
  w_eq : ∀ (e : ℕ) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι)
    (V : (thickObj R' I' e G').left.Opens)
    (h₁ : V ≤ (U'.gt e).pG.left ⁻¹ᵁ
      (LB.div (D.toPre.P.L.pull pD.F) D'.toPre.P.L).U (fun _ => jM, jM'))
    (h₂ : V ≤ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left)
      (U'.LG.L.pull (fstG I' e G').left)).U (fun _ => jM', fun _ => jL'))
    (h₃ : V ≤ pG.thickF hI e ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
      (U.LG.L.pull (fstG I e G).left)).U (fun _ => jM, fun _ => jL))
    (h₄ : V ≤ (fstG I' e G').left ⁻¹ᵁ
      (LB.div (U.LG.L.pull pG.F) U'.LG.L).U (fun _ => jL, jL')),
    res h₁ (pullU (U'.gt e).pG.left _ (pD.w.s (fun _ => jM, jM'))) *
        res h₂ ((U'.w e).s (fun _ => jM', fun _ => jL')) =
      res h₃ (pullU (pG.thickF hI e) _ ((U.w e).s (fun _ => jM, fun _ => jL))) *
        res h₄ (pullU (fstG I' e G').left _ (bundle.w.s (fun _ => jL, jL')))
def GenericInPsiLocus (φ : R →+* R') (D : DegPre R) : Prop :=
  ∃ (W : (Spec (CommRingCat.of R)).Opens) (_ : PsiOn D W) (g : (TK R').left ⟶ (TW W).left),
    g ≫ W.ι = jK R' ≫ specOf φ
end Pull
open scoped CategoryTheory.Obj in

def UnifBaseChange : Prop :=
  ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (I : Ideal R) (I' : Ideal R') (_ : AdmBase R I) (_ : AdmBase R' I')
    (φ : R →+* R') (hI : I ≤ I'.comap φ)
    (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (_ : IsSemiAbelian G)
    (U : Unif I D A G) (_ : GenericInPsiLocus φ D.toPre)
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (pG : GrpPull φ G G')
    (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (_ : A'.g = A.g)
    (gen' : (Over.pullback (jK R')).obj G' ≅ A'.A) (_ : IsMonHom gen'.hom)
    (L' : RigLB G') (pL : RigPull pG U.LG L')
    (_ : ∃ w : LB.Iso (A'.L.pull gen'.hom.left) (L'.L.pull (pullback.fst G'.hom (jK R'))),
      w.IsGen),
    ∃ (D' : DegData R' I') (pD : PullIdent φ D.toPre D'.toPre) (U' : Unif I' D' A' G')
      (hL : U'.LG = L') (P : UnifPull hI pD pG U U'),
      U'.gen = gen' ∧ (hL ▸ P.bundle : RigPull pG U.LG L') = pL
section Basic₂
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
example (G : Over (Spec (CommRingCat.of R))) [GrpObj G] : Nonempty (GrpPull (RingHom.id R) G G) := by
  have h : specOf (RingHom.id R) = 𝟙 _ := by simp [specOf]
  refine ⟨⟨𝟙 _, ?_, ?_, ?_⟩⟩
  · rw [h]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · rw [h]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have : ∀ a b, pullback.map G.hom G.hom G.hom G.hom (𝟙 _) (𝟙 _) (specOf (RingHom.id R)) a b =
        𝟙 _ := by
      intro a b
      apply pullback.hom_ext <;> simp
    rw [this]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
example {φ : R →+* R'} {I : Ideal R} {I' : Ideal R'} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] (pG : GrpPull φ G G')
    (hI : I ≤ I'.comap φ) (e : ℕ) :
    pG.thickF hI e ≫ (fstG I e G).left = (fstG I' e G').left ≫ pG.F :=
  pullback.lift_fst _ _ _
example (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (h : PullIdent φ D D') :
    GenericInPsiLocus φ D := by
  obtain ⟨W, ψW, g, hg, -⟩ := h.w_psi
  exact ⟨W, ψW, g, hg⟩
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange


