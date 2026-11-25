-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T14:08:52.134211+00:00
-- url     : https://prove2.me/theorems/e7a1f5d7-efdb-4003-b73e-e4b2199ee967
-- title:
--   Eps Pullback Fst
-- statement:
--   Definitions and structural lemmas for Eps Pullback Fst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullbackDegree/EpsPullbackFst.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_isAb_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_pull

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
namespace ReciprocityTheory.ChartRestriction.G.Out.UBC
open Semi
section Adj
end Adj
def PolPullSt : Prop :=
  ∀ (R : Type) [CommRing R] (S' : Scheme.{0}) (f : S' ⟶ Spec (CommRingCat.of R))
    (P : PolAV (Spec (CommRingCat.of R))),
    Rigidified ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f)) ∧
    Sym ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f)) ∧
    RelAmple ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f)) ∧
    KTriv ((Over.pullback f).obj P.A) (P.L.pull (pullback.fst P.A.hom f))
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
abbrev pA (φ : R →+* R') (A : Over (Spec (CommRingCat.of R))) : Over (Spec (CommRingCat.of R')) :=
  (Over.pullback (specOf φ)).obj A
abbrev pF (φ : R →+* R') (A : Over (Spec (CommRingCat.of R))) : (pA φ A).left ⟶ A.left :=
  (Iso.refl (pA φ A)).hom.left ≫ pullback.fst A.hom (specOf φ)
lemma pF_eq (φ : R →+* R') (A : Over (Spec (CommRingCat.of R))) :
    pF φ A = pullback.fst A.hom (specOf φ) := by
  simp [pF]
def pullPol (φ : R →+* R') (P : PolAV (Spec (CommRingCat.of R))) [hP : Fact PolPullSt] :
    PolAV (Spec (CommRingCat.of R')) where
  A := pA φ P.A
  isAb := TLinPf.isAb_pullback _ P.A P.isAb
  g := P.g
  smoothDim := by
    show SmoothOfRelativeDimension P.g (pullback.snd P.A.hom (specOf φ))
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := P.g)
    first
      | exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P.g)
          (IsPullback.of_hasPullback P.A.hom (specOf φ)) P.smoothDim
      | exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension P.g)
          (IsPullback.of_hasPullback P.A.hom (specOf φ)).flip P.smoothDim
  L := P.L.pull (pF φ P.A)
  isLB := Semi.LB.isLB_pull P.isLB _
  rigid := by rw [pF_eq]; exact (hP.out R (Spec (CommRingCat.of R')) (specOf φ) P).1
  sym := by rw [pF_eq]; exact (hP.out R (Spec (CommRingCat.of R')) (specOf φ) P).2.1
  ample := by rw [pF_eq]; exact (hP.out R (Spec (CommRingCat.of R')) (specOf φ) P).2.2.1
  ktriv := by rw [pF_eq]; exact (hP.out R (Spec (CommRingCat.of R')) (specOf φ) P).2.2.2
def pc (φ : R →+* R') {A : Over (Spec (CommRingCat.of R))}
    (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A) : 𝟙_ (Over (Spec (CommRingCat.of R'))) ⟶ pA φ A :=
  (Over.mapPullbackAdj (specOf φ)).homEquiv _ _ (toUnit _ ≫ x)
section Kappa
variable (φ : R →+* R') (hφ : Function.Injective φ)
def kap : FractionRing R →+* FractionRing R' :=
  IsLocalization.map (FractionRing R') φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ)
abbrev kapS : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of (FractionRing R)) :=
  Spec.map (CommRingCat.ofHom (kap φ hφ))
end Kappa
end ReciprocityTheory.ChartRestriction.G.Out.UBC


