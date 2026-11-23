-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
-- name    : Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_MulGenNegRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:29.755796+00:00
-- url     : https://prove2.me/theorems/abeee406-51ec-465c-9ada-e94a2320ad99
-- title:
--   Mul Gen Neg Right
-- statement:
--   Definitions and structural lemmas for Mul Gen Neg Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/AbelianLawCounterexamples/MulGenNegRight.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_TrivialBiextension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BiextSignTwist
theorem res_neg {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)ˣ) :
    res h (-a) = -res h a := by
  ext; simp [res]
theorem pullU_neg {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)ˣ) :
    pullU f U (-a) = -pullU f U a := by
  ext; simp [pullU]
def negGen {X : Scheme.{u}} {L : LB X} (t : LB.Gen L) : LB.Gen L := ⟨fun i => -t.s i⟩
theorem negGen_isGen {X : Scheme.{u}} {L : LB X} {t : LB.Gen L} (h : t.IsGen) :
    (negGen t).IsGen := fun i j => by
  simp only [negGen, res_neg, mul_neg]
  rw [h i j]
section
variable {X Y Z : Scheme.{u}} (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']
theorem negGen_negGen (t : LB.Gen L) : negGen (negGen t) = t := by
  cases t; simp [negGen]
theorem pullGen_neg (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen L φ ε (negGen t) h = negGen (LB.pullGen L φ ε t h) :=
  congrArg LB.Gen.mk (funext fun _ => (congrArg (res _) (pullU_neg _ _ _)).trans (res_neg _ _))
theorem mulGen_neg_left (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    LB.mulGen L φ ε φ' ε' (negGen t) t' = negGen (LB.mulGen L φ ε φ' ε' t t') :=
  congrArg LB.Gen.mk (funext fun _ => (congrArg (· * _) (res_neg _ _)).trans (neg_mul _ _))
theorem mulGen_neg_right (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) :
    LB.mulGen L φ ε φ' ε' t (negGen t') = negGen (LB.mulGen L φ ε φ' ε' t t') :=
  congrArg LB.Gen.mk (funext fun _ => (congrArg (_ * ·) (res_neg _ _)).trans (mul_neg _ _))
theorem corr_neg {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : LB.Gen.Corr L φ ε φ' ε' t t') : LB.Gen.Corr L φ ε φ' ε' (negGen t) (negGen t') :=
  fun j j' a b c => (res_neg _ _).trans ((congrArg Neg.neg (h j j' a b c)).trans (res_neg _ _).symm)
end
variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]
def negBiext {P : LB (G2 G).left} (β : IsBiext G P) : IsBiext G P where
  isLB := β.isLB
  law1 := negGen β.law1
  law2 := negGen β.law2
  isGen1 := negGen_isGen β.isGen1
  isGen2 := negGen_isGen β.isGen2
  assoc1 := by
    simp only [pullGen_neg, mulGen_neg_left, mulGen_neg_right, negGen_negGen]; exact β.assoc1
  comm1 := by simp only [pullGen_neg]; exact corr_neg _ β.comm1
  assoc2 := by
    simp only [pullGen_neg, mulGen_neg_left, mulGen_neg_right, negGen_negGen]; exact β.assoc2
  comm2 := by simp only [pullGen_neg]; exact corr_neg _ β.comm2
  compat := by
    simp only [pullGen_neg, mulGen_neg_left, mulGen_neg_right, negGen_negGen]
    exact corr_neg _ β.compat
abbrev lamφ : ULift.{u} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) :=
  fun I => (psum G (x2 G) I.down).left
def LawIsCube (L : RigLB G) (c : CubicalStr G L)
    (ψ : ULift.{u} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (law : LB.Gen (LB.LinComb (abelian₂ G L.L) ψ lawε)) : Prop :=
  ∀ (J : ULift.{u} (Fin 3) → ULift.{u} (Finset (Fin 2)) → L.L.ι) (j : thK → L.L.ι),
    (∀ k I k' I', ψ k ≫ lamφ G I = ψ k' ≫ lamφ G I' → J k I = J k' I') →
    LB.Coh L.L (thφ G (x3 G)) j →
    (∀ k I I', ψ k ≫ lamφ G I = thφ G (x3 G) I' → J k I = j I') →
    res (inf_le_left : LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j ≤ _) (law.s J) =
    res (inf_le_right : LB.wchart (abelian₂ G L.L) ψ J ⊓ LB.wchart L.L (thφ G (x3 G)) j ≤ _) (c.t.s j)
def AbelianLawCounterexample : Prop :=
  ∀ (S : Scheme.{u}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L),
    ∃ β : IsBiext G (abelian₂ G L.L), LawIsCube G L c _ β.law1 ∧ LawIsCube G L c _ β.law2
section Trivial
open GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension (trivLB pull_one mul_one' corr_one isGen_one)
theorem linComb_g_one {X Y : Scheme.{u}} (L : LB X) (hL : ∀ i j, L.g i j = 1) {K : Type u}
    [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (i j) : (LB.LinComb L φ ε).g i j = 1 :=
  Finset.prod_eq_one fun k _ =>
    (congrArg (· ^ ε k) ((congrArg _ ((congrArg _ (hL _ _)).trans (map_one _))).trans
      (map_one _))).trans (one_zpow _)
theorem isGen_one' {X : Scheme.{u}} (L : LB X) (hL : ∀ i j, L.g i j = 1) :
    LB.Gen.IsGen (L := L) ⟨fun _ => 1⟩ := fun i j => by
  rw [hL]
  exact (map_one _).trans ((_root_.one_mul _).trans (map_one _)).symm
theorem isLB_of_g_one {X : Scheme.{u}} (L : LB X) (hL : ∀ i j, L.g i j = 1)
    (hc : ⨆ i, L.U i = ⊤) : L.IsLB :=
  ⟨hc, fun _ => by rw [hL, map_one], fun _ _ _ => by
    rw [hL, hL, hL, map_one, map_one, map_one, _root_.mul_one]⟩
def oneRig : RigLB G :=
  ⟨trivLB _, ⟨fun _ => 1⟩, isLB_of_g_one _ (fun _ _ => rfl) (@iSup_const _ PUnit _ _ _), isGen_one _ _⟩
def oneCub : CubicalStr G (oneRig G) where
  t := ⟨fun _ => 1⟩
  isGen := isGen_one _ _
  face := fun _ => corr_one _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (fun _ => rfl)
  cubeSymmetric_swap_first := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  cubeSymmetric_swap_last := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  cocycle := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
theorem lam_g_one (i j) : (abelian₂ G (oneRig G).L).g i j = 1 :=
  linComb_g_one (trivLB _) (fun _ _ => rfl) _ _ i j
def oneBiext : IsBiext G (abelian₂ G (oneRig G).L) where
  isLB := isLB_of_g_one _ (lam_g_one G) (top_le_iff.1 fun _ _ =>
    Opens.mem_iSup.2 ⟨fun _ => PUnit.unit, Set.mem_iInter.2 fun _ => trivial⟩)
  law1 := ⟨fun _ => 1⟩
  law2 := ⟨fun _ => 1⟩
  isGen1 := isGen_one' _ (linComb_g_one _ (lam_g_one G) _ _)
  isGen2 := isGen_one' _ (linComb_g_one _ (lam_g_one G) _ _)
  comm1 := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  comm2 := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  assoc1 := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
  assoc2 := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
  compat := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _
      (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
      (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _
      (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl))
      (pull_one _ _ _ _ _ fun _ => rfl))
end Trivial
end GlobalTheory.BiextSignTwist


