-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T14:35:47.189863+00:00
-- url     : https://prove2.me/theorems/94b59f1b-5052-45cd-b411-e6cc1c52f729
-- title:
--   Expansion Bijective Over Fields
-- statement:
--   Definitions and structural lemmas for Expansion Bijective Over Fields, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExpansionBijectiveOverFields.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_gs_zero__47fb152d3439
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_add__395e1a61c295
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_smul__9bcebbd1d3c5
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sval_zero__c17798940263
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_expandsAt_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_expandsAt_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
section Pow
variable {S : Type} [CommRing S] {X Y Z : Scheme.{0}} {L : LB X} {g : Y ⟶ X} {k : ℤ}
  {π : Y ⟶ Spec (CommRingCat.of S)}
theorem powVal_add (a b : SecOver π (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) (r : Z ⟶ Y) (z : Z)
    {i : L.ι} (hi : g (r z) ∈ L.U i) :
    powVal (a + b : SecOver π _) r z i = powVal a r z i + powVal b r z i :=
  gs_add r z _ (mem_wchart.2 fun _ => hi) _ _
theorem powVal_smul (c : S) (a : SecOver π (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) (r : Z ⟶ Y)
    (z : Z) {i : L.ι} (hi : g (r z) ∈ L.U i) :
    powVal (c • a : SecOver π _) r z i = constVal (r ≫ π) z c * powVal a r z i :=
  gs_smul π r z _ (mem_wchart.2 fun _ => hi) c _
theorem powVal_zero (r : Z ⟶ Y) (z : Z) {i : L.ι} (hi : g (r z) ∈ L.U i) :
    powVal (0 : SecOver π (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k))) r z i = 0 :=
  gs_zero' r z _ (mem_wchart.2 fun _ => hi)
end Pow
section Iso
variable {Y Y' X₁ X₂ Z₁ : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
  {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} {m : Y' ⟶ Y} {k : ℕ} {g₁ : Z₁ ⟶ X₁} {h₁ : Y' ⟶ Z₁}
end Iso
section Data
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
theorem famφ_prB (α : D.X) (i : Fin 4) : DegPre.famφ D F α i = (DegPre.prB D F).left ≫ D.famφB α i := by
  fin_cases i
  · exact (Category.comp_id _).symm
  · refine congrArg (fun q => q.left) (Eq.symm ((MonObj.comp_mul (DegPre.prB D F) (𝟙 _) (cP D _ α)).trans ?_))
    rw [comp_cP, Category.comp_id]; rfl
  · exact congrArg (fun q => q.left) (comp_cP D (DegPre.prB D F) α).symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (DegPre.prB D F)).symm
variable [Algebra R F] [IsScalarTower R (FractionRing R) F]
theorem bf_hom : (DegPre.BF D F).hom = famBase D F ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
  have e : jFK (R := R) F ≫ jK R = Spec.map (CommRingCat.ofHom (algebraMap R F)) := by
    rw [jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [← e]
  exact (Over.w (fst (TF (R := R) F) D.P.A)).symm
theorem prB_hom : (DegPre.prB D F).left ≫ D.P.A.hom =
    famBase D F ≫ Spec.map (CommRingCat.ofHom (algebraMap R F)) :=
  (Over.w (DegPre.prB D F)).trans (bf_hom D F)
end Data
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
abbrev IntSec (k : ℕ) : Type :=
  SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))
variable (D) in

abbrev IntTerm (k : ℕ) (α : D.toPre.X) : Type :=
  SecOver D.toPre.P.A.hom (LB.LinComb D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k))
theorem expandsAt_lin (e k : ℕ) (c : R) {σ σ' : IntSec U k} {f f' : ∀ α, IntTerm D k α}
    (h : U.ExpandsAt e k σ f) (h' : U.ExpandsAt e k σ' f') :
    U.ExpandsAt e k (c • σ + σ' : IntSec U k) (fun α => (c • f α + f' α : IntTerm D k α)) := by
  classical
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
  obtain ⟨S', hS'⟩ := expandsAt_val U e k σ' f' h'
  have hπ : fGl I G e ≫ G.hom = pGl U e ≫ D.toPre.P.A.hom := (Over.w (fstG I e G)).trans (Over.w (U.gt e).pG).symm
  refine expandsAt_of_val U e k _ _ (S ∪ S') fun y J hJ => ?_
  obtain ⟨z₁, v₁⟩ := hS _ (𝟙 _) y J hJ
  obtain ⟨z₂, v₂⟩ := hS' _ (𝟙 _) y J hJ
  simp only [Category.id_comp] at z₁ v₁ z₂ v₂
  refine ⟨fun α hα => ?_, fun jL hj => ?_⟩
  · rw [Finset.mem_union, not_or] at hα
    rw [sval_add' hJ, sval_smul' hJ, z₁ α hα.1, z₂ α hα.2, mul_zero, add_zero]
  · have e₁ : sv U k (c • σ + σ' : IntSec U k) (fGl I G e) y jL =
        constVal (fGl I G e ≫ G.hom) y c * sv U k σ (fGl I G e) y jL + sv U k σ' (fGl I G e) y jL :=
      (powVal_add _ _ _ y hj).trans (congrArg (· + _) (powVal_smul _ _ _ y hj))
    have w₁ := (v₁ jL hj).trans (Finset.sum_subset (Finset.subset_union_left (s₂ := S'))
      fun α _ hα => by rw [z₁ α hα, zero_mul])
    have w₂ := (v₂ jL hj).trans (Finset.sum_subset (Finset.subset_union_right (s₁ := S))
      fun α _ hα => by rw [z₂ α hα, zero_mul])
    rw [e₁, mul_add, mul_left_comm, w₁, w₂, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [sval_add' hJ, sval_smul' hJ, hπ]
    ring
theorem expandsAt_zero (e k : ℕ) :
    U.ExpandsAt e k (0 : IntSec U k) (fun α => (0 : IntTerm D k α)) :=
  expandsAt_of_val U e k _ _ ∅ fun y J hJ => ⟨fun _ _ => sval_zero' hJ _, fun jL hj => by
    rw [Finset.sum_empty]
    exact (congrArg _ (powVal_zero (π := G.hom) _ y hj)).trans (mul_zero _)⟩
def expansionPairs (k : ℕ) : Submodule R (IntSec U k × ∀ α, IntTerm D k α) where
  carrier := {x | ∀ e, U.ExpandsAt e k x.1 x.2}
  zero_mem' e := expandsAt_zero U e k
  add_mem' {x y} hx hy e := by
    have := expandsAt_lin U e k 1 (hx e) (hy e)
    simp only [one_smul] at this
    exact this
  smul_mem' c x hx e := by
    have := expandsAt_lin U e k c (hx e) (expandsAt_zero U e k)
    simp only [add_zero] at this
    exact this
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
variable (G) in

def groupBase : (UnifPre.GF (G := G) F).left ⟶ Spec (CommRingCat.of F) :=
  (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left
variable (A) in

def abelianBase : (TFK (R := R) F ⊗ A.A).left ⟶ Spec (CommRingCat.of F) := (fst (TFK (R := R) F) A.A).left
omit [GrpObj G] [IsCommMonObj G] in
theorem isPullback_groupBase : IsPullback (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left
    (groupBase G F) (pullback.snd G.hom (jK R))
    (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F))) := (IsPullback.of_hasPullback _ _).flip
abbrev GroupSec (k : ℕ) : Type :=
  SecOver (groupBase G F) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)))
def genericSec (k : ℕ) : IntSec U k →ₛₗ[algebraMap R (FractionRing R)] SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))) :=
  pullOver U.LG.L _ (p := pullback.fst G.hom (jK R)) pullback.condition (fun _ => (Category.comp_id _).symm)
variable (D) in

def genericTerm (k : ℕ) (α : D.toPre.X) :
    IntTerm D k α →ₛₗ[algebraMap R (FractionRing R)] FamTerm D.toPre (FractionRing R) k α :=
  pullOver D.toPre.P.L _ (prB_hom D.toPre (FractionRing R)) (famφ_prB D.toPre (FractionRing R) α)
def extendSec (k : ℕ) : SecOver (pullback.snd G.hom (jK R))
    (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)))
      →ₛₗ[algebraMap (FractionRing R) F] GroupSec U F k :=
  pullOver U.LG.L _ (isPullback_groupBase F).w (fun _ => rfl)
variable {k : ℕ} {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))}
end GlobalTheory.FieldBaseChange
namespace GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR FieldBaseChange
end GlobalTheory


