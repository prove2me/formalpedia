-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_FubiniStudyPotentialProductIsPotential
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_FubiniStudyPotentialProductIsPotential
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:20.441051+00:00
-- url     : https://prove2.me/theorems/a73ce0a6-0207-46a0-84f8-1a82c6ff332a
-- title:
--   Fubini Study Potential Product Is Potential
-- statement:
--   Definitions and structural lemmas for Fubini Study Potential Product Is Potential, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/FubiniStudyPotentialProductIsPotential.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply


set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint CompatibleChartOperations
noncomputable section
def appendCLE (e e' : ℕ) : ((Fin e → ℂ) × (Fin e' → ℂ)) ≃L[ℂ] (Fin (e + e') → ℂ) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin e) (Fin e') ℂ ℂ).symm.trans
    (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)).toContinuousLinearEquiv
def prodChart {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n) :
    OpenPartialHomeomorph (X × Y) (Fin (e + e') → ℂ) :=
  ((A.chart j).prod (B.chart k)).trans (appendCLE e e').toHomeomorph.toOpenPartialHomeomorph
section ProdChart
variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n)
theorem prodChart_symm_apply (z : Fin (e + e') → ℂ) :
    (prodChart A B j k).symm z = ((A.chart j).symm ((appendCLE e e').symm z).1,
      (B.chart k).symm ((appendCLE e e').symm z).2) := rfl
theorem prodChart_source :
    (prodChart A B j k).source = (A.chart j).source ×ˢ (B.chart k).source := by
  simp [prodChart]
theorem mem_prodChart_target (z : Fin (e + e') → ℂ) :
    z ∈ (prodChart A B j k).target ↔
      ((appendCLE e e').symm z).1 ∈ (A.chart j).target ∧
        ((appendCLE e e').symm z).2 ∈ (B.chart k).target := by
  simp [prodChart]
end ProdChart
section ProdChart2
variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)
theorem prodChart_holo (j j' : Fin A.n) (k k' : Fin B.n) :
    AnalyticOnNhd ℂ (prodChart A B j' k' ∘ (prodChart A B j k).symm)
      ((prodChart A B j k).target ∩ (prodChart A B j k).symm ⁻¹' (prodChart A B j' k').source) := by
  intro z ⟨ht, hs⟩
  rw [mem_prodChart_target] at ht
  rw [Set.mem_preimage, prodChart_source, prodChart_symm_apply] at hs
  have h1 := A.holo j j' _ ⟨ht.1, hs.1⟩
  have h2 := B.holo k k' _ ⟨ht.2, hs.2⟩
  have hF : AnalyticAt ℂ (fun z => ((appendCLE e e').symm z).1) z :=
    ((ContinuousLinearMap.fst ℂ _ _).comp (appendCLE e e').symm.toContinuousLinearMap).analyticAt z
  have hS : AnalyticAt ℂ (fun z => ((appendCLE e e').symm z).2) z :=
    ((ContinuousLinearMap.snd ℂ _ _).comp (appendCLE e e').symm.toContinuousLinearMap).analyticAt z
  have hp : AnalyticAt ℂ (fun z => ((A.chart j' ∘ (A.chart j).symm) ((appendCLE e e').symm z).1,
      (B.chart k' ∘ (B.chart k).symm) ((appendCLE e e').symm z).2)) z :=
    (h1.comp_of_eq hF rfl).prod (h2.comp_of_eq hS rfl)
  exact (appendCLE e e').analyticAt _ |>.comp hp
end ProdChart2
def prodAtlas {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) : FinHolAtlas (e + e') (X × Y) where
  n := A.n * B.n
  chart i := prodChart A B (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  cover := by
    intro x
    obtain ⟨j, hj⟩ := A.cover x.1
    obtain ⟨k, hk⟩ := B.cover x.2
    refine ⟨finProdFinEquiv (j, k), ?_⟩
    simp only [Equiv.symm_apply_apply, prodChart_source]
    exact ⟨hj, hk⟩
  holo := fun i i' => prodChart_holo A B _ _ _ _
section Pull
variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y)
end Pull
def LocPot.pr1 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (P : LocPot X) :
    LocPot (X × Y) :=
  P.pullback Prod.fst continuous_fst
def LocPot.pr2 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (P : LocPot Y) :
    LocPot (X × Y) :=
  P.pullback Prod.snd continuous_snd
open scoped Classical in

def openAtlas {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    FinHolAtlas b U where
  n := 1
  chart _ :=
    { toFun := Subtype.val
      invFun := fun y => if h : y ∈ U then ⟨y, h⟩ else ⟨hne.some, hne.some_mem⟩
      source := Set.univ
      target := U
      map_source' := fun x _ => x.2
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := fun x _ => by simp [x.2]
      right_inv' := fun y hy => by simp [hy]
      open_source := isOpen_univ
      open_target := hU
      continuousOn_toFun := continuous_subtype_val.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_domRestrict]
        have : (U.domRestrict fun y => if h : y ∈ U then (⟨y, h⟩ : U) else ⟨hne.some, hne.some_mem⟩) =
            id := by
          funext y
          simp only [Set.domRestrict_apply, dif_pos y.2, id]
        rw [this]
        exact continuous_id }
  cover := fun _ => ⟨0, Set.mem_univ _⟩
  holo := by
    intro j k z ⟨hz, _⟩
    refine analyticAt_id.congr ?_
    filter_upwards [hU.mem_nhds hz] with y hy
    simp [hy]
def p1p1 : FinHolAtlas 2 (OnePoint ℂ × OnePoint ℂ) := prodAtlas p1 p1
def fubiniStudyPotentialProduct : LocPot (OnePoint ℂ × OnePoint ℂ) :=
  fsPot.pullback Prod.fst continuous_fst + fsPot.pullback Prod.snd continuous_snd
open scoped Classical in

def diagSec (x y : OnePoint ℂ × OnePoint ℂ) : ℂ :=
  if x.1 = ∞ then
    (if x.2 = ∞ then crd1 y.1 - crd1 y.2 else crd1 y.1 * crd0 y.2 - 1)
  else
    (if x.2 = ∞ then 1 - crd0 y.1 * crd1 y.2 else crd0 y.2 - crd0 y.1)
end
end ReciprocityTheory.AnForm.M


