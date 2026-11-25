-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T13:08:00.889889+00:00
-- url     : https://prove2.me/theorems/c59a3689-a767-5cdf-b8b9-9cbc977a05dd
-- title:
--   Objects
-- statement:
--   Definitions and structural lemmas for Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Objects.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isPlurisubharmonic
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isSmoothPotential
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
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot mInt MIntegrable)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ThGe ell errE)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X]
def FormNonneg (A : FinHolAtlas D X) (V : Set X) (P : LocPot X) : Prop :=
  ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (V ∩ P.U x), ∀ w : Fin D → ℂ,
    0 ≤ levi (P.φ x ∘ (A.chart k).symm) y w
def LeviLe (A : FinHolAtlas D X) (V : Set X) (a : ℝ) (P : LocPot X) (b : ℝ) (Q : LocPot X) :
    Prop :=
  ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (V ∩ P.U x ∩ Q.U x), ∀ w : Fin D → ℂ,
    a * levi (P.φ x ∘ (A.chart k).symm) y w ≤ b * levi (Q.φ x ∘ (A.chart k).symm) y w
structure KaehlerForm (A : FinHolAtlas D X) where

  pot : LocPot X
  isPot : IsPotential A pot
  pos : IsPosPot A pot
def KaehlerForm.vol {A : FinHolAtlas D X} (Om : KaehlerForm A) : ℝ :=
  mInt A (fun _ => Om.pot) fun _ => 1
def potForm (th : LocPot X) (u : X → ℝ) : LocPot X := th + LocPot.ofFun u
structure IsBoundedPotForm (A : FinHolAtlas D X) (Yo : Set X) (r : X → ℝ) (Om : KaehlerForm A)
    (C₁ : ℝ) (th : LocPot X) (u : X → ℝ) : Prop where
  th_pot : IsPotential A th
  th_le : LeviLe A Set.univ 1 th 1 Om.pot
  neg_le_th : LeviLe A Set.univ (-1) Om.pot 1 th
  u_smooth : A.SmoothOn Yo u
  u_nonpos : ∀ x ∈ Yo, u x ≤ 0
  le_u : ∀ x ∈ Yo, -(C₁ * Real.log (r x)) ≤ u x
  nonneg : FormNonneg A Yo (potForm th u)
  smooth_or_pole : A.Smooth u ∨ ∀ y, y ∉ Yo → Tendsto u (𝓝[Yo] y) atBot
def IsSmoothPotForm (A : FinHolAtlas D X) (Yo : Set X) (r : X → ℝ) (Om : KaehlerForm A) (C₁ : ℝ)
    (th : LocPot X) (u : X → ℝ) : Prop :=
  IsBoundedPotForm A Yo r Om C₁ th u ∧ A.Smooth u
def IsBoundedNonnegForm (A : FinHolAtlas D X) (a om : LocPot X) (C : ℝ) : Prop :=
  IsPotential A a ∧ FormNonneg A Set.univ a ∧ LeviLe A Set.univ 1 a C om
def tail (Yo : Set X) (r : X → ℝ) (R₀ : ℝ) : Set X := {x | x ∈ Yo ∧ R₀ ≤ r x}
def MassBound (A : FinHolAtlas D X) (Yo : Set X) (T Θ : Fin D → LocPot X) (V : ℝ) : Prop :=
  MIntegrable A T (Yo.indicator 1) ∧ mInt A T (Yo.indicator 1) = mInt A Θ (fun _ => 1) ∧
    mInt A Θ (fun _ => 1) ≤ V
def TailMassBound (A : FinHolAtlas D X) (Yo : Set X) (r : X → ℝ) (T : Fin D → LocPot X)
    (CE : ℝ) : Prop :=
  ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ → MIntegrable A T ((tail Yo r R₀).indicator 1) ∧
    mInt A T ((tail Yo r R₀).indicator 1) ≤ CE * Real.log R₀ ^ D / R₀
def TailLogBound (A : FinHolAtlas D X) (Yo : Set X) (r : X → ℝ) (T : Fin D → LocPot X)
    (CE : ℝ) : Prop :=
  ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ →
    MIntegrable A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) ∧
    mInt A T ((tail Yo r R₀).indicator fun x => Real.log (r x)) ≤
      CE * Real.log R₀ ^ (D + 1) / R₀
structure System {A : FinHolAtlas D X} (R : RegChartData A) where

  ph : ℝ → X → ℝ

  C : ℝ

  ell₀ : ℝ
  smooth : ∀ t, 0 < t → ell₀ ≤ ell t → A.Smooth (ph t)
  le_ph : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ R.Yo, R.φ x ≤ ph t x
  ph_le : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x, ph t x ≤ C
  le_log : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x, -(C * Real.log (ell t)) ≤ ph t x
  thGe : ∀ t, 0 < t → ell₀ ≤ ell t → ThGe A R.θ (ph t) R.om (-errE C t)
  near : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ R.Yo, R.r x ≤ ell t →
    ph t x ≤ R.φ x + t ^ (1 / 3 : ℝ) + errE C t
  far : ∀ t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ R.Yo,
    ph t x ≤ R.φ x + t ^ (1 / 3 : ℝ) + errE C t * R.r x
  mono : ∀ t t₀, 0 < t → t ≤ t₀ → ell₀ ≤ ell t₀ → ∀ x, ph t x ≤ ph t₀ x + C * errE C t₀
  c2 : ∀ (k : Fin A.n) (K : Set (Fin D → ℂ)), IsCompact K →
    K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' R.Yo →
    TendstoUniformlyOn (fun t y => ph t ((A.chart k).symm y)) (fun y => R.φ ((A.chart k).symm y))
        (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => ph t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fun y' => R.φ ((A.chart k).symm y')) y) (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ fun y' => ph t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => R.φ ((A.chart k).symm y')) y) (𝓝[>] 0) K
def thetaOmega {A : FinHolAtlas D X} (R : RegChartData A) : LocPot X := R.θ + R.om
namespace System
variable {A : FinHolAtlas D X} {R : RegChartData A} (S : System R)
def uT (t : ℝ) : X → ℝ := fun x => S.ph t x - S.C
def curr (t : ℝ) : LocPot X := potForm (thetaOmega R) (S.uT t)
end System
def lincomb : (m : ℕ) → (Fin m → ℝ) → (Fin m → LocPot X) → LocPot X
  | 0, _, _ => LocPot.ofFun fun _ => 0
  | m + 1, c, P => LocPot.rsmul (c 0) (P 0) + lincomb m (fun i => c i.succ) fun i => P i.succ
structure Family (A : FinHolAtlas D X) where

  m : ℕ

  R : Fin m → RegChartData A

  sys : ∀ i, System (R i)
  Yo : Set X
  r : X → ℝ
  om : LocPot X
  Yo_eq : ∀ i, (R i).Yo = Yo
  r_eq : ∀ i, ∀ x ∈ Yo, (R i).r x = r x
  om_eq : ∀ i, (R i).om = om
def Family.chernForm {A : FinHolAtlas D X} (F : Family A) (c : Fin F.m → ℝ) (t : ℝ) : LocPot X :=
  lincomb F.m c fun i => (F.R i).θ + LocPot.ofFun ((F.sys i).ph t)
section Inhabitants
open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (projLineChartData projLine_fubiniStudy_isPosPot)
theorem tendstoUniformlyOn_self {α β ι : Type*} [UniformSpace β] (f : α → β) (p : Filter ι)
    (s : Set α) : TendstoUniformlyOn (fun _ => f) f p s :=
  fun _ hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu
theorem errE_zero (t : ℝ) : errE 0 t = 0 := by simp [errE]
theorem levi_const {ι : Type*} [Fintype ι] (c : ℝ) (z w : ι → ℂ) :
    levi (fun _ : ι → ℂ => c) z w = 0 := by
  simp [levi]
def projectiveLineKaehler : KaehlerForm p1 := ⟨fsPot, projLine_isSmoothPotential, projLine_fubiniStudy_isPosPot⟩
def projectiveLineConstantSystem : System projLineChartData where
  ph _ _ := 0
  C := 0
  ell₀ := 1
  smooth _ _ _ _ := contDiffOn_const
  le_ph _ _ _ _ _ := le_rfl
  ph_le _ _ _ _ := le_rfl
  le_log _ _ _ _ := by simp
  thGe t _ _ := by
    intro x k y _ w
    have h : ((fun z => projLineChartData.θ.φ x z + (fun _ : OnePoint ℂ => (0 : ℝ)) z) ∘ (p1.chart k).symm) =
        fun _ => (0 : ℝ) := by
      funext z
      show (0 : ℝ) + 0 = 0
      simp
    rw [h, levi_const, errE_zero]
    simp
  near t ht _ _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  far t ht _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t * _
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  mono _ _ _ _ _ _ := by simp
  c2 _ _ _ _ := ⟨tendstoUniformlyOn_self _ _ _, tendstoUniformlyOn_self _ _ _,
    tendstoUniformlyOn_self _ _ _⟩
def projectiveLineFamily : Family p1 where
  m := 1
  R _ := projLineChartData
  sys _ := projectiveLineConstantSystem
  Yo := projLineChartData.Yo
  r := projLineChartData.r
  om := fsPot
  Yo_eq _ := rfl
  r_eq _ _ _ := rfl
  om_eq _ := rfl
end Inhabitants
end
end GroundTheory.Heights₂.Heights.AnalyticLimit


