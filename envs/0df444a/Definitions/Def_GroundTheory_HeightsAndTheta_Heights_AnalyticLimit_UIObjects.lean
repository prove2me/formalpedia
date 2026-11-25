-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_UIObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_UIObjects
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:23:20.132935+00:00
-- url     : https://prove2.me/theorems/f3fac9db-2309-57d7-b523-f72db6f18212
-- title:
--   UIObjects
-- statement:
--   Definitions and structural lemmas for UIObjects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/UIObjects.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isHolomorphicSection
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isPlurisubharmonic
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isSimpleNormalCrossing
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
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  integralWith)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)
noncomputable section
section Defs
variable {W : Type} [TopologicalSpace W]
def secNorm (L : LocPot W) (s : W → W → ℂ) (x : W) : ℝ := ‖s x x‖ * Real.exp (-L.φ x x)
def greenEp (L : LocPot W) (s : W → W → ℂ) (ε : ℝ) (x : W) : ℝ :=
  Real.log (1 + ε / secNorm L s x ^ 2)
def kappaEp (L : LocPot W) (s : W → W → ℂ) (ε : ℝ) : LocPot W :=
  LocPot.rsmul 2 L + LocPot.ofFun fun x => Real.log (secNorm L s x ^ 2 + ε)
def curForms {D : ℕ} (th : Fin (D + 1) → LocPot W) (u : Fin (D + 1) → ℝ → W → ℝ) (t : ℝ) :
    Fin (D + 1) → LocPot W :=
  fun i => potForm (th i) (u i t)
def mixedForms {D : ℕ} (Om : LocPot W) (T : Fin (D + 1) → LocPot W) (b : ℕ) :
    Fin (D + 1) → LocPot W :=
  fun i => if (i : ℕ) < b then T i else Om
def restForms {D : ℕ} (Om : LocPot W) (T : Fin (D + 1) → LocPot W) (b : ℕ) : Fin D → LocPot W :=
  fun i => if (i : ℕ) < b then T i.castSucc else Om
def restrictForms {D : ℕ} (S : Set W) (Φ : Fin D → LocPot W) : Fin D → LocPot S :=
  fun i => (Φ i).pullback Subtype.val continuous_subtype_val
end Defs
structure UIData (D : ℕ) (W : Type) [TopologicalSpace W] where

  A : FinHolAtlas (D + 1) W

  Om : KaehlerForm A

  L : LocPot W

  s : W → W → ℂ

  nc : ℕ

  mult : Fin nc → ℕ

  comp : Fin nc → Set W

  B : ∀ k, FinHolAtlas D (comp k)
  L_pot : IsPotential A L
  s_sec : IsSection A L s
  s_snc : IsSNC A L s mult comp
  B_holo : ∀ k, HoloMap (B k) A Subtype.val

  Yo : Set W
  Yo_open : IsOpen Yo
  bd_analytic : A.IsAnalyticSubset Yoᶜ
  bd_interior : interior Yoᶜ = ∅
  bdComp_analytic : ∀ k, (B k).IsAnalyticSubset (Subtype.val ⁻¹' Yo)ᶜ
  bdComp_interior : ∀ k, interior ((Subtype.val ⁻¹' Yo : Set (comp k))ᶜ) = ∅

  r : W → ℝ

  th : Fin (D + 1) → LocPot W

  u : Fin (D + 1) → ℝ → W → ℝ

  lim : Fin (D + 1) → W → ℝ

  C : ℝ

  C₁ : ℝ

  ell₀ : ℝ

  CE : ℝ
  form : ∀ a t, 0 < t → ell₀ ≤ ell t → IsSmoothPotForm A Yo r Om C₁ (th a) (u a t)
  lim_le : ∀ a t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ Yo, lim a x ≤ u a t x
  near : ∀ a t, 0 < t → ell₀ ≤ ell t → ∀ x ∈ Yo, r x ≤ ell t →
    u a t x ≤ lim a x + t ^ (1 / 3 : ℝ) + errE C t
  mono : ∀ a t t₀, 0 < t → t ≤ t₀ → ell₀ ≤ ell t₀ → ∀ x, u a t x ≤ u a t₀ x + C * errE C t₀
  tail : ∀ b, b ≤ D → ∀ t, 0 < t → ell₀ ≤ ell t →
    TailLogBound A Yo r (mixedForms Om.pot (curForms th u t) b) CE
  tailComp : ∀ k b, b ≤ D → ∀ t, 0 < t → ell₀ ≤ ell t →
    TailLogBound (B k) (Subtype.val ⁻¹' Yo) (r ∘ Subtype.val)
      (restrictForms (comp k) (restForms Om.pot (curForms th u t) b)) CE
namespace UIData
variable {D : ℕ} {W : Type} [TopologicalSpace W] (S : UIData D W)
def T (t : ℝ) : Fin (D + 1) → LocPot W := curForms S.th S.u t
def green (ε : ℝ) : W → ℝ := greenEp S.L S.s ε
def J (a : ℕ) (ε t : ℝ) : ℝ := mInt S.A (mixedForms S.Om.pot (S.T t) a) (S.green ε)
def rest (a : ℕ) (t : ℝ) : Fin D → LocPot W := restForms S.Om.pot (S.T t) a
def divInt (Φ : Fin D → LocPot W) (g : W → ℝ) : ℝ :=
  ∑ k, (S.mult k : ℝ) * mInt (S.B k) (restrictForms (S.comp k) Φ) (g ∘ Subtype.val)
def plTerm (a : ℕ) (ha : a < D + 1) (ε t : ℝ) : ℝ :=
  mInt S.A (Fin.cons (kappaEp S.L S.s ε) (S.rest a t)) (S.u ⟨a, ha⟩ t) -
    2 * S.divInt (S.rest a t) (S.u ⟨a, ha⟩ t)
def gap (a : ℕ) (ha : a < D + 1) (t₀ t : ℝ) : W → ℝ :=
  fun x => S.u ⟨a, ha⟩ t₀ x + S.C * errE S.C t₀ - S.u ⟨a, ha⟩ t x
def errW (a : ℕ) (ha : a < D + 1) (t₀ t : ℝ) : ℝ :=
  mInt S.A (mixedForms S.Om.pot (S.T t) a) (S.gap a ha t₀ t)
def errDiv (a : ℕ) (ha : a < D + 1) (t₀ t : ℝ) : ℝ :=
  S.divInt (S.rest a t) (S.gap a ha t₀ t)
end UIData
def UniformIntegrability.Statement : Prop :=
  ∀ {D : ℕ} {W : Type} [TopologicalSpace W] [CompactSpace W] [T2Space W] (S : UIData D W),
    ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∃ t₁, 0 < t₁ ∧ ∀ ε t, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ →
      S.ell₀ ≤ ell t → mInt S.A (S.T t) (S.green ε) ≤ η
section Inhabitant
open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isPlurisubharmonic projLine_isHolomorphicSection projLine_isSimpleNormalCrossing ptAtlas)
open OnePoint
theorem analyticOnNhd_fin_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : (Fin 0 → ℂ) → E) (s : Set (Fin 0 → ℂ)) : AnalyticOnNhd ℂ f s := by
  intro z _
  have h : f = fun _ => f z := funext fun w => congrArg f (Subsingleton.elim w z)
  rw [h]
  exact analyticAt_const
theorem isAnalyticSubset_empty {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) :
    A.IsAnalyticSubset ∅ := by
  intro x
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, fun _ _ => 1,
    fun _ _ => analyticOnNhd_const, ?_⟩
  ext y
  simp
theorem mInt_zero_fun {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) : mInt A Φ (fun _ => 0) = 0 := by
  unfold mInt
  split_ifs
  · simp [integralWith]
  · rfl
theorem mIntegrable_zero_fun {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) : MIntegrable A Φ (fun _ => 0) := by
  intro j K _ _
  simp only [zero_mul]
  exact integrableOn_zero
theorem tailLogBound_of_small {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Yo : Set X) (r : X → ℝ) (hr : ∀ x, r x < Real.exp 1) (T : Fin e → LocPot X) :
    TailLogBound A Yo r T 0 := by
  intro R₀ hR₀
  have h : ((tail Yo r R₀).indicator fun x => Real.log (r x)) = fun _ => 0 := by
    funext x
    have hx : x ∉ tail Yo r R₀ := fun hx => lt_irrefl _ ((hR₀.trans hx.2).trans_lt (hr x))
    simp [hx]
  rw [h, mInt_zero_fun]
  exact ⟨mIntegrable_zero_fun A T, by simp⟩
theorem one_lt_exp_one : (1 : ℝ) < Real.exp 1 := by
  have := Real.add_one_lt_exp (x := 1) one_ne_zero
  linarith
theorem inf_comp (k : Fin 1) : (![{∞}] : Fin 1 → Set (OnePoint ℂ)) k = {∞} := by
  fin_cases k
  rfl
abbrev infUnique (k : Fin 1) : Unique ((![{∞}] : Fin 1 → Set (OnePoint ℂ)) k) where
  default := ⟨∞, by rw [inf_comp]; exact Set.mem_singleton _⟩
  uniq y := by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact Subtype.ext y.2
theorem projectiveLine_smoothPotForm :
    IsSmoothPotForm p1 Set.univ (fun _ => (1 : ℝ)) projectiveLineKaehler 0 fsPot (fun _ => 0) := by
  refine ⟨⟨projLine_isSmoothPotential, fun _ _ _ _ _ => le_rfl, ?_, fun _ => contDiffOn_const,
    fun _ _ => le_rfl, fun _ _ => by simp, ?_, Or.inl fun _ => contDiffOn_const⟩,
    fun _ => contDiffOn_const⟩
  · intro x k y hy w
    have := projLine_isPlurisubharmonic x k y ⟨hy.1, hy.2.1.2⟩ w
    show -1 * levi (fsPot.φ x ∘ (p1.chart k).symm) y w ≤
      1 * levi (fsPot.φ x ∘ (p1.chart k).symm) y w
    linarith
  · intro x k y hy w
    have h : (potForm fsPot fun _ => (0 : ℝ)).φ x = fsPot.φ x := funext fun z => add_zero _
    rw [h]
    exact projLine_isPlurisubharmonic x k y ⟨hy.1, hy.2.2.1⟩ w
def projectiveLineUniformIntegrabilityData : UIData 0 (OnePoint ℂ) where
  A := p1
  Om := projectiveLineKaehler
  L := fsPot
  s := projectiveLinePairSection
  nc := 1
  mult := ![1]
  comp := ![{∞}]
  B k := @ptAtlas _ _ (infUnique k)
  L_pot := projLine_isSmoothPotential
  s_sec := projLine_isHolomorphicSection
  s_snc := projLine_isSimpleNormalCrossing
  B_holo _ := ⟨continuous_subtype_val, fun _ _ => analyticOnNhd_fin_zero _ _⟩
  Yo := Set.univ
  Yo_open := isOpen_univ
  bd_analytic := by rw [Set.compl_univ]; exact isAnalyticSubset_empty p1
  bd_interior := by simp
  bdComp_analytic _ := by rw [Set.preimage_univ, Set.compl_univ]; exact isAnalyticSubset_empty _
  bdComp_interior _ := by simp
  r _ := 1
  th _ := fsPot
  u _ _ _ := 0
  lim _ _ := 0
  C := 0
  C₁ := 0
  ell₀ := 1
  CE := 0
  form _ _ _ _ := projectiveLine_smoothPotForm
  lim_le _ _ _ _ _ _ := le_rfl
  near _ t ht _ _ _ _ := by
    show (0 : ℝ) ≤ 0 + t ^ (1 / 3 : ℝ) + errE 0 t
    rw [errE_zero]
    have := Real.rpow_nonneg ht.le (1 / 3 : ℝ)
    linarith
  mono _ _ t₀ _ _ _ _ := by
    show (0 : ℝ) ≤ 0 + 0 * errE 0 t₀
    simp
  tail _ _ _ _ _ := tailLogBound_of_small p1 _ _ (fun _ => one_lt_exp_one) _
  tailComp _ _ _ _ _ _ := tailLogBound_of_small _ _ _ (fun _ => one_lt_exp_one) _
end Inhabitant
end
end GroundTheory.Heights₂.Heights.AnalyticLimit


