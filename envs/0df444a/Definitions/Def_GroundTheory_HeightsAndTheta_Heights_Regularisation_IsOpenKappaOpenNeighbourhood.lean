-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_IsOpenKappaOpenNeighbourhood
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:02.368385+00:00
-- url     : https://prove2.me/theorems/07f22dfc-0908-5b48-b9c8-69d182455373
-- title:
--   Is Open Kappa Open Neighbourhood
-- statement:
--   Definitions and structural lemmas for Is Open Kappa Open Neighbourhood, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsOpenKappaOpenNeighbourhood.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_chart
import Theorems.Thm_ReciprocityTheory_AnForm_M_hasDerivAt_fubiniStudyProfile
import Theorems.Thm_ReciprocityTheory_AnForm_M_hasDerivAt_fubiniStudyProfileInv
import Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_const
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_analyticAt_apply_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isCompatibleChart
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_isSmoothPotential
import Theorems.Thm_ReciprocityTheory_AnForm_M_projLine_leviForm_radial
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (polyMax Mollifier molli regMax coordDiv)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart maMeasure)
noncomputable section
def MaxOscillation.Statement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (δ C₁ t : ℝ),
    IsOpen U → ReciprocityTheory.AnForm.A.IsPsh U u → closedBall z δ ⊆ U → 1 ≤ C₁ → 0 < t → C₁ * t < δ →
    polyMax u z (C₁ * t) - polyMax u z (t / (4 * C₁)) ≤
      Real.log (4 * C₁ ^ 2) * (polyMax u z δ - polyMax u z (C₁ * t)) / Real.log (δ / (C₁ * t))
def MollifierLowerBound.Statement : Prop :=
  ∀ (D : ℕ) (ρ : Mollifier D) (B : ℝ), (∀ w, ρ.toFun w ≤ B) →
    ∀ (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ),
      IsOpen U → ReciprocityTheory.AnForm.A.IsPsh U u → 0 < t → closedBall z (2 * t) ⊆ U →
      polyMax u z (2 * t) - Real.pi ^ D * (3 / 2) ^ (2 * D) * B *
          (polyMax u z (2 * t) - polyMax u z (t / 4)) ≤ molli ρ t u z
def ell (t : ℝ) : ℝ := Real.log t⁻¹
def errE (C t : ℝ) : ℝ := C * Real.log (ell t) / ell t
def errorWithLinear (C t : ℝ) : ℝ := errE C t + C * t
variable {D : ℕ} {X : Type*} [TopologicalSpace X]
def DdcGeOn (A : FinHolAtlas D X) (V : Set X) (f : X → ℝ) (P : LocPot X) (c : ℝ) : Prop :=
  ∀ x ∈ V, ∀ k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (V ∩ P.U x), ∀ w : Fin D → ℂ,
    c * levi (P.φ x ∘ (A.chart k).symm) y w ≤ levi (f ∘ (A.chart k).symm) y w
def ThGe (A : FinHolAtlas D X) (θ : LocPot X) (f : X → ℝ) (om : LocPot X) (c : ℝ) : Prop :=
  ∀ x k, ∀ y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (θ.U x ∩ om.U x), ∀ w : Fin D → ℂ,
    c * levi (om.φ x ∘ (A.chart k).symm) y w ≤
      levi ((fun z => θ.φ x z + f z) ∘ (A.chart k).symm) y w
structure RegCharts (A : FinHolAtlas D X) where

  n : ℕ

  ψ : Fin n → OpenPartialHomeomorph X (Fin D → ℂ)
  compat : ∀ j, IsCompatChart A (ψ j)

  W : Fin n → Set (Fin D → ℂ)

  W' : Fin n → Set (Fin D → ℂ)

  W'' : Fin n → Set (Fin D → ℂ)
  isOpen_kappaOpenNeighbourhood : ∀ j, IsOpen (W j)
  isOpen_alt : ∀ j, IsOpen (W' j)
  isOpen_alt_alt : ∀ j, IsOpen (W'' j)
  W_subset : ∀ j, W j ⊆ (ψ j).target
  isCompact_closure_middle : ∀ j, IsCompact (closure (W' j))
  closure_W'_subset : ∀ j, closure (W' j) ⊆ W j
  closure_W''_subset : ∀ j, closure (W'' j) ⊆ W' j
  cover : ∀ x, ∃ j, x ∈ (ψ j).source ∧ ψ j x ∈ W'' j

  θ : LocPot X
  θ_pot : IsPotential A θ

  om : LocPot X
  om_pot : IsPotential A om
  om_pos : IsPosPot A om

  q : Fin n → (Fin D → ℂ) → ℝ
  q_smooth : ∀ j, ContDiffOn ℝ ∞ (q j) (W j)
  q_θ : ∀ j, ∀ y ∈ (ψ j).source, ψ j y ∈ W j → ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ ∃ G : X → ℂ,
    A.HoloOn V G ∧ ∀ x ∈ V ∩ θ.U y ∩ (ψ j).source, ψ j x ∈ W j →
      θ.φ y x - q j (ψ j x) = (G x).re
namespace RegCharts
variable {A : FinHolAtlas D X} (R : RegCharts A)
def V' (j : Fin R.n) : Set X := (R.ψ j).source ∩ R.ψ j ⁻¹' R.W' j
def V'' (j : Fin R.n) : Set X := (R.ψ j).source ∩ R.ψ j ⁻¹' R.W'' j
def u (φ : X → ℝ) (j : Fin R.n) (z : Fin D → ℂ) : ℝ := R.q j z + φ ((R.ψ j).symm z)
def phChart (φ : X → ℝ) (ρ : Mollifier D) (t : ℝ) (j : Fin R.n) (x : X) : ℝ :=
  molli ρ t (R.u φ j) (R.ψ j x) - R.q j (R.ψ j x)
def IsCutoffFamily (C : ℝ) (η : Fin R.n → X → ℝ) : Prop :=
  ∀ j, A.SmoothOn (R.V' j) (η j) ∧ (∀ x ∈ R.V' j, -1 ≤ η j x ∧ η j x ≤ 0) ∧
    (∀ x ∈ R.V'' j, η j x = 0) ∧
    (∃ K : Set (Fin D → ℂ), IsCompact K ∧ K ⊆ R.W' j ∧ ∀ x ∈ R.V' j, R.ψ j x ∉ K → η j x = -1) ∧
    DdcGeOn A (R.V' j) (η j) R.om (-C)
def regArg (φ : X → ℝ) (ρ : Mollifier D) (η : Fin R.n → X → ℝ) (C t : ℝ) (j : Fin R.n)
    (x : X) : ℝ :=
  R.phChart φ ρ t j x + 4 * errorWithLinear C t * η j x
open Classical in

def glued (φ : X → ℝ) (ρ : Mollifier D) (η : Fin R.n → X → ℝ) (C t : ℝ) (x : X) : ℝ :=
  haveI : Nonempty (Fin R.n) := ⟨(R.cover x).choose⟩
  regMax (errorWithLinear C t) (fun j => if x ∈ R.V' j then R.regArg φ ρ η C t j x
      else R.regArg φ ρ η C t (R.cover x).choose x - errorWithLinear C t) + errorWithLinear C t / 2
end RegCharts
structure RegChartData (A : FinHolAtlas D X) extends RegCharts A where

  Yo : Set X
  isOpen_Yo : IsOpen Yo

  S : Fin n → Finset (Fin D)
  mem_Yo_iff : ∀ j, ∀ z ∈ W j, (ψ j).symm z ∈ Yo ↔ z ∉ coordDiv (S j)

  r : X → ℝ

  f : Fin n → (Fin D → ℂ) → ℝ
  f_cont : ∀ j, ContinuousOn (f j) (W j)
  f_bdd : ∀ j, ∃ B, ∀ z ∈ W j, |f j z| ≤ B
  r_chart : ∀ j, ∀ z ∈ W j \ coordDiv (S j),
    r ((ψ j).symm z) = Real.exp 1 + f j z - ∑ i ∈ S j, Real.log (‖z i‖ ^ 2)
  one_le_r : ∀ x ∈ Yo, 1 ≤ r x

  φ : X → ℝ
  φ_smooth : A.SmoothOn Yo φ
  psh : ∀ j, ReciprocityTheory.AnForm.A.IsPsh (W j \ coordDiv (S j)) (toRegCharts.u φ j)

  C : ℝ
  φ_le : ∀ x ∈ Yo, φ x ≤ C
  le_φ : ∀ x ∈ Yo, -(C * Real.log (r x)) ≤ φ x
  grad : ∀ j, ∀ z ∈ W j \ coordDiv (S j),
    ‖fderiv ℝ (toRegCharts.u φ j) z‖ ≤
      C * r ((ψ j).symm z) ^ C * Real.exp (r ((ψ j).symm z) / 2)
structure BoundedThPsh {A : FinHolAtlas D X} (R : RegCharts A) where

  φ : X → ℝ
  bdd : ∃ B, ∀ x, |φ x| ≤ B
  psh : ∀ j, ReciprocityTheory.AnForm.A.IsPsh (R.W j) (R.u φ j)
def ChartComparison.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D), ∃ C t₀ : ℝ, 0 < t₀ ∧
      ∀ t, 0 < t → t < t₀ → ∀ j k (x : X), x ∈ R.V' j → x ∈ R.V' k →
        |R.phChart R.φ ρ t j x - R.phChart R.φ ρ t k x| ≤ errorWithLinear C t
def Cutoffs.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegCharts A), ∃ (C : ℝ) (η : Fin R.n → X → ℝ), R.IsCutoffFamily C η
def GlueRegularised.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (Cη : ℝ) (η : Fin R.n → X → ℝ),
    R.IsCutoffFamily Cη η → ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      A.Smooth (R.glued R.φ ρ η C t) ∧
        ThGe A R.θ (R.glued R.φ ρ η C t) R.om (-(4 * Cη * errorWithLinear C t))
def LemmaS4'.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ C ℓ₀ : ℝ, ∀ t, 0 < t → ℓ₀ ≤ ell t → ∃ φt : X → ℝ,
      A.Smooth φt ∧ (∀ x ∈ R.Yo, R.φ x ≤ φt x) ∧ (∀ x, φt x ≤ C) ∧
      (∀ x, -(C * Real.log (ell t)) ≤ φt x) ∧ ThGe A R.θ φt R.om (-errE C t) ∧
      (∀ x ∈ R.Yo, R.r x ≤ ell t → φt x ≤ R.φ x + t ^ (1 / 3 : ℝ) + errE C t) ∧
      (∀ x ∈ R.Yo, φt x ≤ R.φ x + t ^ (1 / 3 : ℝ) + errE C t * R.r x)
def BoundedRegularisationLemma.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegCharts A) (P : BoundedThPsh R),
    ∃ (C t₀ : ℝ) (φt : ℝ → X → ℝ), 0 < t₀ ∧
      (∀ t, 0 < t → t < t₀ → A.Smooth (φt t) ∧ (∀ x, P.φ x ≤ φt t x ∧ φt t x ≤ C) ∧
        ThGe A R.θ (φt t) R.om (-(C / ell t)) ∧
        Integrable (fun x => φt t x - P.φ x) (maMeasure A (fun _ : Fin D => R.om))) ∧
      Tendsto (fun t => ∫ x, |φt t x - P.φ x| ∂(maMeasure A (fun _ : Fin D => R.om)))
        (𝓝[>] 0) (𝓝 0) ∧
      ∀ x, ContinuousAt P.φ x → Tendsto (fun t => φt t x) (𝓝[>] 0) (𝓝 (P.φ x))
def siegel (g : ℕ) : Set (Matrix (Fin g) (Fin g) ℂ) :=
  {Z | Zᵀ = Z ∧ (Z.map Complex.im).PosDef}
def openPart (n a : ℕ) : Set (Fin n → ℂ) :=
  {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, (i : ℕ) < a → z i ≠ 0}
def coverSet (n a : ℕ) : Set (Fin n → ℂ) :=
  {w | ∀ i : Fin n, ((i : ℕ) < a → (w i).re < 0) ∧ (a ≤ (i : ℕ) → ‖w i‖ < 1)}
def expCov {n : ℕ} (a : ℕ) (w : Fin n → ℂ) : Fin n → ℂ :=
  fun i => if (i : ℕ) < a then Complex.exp (w i) else w i
def logCov {n : ℕ} (a : ℕ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => if (i : ℕ) < a then Complex.log (z i) else z i
def rPer {n : ℕ} (a : ℕ) (z : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < a), Real.log (‖z i‖ ^ 2)⁻¹
structure PeriodPolydisc (n a g : ℕ) where
  le : a ≤ n

  τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  holo : ∀ p q, AnalyticOnNhd ℂ (fun w => τ w p q) (coverSet n a)
  mem_siegel : ∀ w ∈ coverSet n a, τ w ∈ siegel g

  B : Fin n → Matrix (Fin g) (Fin g) ℤ
  B_symm : ∀ i, (B i)ᵀ = B i
  B_zero : ∀ i : Fin n, a ≤ (i : ℕ) → B i = 0
  period : ∀ i : Fin n, (i : ℕ) < a → ∀ w ∈ coverSet n a,
    τ (w + Pi.single i (2 * Real.pi * Complex.I)) = τ w + (B i).map (fun m : ℤ => (m : ℂ))
namespace PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)
def Bc (i : Fin n) : Matrix (Fin g) (Fin g) ℂ := (P.B i).map (fun m : ℤ => (m : ℂ))
def Br (i : Fin n) : Matrix (Fin g) (Fin g) ℝ := (P.B i).map (fun m : ℤ => (m : ℝ))
def tau0Cov (w : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  P.τ w - ∑ i, (w i / (2 * Real.pi * Complex.I)) • P.Bc i
def Hmat (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  ((P.τ (logCov a z)).map Complex.im)⁻¹
end PeriodPolydisc
def ExpExtension.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g) (v : Fin g → ℤ),
    (∀ i, 0 ≤ v ⬝ᵥ (P.B i *ᵥ v)) ∧
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ u (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin n → ℂ) 1, u z ≠ 0) ∧
      ∀ w ∈ coverSet n a,
        Complex.exp (2 * Real.pi * Complex.I *
            ((fun k => (v k : ℂ)) ⬝ᵥ (P.τ w *ᵥ fun k => (v k : ℂ)))) =
          (∏ i, expCov a w i ^ (v ⬝ᵥ (P.B i *ᵥ v)).toNat) * u (expCov a w)
def Tau0Holomorphic.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g), ∃ τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ,
    (∀ p q, AnalyticOnNhd ℂ (fun z => τ₀ z p q) (ball 0 1)) ∧
    (∀ w ∈ coverSet n a, τ₀ (expCov a w) = P.tau0Cov w) ∧ ∀ i, (P.Br i).PosSemidef
def KernelPositive.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ),
    (∀ p q, AnalyticOnNhd ℂ (fun z => τ₀ z p q) (ball 0 1)) →
    (∀ w ∈ coverSet n a, τ₀ (expCov a w) = P.tau0Cov w) →
    ∀ v : Fin g → ℝ, v ≠ 0 → (∀ i, P.Br i *ᵥ v = 0) →
      ∀ z ∈ ball (0 : Fin n → ℂ) 1, 0 < v ⬝ᵥ ((τ₀ z).map Complex.im *ᵥ v)
def ImTauBounds.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g), ∃ ρ₀ c C : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ 0 < c ∧
    ∀ w ∈ coverSet n a, expCov a w ∈ closedBall (0 : Fin n → ℂ) ρ₀ →
      ((P.τ w).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef ∧
      ((C * rPer a (expCov a w)) • (1 : Matrix (Fin g) (Fin g) ℝ) -
        (P.τ w).map Complex.im).PosSemidef
def HodgeDerivative.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g), ∃ ρ₀ C : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
    (∀ z ∈ openPart n a ∩ closedBall 0 ρ₀, ∀ p q : Fin g,
      ‖fderiv ℝ (fun y => P.Hmat y p q) z‖ ≤
          C * (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < a), ‖z i‖⁻¹) ∧
        ‖fderiv ℝ (fun y => P.Hmat y p q) z‖ ≤ C * Real.exp (rPer a z / 2)) ∧
    ∀ (m : ℕ) (F : (Fin n → ℂ) → Matrix (Fin g) (Fin m) ℂ),
      (∀ p q, AnalyticOnNhd ℂ (fun z => F z p q) (ball 0 1)) →
      (∀ z ∈ ball (0 : Fin n → ℂ) 1, (F z).rank = m) →
      ∃ C' : ℝ, ∀ z ∈ openPart n a ∩ closedBall 0 ρ₀,
        ‖fderiv ℝ (fun y => Real.log
            ((F y)ᴴ * (P.Hmat y).map (fun x : ℝ => (x : ℂ)) * F y).det.re) z‖ ≤
          C' * rPer a z ^ C' * Real.exp (rPer a z / 2)
theorem im_mul_inv_two_pi_I (x : ℝ) (w : ℂ) :
    ((x : ℂ) * (2 * Real.pi * Complex.I)⁻¹ * w).im = -x * w.re / (2 * Real.pi) := by
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  simp [Complex.mul_im, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]
  field_simp
def diagPeriod (g : ℕ) (d : Fin g → ℕ) : PeriodPolydisc 1 1 g where
  le := le_rfl
  τ w := diagonal (fun k => (d k : ℂ) * (2 * Real.pi * Complex.I)⁻¹ * w 0 + Complex.I)
  holo p q := by
    intro w _
    by_cases hpq : p = q
    · subst hpq
      simp only [diagonal_apply_eq]
      exact (analyticAt_const.mul (ReciprocityTheory.AnForm.M.projLine_analyticAt_apply_zero w)).add analyticAt_const
    · simp only [diagonal_apply_ne _ hpq]
      exact analyticAt_const
  mem_siegel w hw := by
    refine ⟨diagonal_transpose _, ?_⟩
    rw [diagonal_map (by simp), posDef_diagonal_iff]
    intro k
    have hre : (w 0).re < 0 := ((hw 0).1 (by simp))
    simp only [Complex.add_im, Complex.I_im]
    have h1 := im_mul_inv_two_pi_I (d k : ℝ) (w 0)
    push_cast at h1
    rw [h1]
    have : 0 ≤ (d k : ℝ) * (-(w 0).re) / (2 * Real.pi) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by positivity)
    have e : -(d k : ℝ) * (w 0).re / (2 * Real.pi) = (d k : ℝ) * (-(w 0).re) / (2 * Real.pi) := by
      ring
    linarith
  B _ := diagonal (fun k => (d k : ℤ))
  B_symm _ := diagonal_transpose _
  B_zero i hi := absurd i.isLt (by omega)
  period i hi w _ := by
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst hi0
    rw [diagonal_map (by simp)]
    ext p q
    simp only [Matrix.add_apply, diagonal_apply, Pi.add_apply, Pi.single_eq_same]
    split_ifs
    · have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      rw [mul_add, mul_assoc (d p : ℂ) _ (2 * Real.pi * Complex.I : ℂ), inv_mul_cancel₀ hπ]
      push_cast
      ring
    · simp
def periodGenusOne : PeriodPolydisc 1 1 1 := diagPeriod 1 ![1]
def periodGenusTwo : PeriodPolydisc 1 1 2 := diagPeriod 2 ![1, 0]
section ProjectiveLine
open ReciprocityTheory.AnForm.M
theorem projLine_chart_target (j : Fin 2) : (p1.chart j).target = Set.univ := by
  fin_cases j <;> rfl
theorem norm_fin_one_eq_alt (y : Fin 1 → ℂ) : ‖y‖ = ‖y 0‖ := by
  have h : y = fun _ => y 0 := funext fun i => by fin_cases i; rfl
  conv_lhs => rw [h]
  exact pi_norm_const _
def crdj (j : Fin 2) : OnePoint ℂ → ℂ := ![crd0, crd1] j
theorem projLine_chart_apply (j : Fin 2) (x : OnePoint ℂ) : p1.chart j x = fun _ => crdj j x := by
  fin_cases j <;> rfl
theorem levi_fsPot (x : OnePoint ℂ) (k : Fin 2) (y : Fin 1 → ℂ)
    (hy : y ∈ (p1.chart k).target ∩ (p1.chart k).symm ⁻¹' fsPot.U x) (v : Fin 1 → ℂ) :
    levi (fsPot.φ x ∘ (p1.chart k).symm) y v = (2 * (1 + ‖y 0‖ ^ 2) ^ 2)⁻¹ * ‖v 0‖ ^ 2 := by
  have ht : 0 ≤ ‖y 0‖ ^ 2 := by positivity
  rcases fsPot_chart x k with h | ⟨h, hs⟩
  · rw [h]
    show levi (fun w : Fin 1 → ℂ => fubiniStudyProfile (‖w 0‖ ^ 2)) y v = _
    have h0 : (1 : ℝ) + ‖y 0‖ ^ 2 ≠ 0 := ne_of_gt (by linarith)
    rw [projLine_leviForm_radial (G := fubiniStudyProfile) (G' := fun t => (1 / 2) * (1 + t)⁻¹)
      (G'' := 1 / 2 * (-1 / (1 + ‖y 0‖ ^ 2) ^ 2)) (Filter.Eventually.of_forall fun w => rfl) ?_
      (((((hasDerivAt_id _).const_add 1).inv h0).const_mul (1 / 2)).congr_deriv (by simp)) v]
    · congr 1
      field_simp
      ring
    · filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < ‖y 0‖ ^ 2 by linarith)] with t ht'
      exact hasDerivAt_fubiniStudyProfile ht'
  · rw [h]
    show levi (fun w : Fin 1 → ℂ => fubiniStudyProfileInv (‖w 0‖ ^ 2)) y v = _
    have hy0 : y 0 ≠ 0 := hs y hy
    have htp : 0 < ‖y 0‖ ^ 2 := by have := norm_pos_iff.2 hy0; positivity
    have h0 : ‖y 0‖ ^ 2 * (‖y 0‖ ^ 2 + 1) ≠ 0 := ne_of_gt (by positivity)
    rw [projLine_leviForm_radial (G := fubiniStudyProfileInv) (G' := fun t => -(1 / 2) * (t * (t + 1))⁻¹)
      (G'' := -(1 / 2) * (-(1 * (‖y 0‖ ^ 2 + 1) + ‖y 0‖ ^ 2 * 1) /
        (‖y 0‖ ^ 2 * (‖y 0‖ ^ 2 + 1)) ^ 2))
      (Filter.Eventually.of_forall fun w => rfl) ?_
      (((((hasDerivAt_id _).mul ((hasDerivAt_id _).add_const 1)).inv h0).const_mul
        (-(1 / 2))).congr_deriv (by simp)) v]
    · congr 1
      field_simp
      ring
    · filter_upwards [Ioi_mem_nhds htp] with t ht'
      exact hasDerivAt_fubiniStudyProfileInv ht'
theorem projLine_fubiniStudy_isPosPot : IsPosPot p1 fsPot := by
  intro x j y hy v hv
  rw [levi_fsPot x j y hy v]
  have h0 : v 0 ≠ 0 := fun h => hv (funext fun i => by fin_cases i; exact h)
  have : 0 < ‖v 0‖ := norm_pos_iff.2 h0
  positivity
def cutG (s : ℝ) : ℝ := -Real.smoothTransition ((s - 25 / 16) * (64 / 21))
def cutoffDeriv : ℝ → ℝ := deriv cutG
def cutoffSecondDeriv : ℝ → ℝ := deriv cutoffDeriv
def projLineCutoff (j : Fin 2) (x : OnePoint ℂ) : ℝ := cutG (‖crdj j x‖ ^ 2)
@[reducible] def projLineCharts : RegCharts p1 where
  n := 2
  ψ := p1.chart
  compat := projLine_isCompatibleChart
  W _ := ball 0 2
  W' _ := ball 0 (3 / 2)
  W'' _ := ball 0 (5 / 4)
  isOpen_kappaOpenNeighbourhood _ := isOpen_ball
  isOpen_alt _ := isOpen_ball
  isOpen_alt_alt _ := isOpen_ball
  W_subset j := by rw [projLine_chart_target]; exact Set.subset_univ _
  isCompact_closure_middle _ := by
    rw [closure_ball _ (by norm_num)]; exact isCompact_closedBall _ _
  closure_W'_subset _ := closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num))
  closure_W''_subset _ :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num))
  cover x := by
    induction x with
    | infty =>
      refine ⟨1, show (OnePoint.infty : OnePoint ℂ) ∈ projectiveLineChartAtInfinity.source from OnePoint.infty_ne_coe 0, ?_⟩
      rw [projLine_chart_apply, mem_ball_zero_iff, norm_fin_one_eq_alt]
      show ‖(0 : ℂ)‖ < 5 / 4
      norm_num
    | coe z =>
      by_cases hz : ‖z‖ ≤ 1
      · refine ⟨0, ⟨z, rfl⟩, ?_⟩
        rw [projLine_chart_apply, mem_ball_zero_iff, norm_fin_one_eq_alt]
        show ‖z‖ < 5 / 4
        linarith
      · have hz0 : z ≠ 0 := by rintro rfl; simp at hz
        refine ⟨1, show (z : OnePoint ℂ) ∈ projectiveLineChartAtInfinity.source from
          fun h => hz0 (OnePoint.coe_injective h), ?_⟩
        rw [projLine_chart_apply, mem_ball_zero_iff, norm_fin_one_eq_alt]
        show ‖z⁻¹‖ < 5 / 4
        rw [norm_inv]
        have h1 : 1 < ‖z‖ := lt_of_not_ge hz
        have h2 : ‖z‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
        linarith
  θ := LocPot.ofFun 0
  θ_pot := isPotential_ofFun p1 0 (fun _ => contDiffOn_const)
  om := fsPot
  om_pot := projLine_isSmoothPotential
  om_pos := projLine_fubiniStudy_isPosPot
  q _ _ := 0
  q_smooth _ := contDiffOn_const
  q_θ _ _ _ _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, holoOn_const _ 0,
    fun x _ _ => by simp [LocPot.ofFun]⟩
theorem isPsh_const (U : Set (Fin D → ℂ)) (c : ℝ) : ReciprocityTheory.AnForm.A.IsPsh U (fun _ => c) :=
  ⟨continuousOn_const.upperSemicontinuousOn,
    fun _ _ _ => ⟨circleIntegrable_const c 0 1, (Real.circleAverage_const c 0 1).ge⟩⟩
theorem projLineCharts_potential_zero (j : Fin 2) : projLineCharts.u (fun _ => 0) j = fun _ => (0 : ℝ) :=
  funext fun z => by simp [RegCharts.u]
open Classical in

def projLineChartData : RegChartData p1 where
  toRegCharts := projLineCharts
  Yo := {(OnePoint.infty : OnePoint ℂ)}ᶜ
  isOpen_Yo := isOpen_compl_singleton
  S := ![∅, {0}]
  mem_Yo_iff j z _ := by
    fin_cases j
    · show ((z 0 : ℂ) : OnePoint ℂ) ∈ ({OnePoint.infty}ᶜ : Set (OnePoint ℂ)) ↔ z ∉ coordDiv ∅
      simp [coordDiv]
    · show projectiveLineChartAtInfinity.symm z ∈ ({OnePoint.infty}ᶜ : Set (OnePoint ℂ)) ↔ z ∉ coordDiv {0}
      rw [Set.mem_compl_singleton_iff, OnePoint.ne_infty_iff_exists, ← Set.mem_range,
        projLineChart1_symm_mem_range]
      simp [coordDiv]
  r x := if x = (OnePoint.infty : OnePoint ℂ) then 1 else Real.exp 1 + Real.log (1 + ‖crd0 x‖ ^ 2)
  f _ z := Real.log (1 + ‖z 0‖ ^ 2)
  f_cont _ := (Continuous.log (by fun_prop) (fun z => by positivity)).continuousOn
  f_bdd _ := ⟨4, fun z hz => by
    have hz' : ‖z 0‖ < 2 := lt_of_le_of_lt (norm_le_pi_norm z 0) (mem_ball_zero_iff.1 hz)
    have h0 : 0 ≤ Real.log (1 + ‖z 0‖ ^ 2) := Real.log_nonneg (by nlinarith [norm_nonneg (z 0)])
    have h1 : Real.log (1 + ‖z 0‖ ^ 2) ≤ 1 + ‖z 0‖ ^ 2 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [abs_of_nonneg h0]
    nlinarith [norm_nonneg (z 0)]⟩
  r_chart j z hz := by
    fin_cases j
    · show (if ((z 0 : ℂ) : OnePoint ℂ) = OnePoint.infty then (1 : ℝ) else
          Real.exp 1 + Real.log (1 + ‖crd0 ((z 0 : ℂ) : OnePoint ℂ)‖ ^ 2)) =
        Real.exp 1 + Real.log (1 + ‖z 0‖ ^ 2) - ∑ i ∈ (∅ : Finset (Fin 1)), Real.log (‖z i‖ ^ 2)
      rw [if_neg (OnePoint.coe_ne_infty _)]
      simp [crd0]
    · have hz0 : z 0 ≠ 0 := fun h => hz.2 ⟨0, Finset.mem_singleton_self 0, h⟩
      have hne : projectiveLineChartAtInfinity.symm z ≠ OnePoint.infty := by
        rw [OnePoint.ne_infty_iff_exists, ← Set.mem_range, projLineChart1_symm_mem_range]
        exact hz0
      show (if projectiveLineChartAtInfinity.symm z = OnePoint.infty then (1 : ℝ) else
          Real.exp 1 + Real.log (1 + ‖crd0 (projectiveLineChartAtInfinity.symm z)‖ ^ 2)) =
        Real.exp 1 + Real.log (1 + ‖z 0‖ ^ 2) - ∑ i ∈ ({0} : Finset (Fin 1)), Real.log (‖z i‖ ^ 2)
      rw [if_neg hne, finiteCoord_projLineChart1_symm, Finset.sum_singleton, norm_inv, inv_pow]
      have ha : 0 < ‖z 0‖ ^ 2 := by have := norm_pos_iff.2 hz0; positivity
      have e : 1 + (‖z 0‖ ^ 2)⁻¹ = (1 + ‖z 0‖ ^ 2) / ‖z 0‖ ^ 2 := by field_simp; ring
      rw [e, Real.log_div (by positivity) ha.ne']
      ring
  one_le_r x hx := by
    have hx' : x ≠ OnePoint.infty := hx
    show 1 ≤ (if x = OnePoint.infty then (1 : ℝ) else Real.exp 1 + Real.log (1 + ‖crd0 x‖ ^ 2))
    rw [if_neg hx']
    have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : 0 ≤ Real.log (1 + ‖crd0 x‖ ^ 2) := Real.log_nonneg (by nlinarith [norm_nonneg (crd0 x)])
    linarith
  φ _ := 0
  φ_smooth _ := contDiffOn_const
  psh j := by
    show ReciprocityTheory.AnForm.A.IsPsh _ (projLineCharts.u (fun _ => 0) j)
    rw [projLineCharts_potential_zero]
    exact isPsh_const _ 0
  C := 0
  φ_le _ _ := le_rfl
  le_φ _ _ := by simp
  grad j z _ := by
    show ‖fderiv ℝ (projLineCharts.u (fun _ => 0) j) z‖ ≤ _
    rw [projLineCharts_potential_zero]
    simp
def projLineBoundedPotential : BoundedThPsh projLineCharts where
  φ _ := 0
  bdd := ⟨0, fun _ => by simp⟩
  psh j := by
    rw [projLineCharts_potential_zero]
    exact isPsh_const _ 0
end ProjectiveLine
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular


