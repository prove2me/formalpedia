-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:56.691+00:00
-- url     : https://prove2.me/theorems/ef875b90-7ce6-42d4-87dc-1f0fb5036e08
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/Statements.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Matrix
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
def PolyMaxOscillation.Statement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (δ t C₁ : ℝ),
    IsOpen U → IsPsh U u → closedBall z δ ⊆ U → 0 < t → 1 ≤ C₁ → C₁ * t < δ →
    polyMax u z (C₁ * t) - polyMax u z (t / (4 * C₁)) ≤
      Real.log (4 * C₁ ^ 2) * (polyMax u z δ - polyMax u z (C₁ * t)) / Real.log (δ / (C₁ * t))
def MollifiedLowerBound.Statement : Prop :=
  ∀ (D : ℕ) (ρ : Mollifier D) (b : ℝ) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ)
    (z : Fin D → ℂ) (t : ℝ),
    IsOpen U → IsPsh U u → 0 < t → closedBall z (2 * t) ⊆ U → (∀ w, ρ.toFun w ≤ b) →
    polyMax u z (2 * t) -
        Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b * (polyMax u z (2 * t) - polyMax u z (t / 4)) ≤
      molli ρ t u z
structure PotentialCharts {D : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas D X) where

  N : ℕ

  chart : Fin N → OpenPartialHomeomorph X (Fin D → ℂ)
  compat : ∀ j, IsCompatChart A (chart j)
  target_subset : ∀ j, (chart j).target ⊆ ball 0 1

  mid : Fin N → Set X

  inner : Fin N → Set X
  isOpen_mid : ∀ j, IsOpen (mid j)
  isOpen_inner : ∀ j, IsOpen (inner j)
  closure_inner : ∀ j, closure (inner j) ⊆ mid j
  closure_mid : ∀ j, closure (mid j) ⊆ (chart j).source
  cover : ∀ x, ∃ j, x ∈ inner j

  th : LocPot X
  th_pot : IsPotential A th

  q : Fin N → (Fin D → ℂ) → ℝ
  q_smooth : ∀ j, ContDiffOn ℝ ∞ (q j) (chart j).target
  q_th : ∀ (j : Fin N) (x : X), ∀ y ∈ th.U x ∩ (chart j).source, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧
    ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W ∩ th.U x ∩ (chart j).source, q j (chart j z) - th.φ x z = (G z).re
namespace PotentialCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)
theorem inner_subset_mid (j : Fin P.N) : P.inner j ⊆ P.mid j :=
  subset_closure.trans (P.closure_inner j)
def chartFun (ψ : X → ℝ) (j : Fin P.N) (y : Fin D → ℂ) : ℝ :=
  P.q j y + ψ ((P.chart j).symm y)
def chartMid (j : Fin P.N) : Set (Fin D → ℂ) :=
  (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
instance midNonempty (x : X) : Nonempty {j // x ∈ P.mid j} :=
  ⟨⟨(P.cover x).choose, P.inner_subset_mid _ (P.cover x).choose_spec⟩⟩
open Classical in

def glue (a : Fin P.N → X → ℝ) (ε : ℝ) (x : X) : ℝ :=
  regMax ε (fun j : {j // x ∈ P.mid j} => a j x) + ε / 2
structure IsCutoffFamily (η : Fin P.N → X → ℝ) (Cη : ℝ) : Prop where
  smooth : ∀ j, A.SmoothOn (P.mid j) (η j)
  bounds : ∀ j, ∀ x ∈ P.mid j, -1 ≤ η j x ∧ η j x ≤ 0
  eq_zero : ∀ j, ∀ x ∈ P.inner j, η j x = 0
  eq_neg_one : ∀ j, ∃ L : Set X, IsClosed L ∧ L ⊆ P.mid j ∧ ∀ x ∈ P.mid j \ L, η j x = -1
  levi_ge : ∀ j k, ∀ x ∈ P.mid j ∩ P.mid k, ∀ w : Fin D → ℂ,
    -Cη * ‖w‖ ^ 2 ≤ levi (η j ∘ (P.chart k).symm) (P.chart k x) w
end PotentialCharts
structure RegChartData {D : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas D X)
    extends PotentialCharts A where

  S : Fin N → Finset (Fin D)

  Yo : Set X
  mem_Yo : ∀ j, ∀ x ∈ (chart j).source, x ∈ Yo ↔ chart j x ∉ coordDiv (S j)

  ph : X → ℝ
  ph_smooth : A.SmoothOn Yo ph
  u_psh : ∀ j, IsPsh ((chart j).target \ coordDiv (S j)) (fun y => q j y + ph ((chart j).symm y))

  r : X → ℝ
  one_le_r : ∀ x ∈ Yo, 1 ≤ r x

  f : Fin N → (Fin D → ℂ) → ℝ
  f_smooth : ∀ j, ContDiffOn ℝ ∞ (f j) (chart j).target
  f_bdd : ∃ B : ℝ, ∀ j, ∀ y ∈ (chart j).target, |f j y| ≤ B
  r_chart : ∀ j, ∀ y ∈ (chart j).target \ coordDiv (S j),
    r ((chart j).symm y) = Real.exp 1 + f j y + ∑ i ∈ S j, Real.log (‖y i‖ ^ 2)⁻¹
  Clog : ℝ
  Cph : ℝ
  ph_le : ∀ x ∈ Yo, ph x ≤ Cph
  ph_ge : ∀ x ∈ Yo, -Clog * Real.log (r x) ≤ ph x
  Cgrad : ℝ
  grad_le : ∀ j, ∀ y ∈ (chart j).target \ coordDiv (S j),
    ‖fderiv ℝ (fun y' => q j y' + ph ((chart j).symm y')) y‖ ≤
      Cgrad * r ((chart j).symm y) ^ Cgrad * Real.exp (r ((chart j).symm y) / 2)
structure BoundedPshData {D : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas D X)
    extends PotentialCharts A where
  ph : X → ℝ
  bdd : ∃ C : ℝ, ∀ x, |ph x| ≤ C
  u_psh : ∀ j, IsPsh (chart j).target (fun y => q j y + ph ((chart j).symm y))
namespace RegChartData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)
def u (j : Fin R.N) : (Fin D → ℂ) → ℝ := R.chartFun R.ph j
def trunc (K : ℝ) (j : Fin R.N) : (Fin D → ℂ) → ℝ :=
  limsupExt (R.chart j).target (coordDiv (R.S j)) (fun y => max (R.u j y) (-K))
def smoothed (ρ : Mollifier D) (K t : ℝ) (j : Fin R.N) : (Fin D → ℂ) → ℝ :=
  molli ρ t (R.trunc K j)
def phReg (ρ : Mollifier D) (K t : ℝ) (j : Fin R.N) (x : X) : ℝ :=
  R.smoothed ρ K t j (R.chart j x) - R.q j (R.chart j x)
def regularised (ρ : Mollifier D) (K t ε : ℝ) (η : Fin R.N → X → ℝ) : X → ℝ :=
  R.glue (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) ε
end RegChartData
def PolyMaxLowerBound.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∀ (K : ℝ) (j : Fin R.N), ∀ x ∈ R.mid j,
        -C * Real.log (Real.log t⁻¹) ≤ polyMax (R.trunc K j) (R.chart j x) t
def ChartComparison.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D), ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∀ K : ℝ, C * Real.log (Real.log t⁻¹) ≤ K → ∀ j k : Fin R.N, ∀ x ∈ R.mid j ∩ R.mid k,
        |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤
          C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ + C * t
def MollifiedNearSmooth.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D), ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∀ K : ℝ, C * Real.log (Real.log t⁻¹) ≤ K → ∀ j : Fin R.N, ∀ x ∈ R.mid j ∩ R.Yo,
        R.r x ≤ Real.log t⁻¹ →
        R.smoothed ρ K t j (R.chart j x) - R.u j (R.chart j x) ≤
          C * Real.log t⁻¹ ^ C * t ^ (1 / 2 : ℝ)
def CutoffsExist.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (P : PotentialCharts A), ∃ (η : Fin P.N → X → ℝ) (Cη : ℝ), P.IsCutoffFamily η Cη
def GlueRegularised.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (ρ : Mollifier D) (η : Fin R.N → X → ℝ) (Cη K t ε : ℝ),
    R.IsCutoffFamily η Cη → 0 < t → 0 < ε →
    (∀ j, ∀ x ∈ closure (R.mid j), closedBall (R.chart j x) t ⊆ (R.chart j).target) →
    (∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε) →
    A.Smooth (R.regularised ρ K t ε η) ∧
      ∀ k : Fin R.N, ∀ x ∈ R.mid k, ∀ w : Fin D → ℂ,
        -(4 * Cη * ε) * ‖w‖ ^ 2 ≤ levi (R.chartFun (R.regularised ρ K t ε η) k) (R.chart k x) w
def LogLogRegularisation.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ C ℓ₀ : ℝ, ∀ t : ℝ, 0 < t → ℓ₀ ≤ Real.log t⁻¹ →
      ∃ φt : X → ℝ, A.Smooth φt ∧
        (∀ x ∈ R.Yo, R.ph x ≤ φt x) ∧ (∀ x, φt x ≤ C) ∧
        (∀ x, -C * Real.log (Real.log t⁻¹) ≤ φt x) ∧
        (∀ k : Fin R.N, ∀ x ∈ R.mid k, ∀ w : Fin D → ℂ,
          -(C * Real.log (Real.log t⁻¹) / Real.log t⁻¹) * ‖w‖ ^ 2 ≤
            levi (R.chartFun φt k) (R.chart k x) w) ∧
        (∀ x ∈ R.Yo, R.r x ≤ Real.log t⁻¹ →
          φt x ≤ R.ph x + t ^ (1 / 3 : ℝ) + C * Real.log (Real.log t⁻¹) / Real.log t⁻¹) ∧
        (∀ x ∈ R.Yo,
          φt x ≤ R.ph x + t ^ (1 / 3 : ℝ) + C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ * R.r x)
def BoundedRegularisation.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (B : BoundedPshData A), ∃ (C t₀ : ℝ) (φt : ℝ → X → ℝ), 0 < t₀ ∧
      (∀ t : ℝ, 0 < t → t < t₀ → A.Smooth (φt t) ∧ (∀ x, B.ph x ≤ φt t x ∧ φt t x ≤ C) ∧
        ∀ k : Fin B.N, ∀ x ∈ B.mid k, ∀ w : Fin D → ℂ,
          -(C / Real.log t⁻¹) * ‖w‖ ^ 2 ≤ levi (B.chartFun (φt t) k) (B.chart k x) w) ∧
      (∀ k : Fin B.N,
        (∀ t : ℝ, 0 < t → t < t₀ → IntegrableOn
          (fun y => φt t ((B.chart k).symm y) - B.ph ((B.chart k).symm y)) (B.chartMid k)) ∧
        Tendsto (fun t => ∫ y in B.chartMid k, |φt t ((B.chart k).symm y) - B.ph ((B.chart k).symm y)|)
          (𝓝[>] 0) (𝓝 0)) ∧
      ∀ x, ContinuousAt B.ph x → Tendsto (fun t => φt t x) (𝓝[>] 0) (𝓝 (B.ph x))
def logCover {n a : ℕ} (h : a ≤ n) : Set (Fin n → ℂ) :=
  {w | (∀ i : Fin a, (w (Fin.castLE h i)).re < 0) ∧ ∀ k : Fin n, a ≤ k.val → ‖w k‖ < 1}
def expCover {n : ℕ} (a : ℕ) (w : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if k.val < a then Complex.exp (w k) else w k
def logLift {n : ℕ} (a : ℕ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if k.val < a then Complex.log (z k) else z k
def intQuad {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) : ℤ := v ⬝ᵥ B *ᵥ v
structure PeriodPolydisc (n a g : ℕ) where
  a_le : a ≤ n

  τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  analytic : ∀ p q, AnalyticOnNhd ℂ (fun w => τ w p q) (logCover a_le)
  symm : ∀ w ∈ logCover a_le, (τ w)ᵀ = τ w
  im_posDef : ∀ w ∈ logCover a_le, ((τ w).map Complex.im).PosDef

  B : Fin a → Matrix (Fin g) (Fin g) ℤ
  B_symm : ∀ i, (B i)ᵀ = B i
  periodic : ∀ (i : Fin a), ∀ w ∈ logCover a_le,
    τ (w + Pi.single (Fin.castLE a_le i) (2 * Real.pi * Complex.I)) =
      τ w + (B i).map (Int.cast : ℤ → ℂ)
namespace PeriodPolydisc
variable {n a g : ℕ} (P : PeriodPolydisc n a g)
def tau0 (w : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  P.τ w - ∑ i : Fin a, (w (Fin.castLE P.a_le i) / (2 * Real.pi * Complex.I)) •
    (P.B i).map (Int.cast : ℤ → ℂ)
def IsTau0Ext (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  (∀ p q, AnalyticOnNhd ℂ (fun z => T0 z p q) (ball 0 1)) ∧
    ∀ w ∈ logCover P.a_le, P.tau0 w = T0 (expCover a w)
def imTau (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (P.τ (logLift a z)).map Complex.im
def hodge (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ := (P.imTau z)⁻¹
end PeriodPolydisc
def ExpQuadMonomial.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g) (v : Fin g → ℤ),
    (∀ i, 0 ≤ intQuad (P.B i) v) ∧
    ∃ h : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ h (ball 0 1) ∧ (∀ z ∈ ball 0 1, h z ≠ 0) ∧
      ∀ w ∈ logCover P.a_le,
        Complex.exp (2 * Real.pi * Complex.I * ((fun k => (v k : ℂ)) ⬝ᵥ P.τ w *ᵥ fun k => (v k : ℂ))) =
          (∏ i : Fin a, expCover a w (Fin.castLE P.a_le i) ^ (intQuad (P.B i) v).toNat) *
            h (expCover a w)
def Tau0Holomorphic.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g),
    (∀ i, ((P.B i).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ ∃ T0, P.IsTau0Ext T0
def KernelPositive.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g) (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ),
    P.IsTau0Ext T0 → ∀ v : Fin g → ℝ, v ≠ 0 → (∀ i, (P.B i).map (Int.cast : ℤ → ℝ) *ᵥ v = 0) →
      ∀ z ∈ ball (0 : Fin n → ℂ) 1, 0 < v ⬝ᵥ ((T0 z).map Complex.im *ᵥ v)
def ImTauBounds.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g), ∃ ρ c C : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < c ∧
    ∀ w ∈ logCover P.a_le, expCover a w ∈ closedBall 0 ρ →
      ((P.τ w).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef ∧
      ((C * chartRadius P.a_le (expCover a w)) • (1 : Matrix (Fin g) (Fin g) ℝ) -
        (P.τ w).map Complex.im).PosSemidef
def HodgeDerivative.Statement : Prop :=
  ∀ (n a g : ℕ) (P : PeriodPolydisc n a g), ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
    (∃ C : ℝ, ∀ z ∈ closedBall (0 : Fin n → ℂ) ρ, z ∈ puncturedChart P.a_le (ball 0 1) →
      ∀ p q : Fin g, DifferentiableAt ℝ (fun y => P.hodge y p q) z ∧
        ‖fderiv ℝ (fun y => P.hodge y p q) z‖ ≤
          C * (1 + ∑ i, ‖cuspCoord P.a_le z i‖⁻¹) ∧
        ‖fderiv ℝ (fun y => P.hodge y p q) z‖ ≤ C * Real.exp (chartRadius P.a_le z / 2)) ∧
    ∀ (k : ℕ) (F : (Fin n → ℂ) → Matrix (Fin g) (Fin k) ℂ),
      (∀ p q, AnalyticOnNhd ℂ (fun z => F z p q) (ball 0 1)) →
      (∀ z ∈ ball (0 : Fin n → ℂ) 1, (F z).rank = k) →
      ∃ C : ℝ, ∀ z ∈ closedBall (0 : Fin n → ℂ) ρ, z ∈ puncturedChart P.a_le (ball 0 1) →
        DifferentiableAt ℝ (fun y => logDetGram (P.imTau y) (F y)) z ∧
        ‖fderiv ℝ (fun y => logDetGram (P.imTau y) (F y)) z‖ ≤
          C * chartRadius P.a_le z ^ C * (1 + ∑ i, ‖cuspCoord P.a_le z i‖⁻¹) ∧
        ‖fderiv ℝ (fun y => logDetGram (P.imTau y) (F y)) z‖ ≤
          C * chartRadius P.a_le z ^ C * Real.exp (chartRadius P.a_le z / 2)
section Inhabitants
theorem isPsh_const {D : ℕ} (U : Set (Fin D → ℂ)) (c : ℝ) : IsPsh U (fun _ => c) :=
  ⟨upperSemicontinuousOn_const, fun _ _ _ =>
    ⟨circleIntegrable_const _ _ _, by rw [Real.circleAverage_const]⟩⟩
def pointChart : OpenPartialHomeomorph Unit (Fin 0 → ℂ) :=
  (Homeomorph.homeomorphOfUnique Unit (Fin 0 → ℂ)).toOpenPartialHomeomorph
theorem analyticOnNhd_fin_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → (Fin 0 → ℂ)) (s : Set E) : AnalyticOnNhd ℂ f s := by
  have : f = fun _ => 0 := funext fun _ => Subsingleton.elim _ _
  rw [this]
  exact analyticOnNhd_const
def pointAtlas : FinHolAtlas 0 Unit where
  n := 1
  chart _ := pointChart
  cover _ := ⟨0, by simp [pointChart]⟩
  holo _ _ := analyticOnNhd_fin_zero _ _
theorem pointChart_compat : IsCompatChart pointAtlas pointChart :=
  fun _ => ⟨analyticOnNhd_fin_zero _ _, analyticOnNhd_fin_zero _ _⟩
theorem holoOn_zero {D : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas D X) (W : Set X) :
    A.HoloOn W (fun _ => (0 : ℂ)) :=
  fun _ => analyticOnNhd_const
def pointCharts : PotentialCharts pointAtlas where
  N := 1
  chart _ := pointChart
  compat _ := pointChart_compat
  target_subset _ y _ := by simp [Subsingleton.elim y 0]
  mid _ := Set.univ
  inner _ := Set.univ
  isOpen_mid _ := isOpen_univ
  isOpen_inner _ := isOpen_univ
  closure_inner _ := by simp
  closure_mid _ := by simp [pointChart]
  cover _ := ⟨0, Set.mem_univ _⟩
  th := LocPot.ofFun (fun _ => 0)
  th_pot := ReciprocityTheory.AnForm.M.isPotential_ofFun _ _ fun _ => contDiffOn_const
  q _ _ := 0
  q_smooth _ := contDiffOn_const
  q_th _ _ y _ := ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, holoOn_zero _ _,
    fun _ _ => by simp [LocPot.ofFun]⟩
def pointReg : RegChartData pointAtlas where
  toPotentialCharts := pointCharts
  S _ := ∅
  Yo := Set.univ
  mem_Yo _ _ _ := by simp [coordDiv]
  ph _ := 0
  ph_smooth _ := contDiffOn_const
  u_psh _ := by simpa [pointCharts] using isPsh_const _ (0 : ℝ)
  r _ := Real.exp 1
  one_le_r _ _ := by linarith [Real.add_one_le_exp (1 : ℝ)]
  f _ _ := 0
  f_smooth _ := contDiffOn_const
  f_bdd := ⟨0, fun _ _ _ => by simp⟩
  r_chart _ _ _ := by simp
  Clog := 0
  Cph := 0
  ph_le _ _ := le_rfl
  ph_ge _ _ := by simp
  Cgrad := 0
  grad_le _ _ _ := by simp [pointCharts]
def pointBounded : BoundedPshData pointAtlas where
  toPotentialCharts := pointCharts
  ph _ := 0
  bdd := ⟨0, fun _ => by simp⟩
  u_psh _ := by simpa [pointCharts] using isPsh_const _ (0 : ℝ)
theorem im_div_two_pi_I (z : ℂ) : (z / (2 * Real.pi * Complex.I)).im = -z.re / (2 * Real.pi) := by
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  simp [Complex.div_im, Complex.normSq_apply]
  field_simp
theorem analyticAt_coord_div_add {n : ℕ} (k : Fin n) (c d : ℂ) (w : Fin n → ℂ) :
    AnalyticAt ℂ (fun w : Fin n → ℂ => w k / c + d) w := by
  have h : (fun w : Fin n → ℂ => w k / c + d) =
      fun w => (c⁻¹ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k) w + d := by
    funext w
    simp [div_eq_inv_mul]
  rw [h]
  exact ((c⁻¹ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt w).add
    analyticAt_const
theorem two_pi_I_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  simp [Real.pi_ne_zero, Complex.I_ne_zero]
def periodOne : PeriodPolydisc 1 1 1 where
  a_le := le_rfl
  τ w := diagonal fun _ => w 0 / (2 * Real.pi * Complex.I) + Complex.I
  analytic p q := by
    fin_cases p; fin_cases q
    simp only [diagonal_apply_eq]
    intro w _
    exact analyticAt_coord_div_add 0 _ _ w
  symm _ _ := diagonal_transpose _
  im_posDef w hw := by
    rw [diagonal_map (by simp), posDef_diagonal_iff]
    intro _
    have h0 := hw.1 0
    simp only [Fin.castLE_refl] at h0
    rw [Complex.add_im, im_div_two_pi_I, Complex.I_im]
    have : 0 < -(w 0).re / (2 * Real.pi) := div_pos (by linarith) (by positivity)
    linarith
  B _ := 1
  B_symm _ := transpose_one
  periodic i w _ := by
    fin_cases i
    ext p q
    fin_cases p; fin_cases q
    simp [diagonal_apply_eq, add_div, div_self two_pi_I_ne_zero]
    ring
def periodTwo : PeriodPolydisc 1 1 2 where
  a_le := le_rfl
  τ w := diagonal ![w 0 / (2 * Real.pi * Complex.I) + Complex.I, Complex.I]
  analytic p q := by
    intro w _
    fin_cases p <;> fin_cases q <;> simp <;>
      first | exact analyticAt_coord_div_add 0 _ _ w | exact analyticAt_const
  symm _ _ := diagonal_transpose _
  im_posDef w hw := by
    rw [diagonal_map (by simp), posDef_diagonal_iff]
    intro i
    have h0 := hw.1 0
    simp only [Fin.castLE_refl] at h0
    fin_cases i
    · simp only [Function.comp_apply, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [Complex.add_im, im_div_two_pi_I, Complex.I_im]
      have : 0 < -(w 0).re / (2 * Real.pi) := div_pos (by linarith) (by positivity)
      linarith
    · simp
  B _ := diagonal ![1, 0]
  B_symm _ := diagonal_transpose _
  periodic i w _ := by
    fin_cases i
    ext p q
    fin_cases p <;> fin_cases q <;> simp [diagonal_apply, add_div, div_self two_pi_I_ne_zero] <;> ring
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Regular


