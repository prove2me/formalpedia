-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:16.099813+00:00
-- url     : https://prove2.me/theorems/9193f90e-9f27-471b-9adb-ba54829a0ace
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/Statements.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
def splitCoord (n m : ℕ) (w : Fin (n + m) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) :=
  (fun j => w (Fin.castAdd m j), fun k => w (Fin.natAdd n k))
def hermPair {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v w : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ ((A.map fun x : ℝ => (x : ℂ)) *ᵥ w)).re
def hermValue {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w : ι → ℂ) : ℝ :=
  hermPair A w w
def metricLength {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (w : ι → ℂ) : ℝ :=
  Real.sqrt (hermValue Y⁻¹ w)
def covolume {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) {k : ℕ}
    (v : Fin k → ι → ℂ) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of fun j l => hermPair Y⁻¹ (v j) (v l)))
def logDetGram {g rk : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (F : Matrix (Fin g) (Fin rk) ℂ) : ℝ :=
  Real.log (Fᴴ * (Y⁻¹).map (fun x : ℝ => (x : ℂ)) * F).det.re
def intVecC {g : ℕ} (a : Fin g → ℤ) : Fin g → ℂ := fun k => (a k : ℂ)
def periodLattice {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Set (Fin g → ℂ) :=
  {w | ∃ a n : Fin g → ℤ, w = intVecC a + τ *ᵥ intVecC n}
def leadingLattice (g r : ℕ) : Set (Fin g → ℂ) :=
  {w | ∃ a : Fin g → ℤ, (∀ k : Fin g, r ≤ k.val → a k = 0) ∧ w = intVecC a}
def unitPolydisc (n : ℕ) : Set (Fin n → ℂ) := {z | ∀ j, ‖z j‖ < 1}
def cuspCoord {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) : ℂ := z (Fin.castLE h j)
def cuspTime {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.log ‖cuspCoord h z j‖⁻¹
def puncturedChart {n a : ℕ} (h : a ≤ n) (U : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | z ∈ U ∧ ∀ j, cuspCoord h z j ≠ 0}
def chartRadius {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ j, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹
def chartImag {n a g : ℕ} (h : a ≤ n) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  (τ0 z).map Complex.im + ∑ j, cuspTime h z j • B j
structure PeriodChartData where

  n : ℕ

  m : ℕ

  g : ℕ

  a : ℕ

  rk : ℕ
  a_le : a ≤ n
  U : Set (Fin n → ℂ)
  isOpen_U : IsOpen U
  U_subset : U ⊆ unitPolydisc n
  τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  τ0_analytic : ∀ j k, AnalyticOnNhd ℂ (fun z => τ0 z j k) U
  τ0_symm : ∀ z ∈ U, (τ0 z)ᵀ = τ0 z
  B : Fin a → Matrix (Fin g) (Fin g) ℝ

  B_psd : ∀ j, (B j).PosSemidef
  c : ℝ
  c_pos : 0 < c
  Y_ge : ∀ z ∈ puncturedChart a_le U, (chartImag a_le τ0 B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  V : Set (Fin m → ℂ)
  isOpen_V : IsOpen V
  f : (Fin n → ℂ) × (Fin m → ℂ) → Matrix (Fin g) (Fin rk) ℂ
  f_analytic : ∀ j k, AnalyticOnNhd ℂ (fun p => f p j k) (U ×ˢ V)
  f_rank : ∀ p ∈ U ×ˢ V, (f p).rank = rk
  K : Set ((Fin n → ℂ) × (Fin m → ℂ))
  isCompact_K : IsCompact K
  K_subset : K ⊆ U ×ˢ V
namespace PeriodChartData
variable (D : PeriodChartData)
def Ustar : Set (Fin D.n → ℂ) := puncturedChart D.a_le D.U
def Y (z : Fin D.n → ℂ) : Matrix (Fin D.g) (Fin D.g) ℝ := chartImag D.a_le D.τ0 D.B z
def radius (z : Fin D.n → ℂ) : ℝ := chartRadius D.a_le z
def u (p : (Fin D.n → ℂ) × (Fin D.m → ℂ)) : ℝ := logDetGram (D.Y p.1) (D.f p)
def period (z : Fin D.n → ℂ) (ℓ : Fin D.a → ℂ) : Matrix (Fin D.g) (Fin D.g) ℂ :=
  D.τ0 z + ∑ j, (ℓ j / (2 * Real.pi * Complex.I)) • (D.B j).map (fun x : ℝ => (x : ℂ))
end PeriodChartData
structure ToricBlock (D : PeriodChartData) where
  r : ℕ
  r_le : r ≤ D.g
  support : ∀ (j : Fin D.a) (k l : Fin D.g), (r ≤ k.val ∨ r ≤ l.val) → D.B j k l = 0
  pos : ((∑ j, D.B j).submatrix (Fin.castLE r_le) (Fin.castLE r_le)).PosDef
structure SiegelFamily (N g rk : ℕ) where
  W : Set (Fin N → ℂ)
  isOpen_kappaOpenNeighbourhood : IsOpen W
  τ : (Fin N → ℂ) → Matrix (Fin g) (Fin g) ℂ
  τ_analytic : ∀ j k, AnalyticOnNhd ℂ (fun x => τ x j k) W
  τ_symm : ∀ x ∈ W, (τ x)ᵀ = τ x
  im_posDef : ∀ x ∈ W, ((τ x).map Complex.im).PosDef
  f : (Fin N → ℂ) → Matrix (Fin g) (Fin rk) ℂ
  f_analytic : ∀ j k, AnalyticOnNhd ℂ (fun x => f x j k) W
  f_rank : ∀ x ∈ W, (f x).rank = rk
def ChartBounds.Statement : Prop :=
  ∀ D : PeriodChartData, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ D.K, p.1 ∈ D.Ustar →
    (D.Y p.1 - D.c • (1 : Matrix (Fin D.g) (Fin D.g) ℝ)).PosSemidef ∧
    ((C * D.radius p.1) • (1 : Matrix (Fin D.g) (Fin D.g) ℝ) - D.Y p.1).PosSemidef ∧
    (C * D.radius p.1)⁻¹ ^ D.rk * ((D.f p)ᴴ * D.f p).det.re ≤
      ((D.f p)ᴴ * (D.Y p.1)⁻¹.map (fun x : ℝ => (x : ℂ)) * D.f p).det.re ∧
    ((D.f p)ᴴ * (D.Y p.1)⁻¹.map (fun x : ℝ => (x : ℂ)) * D.f p).det.re ≤
      D.c⁻¹ ^ D.rk * ((D.f p)ᴴ * D.f p).det.re ∧
    -C * Real.log (D.radius p.1) ≤ D.u p ∧ D.u p ≤ C
def ChartGradient.Statement : Prop :=
  ∀ D : PeriodChartData, ∃ C : ℝ, 0 < C ∧ ∀ p ∈ D.K, p.1 ∈ D.Ustar →
    DifferentiableAt ℝ D.u p ∧
      ‖fderiv ℝ D.u p‖ ≤ C * D.radius p.1 ^ C * Real.exp (D.radius p.1 / 2)
def LogDetGramPsh.Statement : Prop :=
  ∀ (N g rk : ℕ) (S : SiegelFamily N g rk),
    ReciprocityTheory.AnForm.A.IsPsh S.W (fun x => logDetGram ((S.τ x).map Complex.im) (S.f x))
def ChartPotentialPsh.Statement : Prop :=
  ∀ D : PeriodChartData,
    ReciprocityTheory.AnForm.A.IsPsh (splitCoord D.n D.m ⁻¹' (D.Ustar ×ˢ D.V)) (D.u ∘ splitCoord D.n D.m)
def SchurQuotient.Statement : Prop :=
  ∀ (r s : ℕ) (Y : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ), Y.PosDef → ∀ v : Fin s → ℂ,
    IsLeast (Set.range fun x : Fin r → ℂ => hermValue Y⁻¹ (Sum.elim x v))
      (hermValue (Y.toBlocks₂₂)⁻¹ v)
def SchurQuotientPeriod.Statement : Prop :=
  ∀ (r s : ℕ) (τ : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ), τᵀ = τ → (τ.map Complex.im).PosDef →
    (τ.toBlocks₂₂)ᵀ = τ.toBlocks₂₂ ∧ (τ.toBlocks₂₂).map Complex.im = (τ.map Complex.im).toBlocks₂₂ ∧
      ((τ.toBlocks₂₂).map Complex.im).PosDef
def CuspLattice.Statement : Prop :=
  ∀ (D : PeriodChartData) (T : ToricBlock D), ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ p ∈ D.K, p.1 ∈ D.Ustar → ∀ ℓ : Fin D.a → ℂ,
      (∀ j, Complex.exp (ℓ j) = cuspCoord D.a_le p.1 j) →
      (∀ a n : Fin D.g → ℤ, (n ≠ 0 ∨ ∃ k : Fin D.g, T.r ≤ k.val ∧ a k ≠ 0) →
          c₁ ≤ metricLength ((D.period p.1 ℓ).map Complex.im)
            (intVecC a + D.period p.1 ℓ *ᵥ intVecC n)) ∧
      (∃ v : Fin T.r → Fin D.g → ℂ, (∀ j, v j ∈ leadingLattice D.g T.r) ∧
          LinearIndependent ℤ v ∧
          ∀ j, metricLength ((D.period p.1 ℓ).map Complex.im) (v j) ≤ D.c ^ (-(1 / 2 : ℝ))) ∧
      (∀ (k : ℕ) (v : Fin k → Fin D.g → ℂ), (∀ j, v j ∈ periodLattice (D.period p.1 ℓ)) →
          LinearIndependent ℤ v →
          c₂ * covolume ((D.period p.1 ℓ).map Complex.im)
              (fun j : Fin T.r => Pi.single (Fin.castLE T.r_le j) (1 : ℂ)) ≤
            covolume ((D.period p.1 ℓ).map Complex.im) v)
theorem cuspTime_nonneg {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (j : Fin a)
    (hz : ‖cuspCoord h z j‖ < 1) : 0 ≤ cuspTime h z j := by
  unfold cuspTime
  rw [Real.log_inv]
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hz.le))
def exampleChart : PeriodChartData where
  n := 2
  m := 1
  g := 2
  a := 1
  rk := 1
  a_le := by norm_num
  U := Metric.ball 0 1
  isOpen_U := Metric.isOpen_ball
  U_subset := fun z hz j => (norm_le_pi_norm z j).trans_lt (mem_ball_zero_iff.mp hz)
  τ0 := fun z => Matrix.diagonal ![Complex.I, 2 * Complex.I + z 1]
  τ0_analytic := by
    intro j k
    fin_cases j <;> fin_cases k
    · simpa using analyticOnNhd_const
    · simpa using analyticOnNhd_const
    · simpa using analyticOnNhd_const
    · simp only [Matrix.diagonal_apply_eq]
      exact analyticOnNhd_const.add
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).analyticOnNhd _)
  τ0_symm := fun z _ => Matrix.diagonal_transpose _
  B := fun _ => Matrix.diagonal ![1, 0]
  B_psd := fun _ => PosSemidef.diagonal (by intro k; fin_cases k <;> simp)
  c := 1
  c_pos := by norm_num
  Y_ge := by
    intro z hz
    have h0 : ‖z 0‖ < 1 := (norm_le_pi_norm z 0).trans_lt (mem_ball_zero_iff.mp hz.1)
    have h1 : ‖z 1‖ < 1 := (norm_le_pi_norm z 1).trans_lt (mem_ball_zero_iff.mp hz.1)
    have ht : 0 ≤ cuspTime (n := 2) (a := 1) (by norm_num) z 0 := cuspTime_nonneg _ z 0 h0
    have him : -1 < (z 1).im := by
      have := (Complex.abs_im_le_norm (z 1)).trans_lt h1
      linarith [neg_abs_le (z 1).im]
    have : chartImag (n := 2) (a := 1) (by norm_num) (fun z => Matrix.diagonal ![Complex.I, 2 * Complex.I + z 1])
        (fun _ => Matrix.diagonal ![1, 0]) z - (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
        Matrix.diagonal ![cuspTime (n := 2) (a := 1) (by norm_num) z 0, 1 + (z 1).im] := by
      ext k l
      fin_cases k <;> fin_cases l <;> simp [chartImag]
      ring
    rw [this]
    exact PosSemidef.diagonal (by intro k; fin_cases k <;> simp <;> linarith)
  V := Set.univ
  isOpen_V := isOpen_univ
  f := fun p => Matrix.of ![![1], ![p.2 0]]
  f_analytic := by
    intro j k
    fin_cases j <;> fin_cases k
    · simpa using analyticOnNhd_const
    · simp only [Matrix.of_apply]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp
        (ContinuousLinearMap.snd ℂ (Fin 2 → ℂ) (Fin 1 → ℂ))).analyticOnNhd _
  f_rank := by
    intro p _
    apply le_antisymm (Matrix.rank_le_width _)
    have hP : (Matrix.of ![![(1 : ℂ), 0]] : Matrix (Fin 1) (Fin 2) ℂ) *
        Matrix.of ![![1], ![p.2 0]] = 1 := by
      ext k l
      fin_cases k; fin_cases l
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have := Matrix.rank_mul_le_right (Matrix.of ![![(1 : ℂ), 0]] : Matrix (Fin 1) (Fin 2) ℂ)
      (Matrix.of ![![1], ![p.2 0]])
    rw [hP, Matrix.rank_one] at this
    simpa using this
  K := Metric.closedBall 0 (1 / 2) ×ˢ Metric.closedBall 0 1
  isCompact_K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  K_subset := Set.prod_mono (Metric.closedBall_subset_ball (by norm_num)) (Set.subset_univ _)
def exampleToricBlock : ToricBlock exampleChart where
  r := 1
  r_le := by decide
  support := by
    intro j k l h
    fin_cases k <;> fin_cases l <;> simp_all [exampleChart]
  pos := by
    have : ((∑ j, exampleChart.B j).submatrix (Fin.castLE (by decide : 1 ≤ exampleChart.g))
        (Fin.castLE (by decide : 1 ≤ exampleChart.g))) = 1 := by
      ext k l
      fin_cases k; fin_cases l
      show (∑ _j : Fin 1, Matrix.diagonal ![(1 : ℝ), 0]) 0 0 = 1
      rw [Finset.sum_const]
      simp
    rw [this]
    exact PosDef.one
def upperHalfPlaneFamily : SiegelFamily 1 1 1 where
  W := {x | 0 < (x 0).im}
  isOpen_kappaOpenNeighbourhood := isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply 0))
  τ := fun x => Matrix.diagonal fun _ => x 0
  τ_analytic := by
    intro j k
    fin_cases j; fin_cases k
    simp only [Matrix.diagonal_apply_eq]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticOnNhd _
  τ_symm := fun _ _ => Matrix.diagonal_transpose _
  im_posDef := by
    intro x hx
    rw [Matrix.diagonal_map (by simp)]
    exact Matrix.posDef_diagonal_iff.mpr fun _ => hx
  f := fun _ => 1
  f_analytic := fun _ _ => analyticOnNhd_const
  f_rank := fun _ _ => by simp [Matrix.rank_one]
end
end GroundTheory.Heights₂.Heights


