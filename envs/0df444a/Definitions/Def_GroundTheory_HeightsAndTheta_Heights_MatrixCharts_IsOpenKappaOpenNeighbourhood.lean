-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_IsOpenKappaOpenNeighbourhood
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_IsOpenKappaOpenNeighbourhood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:24:23.6301+00:00
-- url     : https://prove2.me/theorems/5898df98-a8b9-4a1d-83bc-68df21578d4d
-- title:
--   Is Open Kappa Open Neighbourhood
-- statement:
--   Definitions and structural lemmas for Is Open Kappa Open Neighbourhood, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/IsOpenKappaOpenNeighbourhood.lean

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart
open Matrix
noncomputable section
def imPart {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  M.map Complex.im
def cplx {ι κ : Type*} (M : Matrix ι κ ℝ) : Matrix ι κ ℂ :=
  M.map (fun x : ℝ => (x : ℂ))
def qf {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ) (w : ι → ℂ) : ℝ :=
  (star w ⬝ᵥ (cplx Q *ᵥ w)).re
def realIP {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (v w : Fin g → ℂ) : ℝ :=
  (star v ⬝ᵥ (cplx Y⁻¹ *ᵥ w)).re
def yNorm {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (w : Fin g → ℂ) : ℝ :=
  Real.sqrt (qf Y⁻¹ w)
def punctured {n a : ℕ} (ha : a ≤ n) (U : Set (Fin n → ℂ)) : Set (Fin n → ℂ) :=
  {z | z ∈ U ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}
def lwP₂ (z : ℂ) : ℝ :=
  Real.log (1 / ‖z‖) / (2 * Real.pi)
def chartY {n a g : ℕ} (ha : a ≤ n) (tau0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ :=
  imPart (tau0 z) + ∑ i : Fin a, lwP₂ (z (Fin.castLE ha i)) • B i
def chartR {n a : ℕ} (ha : a ≤ n) (z : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ i : Fin a, Real.log (1 / ‖z (Fin.castLE ha i)‖ ^ 2)
def gramLogDet {g k : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (F : Matrix (Fin g) (Fin k) ℂ) : ℝ :=
  Real.log (Fᴴ * cplx Y⁻¹ * F).det.re
structure PeriodChartData (n a g m k : ℕ) where
  U : Set (Fin n → ℂ)
  isOpen_U : IsOpen U
  U_sub : U ⊆ Metric.ball 0 1
  a_le : a ≤ n
  tau0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  tau_analyticOn : ∀ j l : Fin g, AnalyticOnNhd ℂ (fun z => tau0 z j l) U
  tau_transpose_eq : ∀ z ∈ U, (tau0 z)ᵀ = tau0 z
  B : Fin a → Matrix (Fin g) (Fin g) ℝ
  B_psd : ∀ i, (B i).PosSemidef
  c : ℝ
  c_pos : 0 < c
  Y_ge : ∀ z ∈ punctured a_le U, (chartY a_le tau0 B z - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  V : Set (Fin m → ℂ)
  isOpen_V : IsOpen V
  f : (Fin n → ℂ) × (Fin m → ℂ) → Matrix (Fin g) (Fin k) ℂ
  f_analytic : ∀ (j : Fin g) (l : Fin k), AnalyticOnNhd ℂ (fun p => f p j l) (U ×ˢ V)
  f_rank : ∀ p ∈ U ×ˢ V, (f p).rank = k
  K : Set ((Fin n → ℂ) × (Fin m → ℂ))
  K_compact : IsCompact K
  K_sub : K ⊆ U ×ˢ V
namespace PeriodChartData
variable {n a g m k : ℕ} (D : PeriodChartData n a g m k)
def Ustar : Set (Fin n → ℂ) := punctured D.a_le D.U
def Y (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℝ := chartY D.a_le D.tau0 D.B z
def r (z : Fin n → ℂ) : ℝ := chartR D.a_le z
def u (p : (Fin n → ℂ) × (Fin m → ℂ)) : ℝ := gramLogDet (D.Y p.1) (D.f p)
def tau (l : Fin a → ℂ) (z : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  D.tau0 z + ∑ i : Fin a, (l i / (2 * (Real.pi : ℂ) * Complex.I)) • cplx (D.B i)
end PeriodChartData
def splitPt {n m : ℕ} (x : Fin (n + m) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) :=
  (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j))
def M1.Statement : Prop :=
  ∀ (n a g m k : ℕ) (D : PeriodChartData n a g m k), ∃ C : ℝ,
    ∀ p ∈ D.K, p.1 ∈ D.Ustar →
      (D.Y p.1 - D.c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef ∧
      ((C * D.r p.1) • (1 : Matrix (Fin g) (Fin g) ℝ) - D.Y p.1).PosSemidef ∧
      -(C * Real.log (D.r p.1)) ≤ D.u p ∧ D.u p ≤ C
def M2.Statement : Prop :=
  ∀ (n a g m k : ℕ) (D : PeriodChartData n a g m k), ∃ C : ℝ,
    ∀ p ∈ D.K, p.1 ∈ D.Ustar →
      DifferentiableAt ℝ D.u p ∧
        ‖fderiv ℝ D.u p‖ ≤ C * D.r p.1 ^ C * Real.exp (D.r p.1 / 2)
structure PshData (N g k : ℕ) where
  W : Set (Fin N → ℂ)
  isOpen_kappaOpenNeighbourhood : IsOpen W
  tau : (Fin N → ℂ) → Matrix (Fin g) (Fin g) ℂ
  tau_analytic : ∀ j l : Fin g, AnalyticOnNhd ℂ (fun z => tau z j l) W
  tau_symm : ∀ z ∈ W, (tau z)ᵀ = tau z
  im_posDef : ∀ z ∈ W, (imPart (tau z)).PosDef
  F : (Fin N → ℂ) → Matrix (Fin g) (Fin k) ℂ
  F_analytic : ∀ (j : Fin g) (l : Fin k), AnalyticOnNhd ℂ (fun z => F z j l) W
  F_rank : ∀ z ∈ W, (F z).rank = k
def M3.Statement : Prop :=
  ∀ (N g k : ℕ) (P : PshData N g k),
    ReciprocityTheory.AnForm.A.IsPsh P.W (fun z => gramLogDet (imPart (P.tau z)) (P.F z))
def PeriodMatrixChart.Statement : Prop :=
  ∀ (n a g m k : ℕ) (D : PeriodChartData n a g m k),
    ReciprocityTheory.AnForm.A.IsPsh (splitPt ⁻¹' (D.Ustar ×ˢ D.V)) (fun x => D.u (splitPt x))
def M4.Statement : Prop :=
  ∀ (r s : ℕ) (Y : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℝ), Y.PosDef → ∀ v : Fin s → ℂ,
    IsLeast (Set.range fun x : Fin r → ℂ => qf Y⁻¹ (Sum.elim x v)) (qf (Y.toBlocks₂₂)⁻¹ v)
def periodLattice {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) : Submodule ℤ (Fin g → ℂ) :=
  Submodule.span ℤ (Set.range (fun j : Fin g => (Pi.single j (1 : ℂ) : Fin g → ℂ)) ∪
    Set.range (fun j : Fin g => T *ᵥ (Pi.single j (1 : ℂ) : Fin g → ℂ)))
def firstBlock {g r : ℕ} (hr : r ≤ g) : Submodule ℤ (Fin g → ℂ) :=
  Submodule.span ℤ (Set.range (fun j : Fin r => (Pi.single (Fin.castLE hr j) (1 : ℂ) : Fin g → ℂ)))
def succMin {g : ℕ} (len : (Fin g → ℂ) → ℝ) (L : Submodule ℤ (Fin g → ℂ)) (j : ℕ) : ℝ :=
  sInf {t : ℝ | j ≤ Module.finrank ℝ (Submodule.span ℝ {v | v ∈ L ∧ len v ≤ t})}
def gramCovol {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (I : Submodule ℤ (Fin g → ℂ)) : ℝ :=
  sInf {x : ℝ | ∃ (q : ℕ) (b : Fin q → Fin g → ℂ), LinearIndependent ℤ b ∧
    Submodule.span ℤ (Set.range b) = I ∧
    x = Real.sqrt (Matrix.of (fun i j => realIP Y (b i) (b j))).det}
structure ToricBlock {n a g m k : ℕ} (D : PeriodChartData n a g m k) (r : ℕ) : Prop where
  r_le : r ≤ g
  B_support : ∀ (i : Fin a) (j l : Fin g), (r ≤ j.val ∨ r ≤ l.val) → D.B i j l = 0
  sum_posDef : ((∑ i, D.B i).submatrix (Fin.castLE r_le) (Fin.castLE r_le)).PosDef
def M5.Statement : Prop :=
  ∀ (n a g m k : ℕ) (D : PeriodChartData n a g m k) (r : ℕ) (T : ToricBlock D r),
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ p ∈ D.K, p.1 ∈ D.Ustar → ∀ l : Fin a → ℂ,
        (∀ i, Complex.exp (l i) = p.1 (Fin.castLE D.a_le i)) →
        (∀ w ∈ periodLattice (D.tau l p.1), w ∉ firstBlock T.r_le → c₁ ≤ yNorm (D.Y p.1) w) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ r →
          succMin (yNorm (D.Y p.1)) (firstBlock T.r_le) j ≤ D.c ^ (-(1 / 2 : ℝ))) ∧
        (∀ I : Submodule ℤ (Fin g → ℂ), I ≤ periodLattice (D.tau l p.1) →
          c₂ * gramCovol (D.Y p.1) (firstBlock T.r_le) ≤ gramCovol (D.Y p.1) I)
def exampleChart : PeriodChartData 1 1 2 1 2 where
  U := Metric.ball 0 1
  isOpen_U := Metric.isOpen_ball
  U_sub := subset_rfl
  a_le := le_rfl
  tau0 := fun _ => Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  tau_analyticOn := fun _ _ => analyticOnNhd_const
  tau_transpose_eq := fun _ _ => by simp [transpose_smul]
  B := fun _ => diagonal ![1, 0]
  B_psd := fun _ => by
    rw [posSemidef_diagonal_iff]
    intro i; fin_cases i <;> simp
  c := 1
  c_pos := one_pos
  Y_ge := by
    intro z hz
    have hb : ‖z 0‖ < 1 := by
      have h1 : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz.1
      exact lt_of_le_of_lt (norm_le_pi_norm z 0) h1
    have hw : 0 ≤ lwP₂ (z 0) := by
      unfold lwP₂
      apply div_nonneg _ (by positivity)
      apply Real.log_nonneg
      have hz0 : z 0 ≠ 0 := by simpa using hz.2 0
      rw [one_le_div (norm_pos_iff.mpr hz0)]
      exact hb.le
    have heq : chartY le_rfl (fun _ => Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (fun _ => diagonal ![1, 0]) z - (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
        diagonal ![lwP₂ (z 0), 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [chartY, imPart]
    rw [heq, posSemidef_diagonal_iff]
    intro i; fin_cases i <;> simp [hw]
  V := Set.univ
  isOpen_V := isOpen_univ
  f := fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  f_analytic := fun _ _ => analyticOnNhd_const
  f_rank := fun _ _ => by simp [Matrix.rank_one]
  K := {((fun _ => (1 / 2 : ℂ)), (fun _ => (0 : ℂ)))}
  K_compact := isCompact_singleton
  K_sub := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨?_, Set.mem_univ _⟩
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num)]
    intro i; norm_num
def examplePsh : PshData 1 2 2 where
  W := Set.univ
  isOpen_kappaOpenNeighbourhood := isOpen_univ
  tau := fun _ => Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  tau_analytic := fun _ _ => analyticOnNhd_const
  tau_symm := fun _ _ => by simp [transpose_smul]
  im_posDef := by
    intro z _
    have : imPart (Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [imPart]
    rw [this]
    exact PosDef.one
  F := fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  F_analytic := fun _ _ => analyticOnNhd_const
  F_rank := fun _ _ => by simp [Matrix.rank_one]
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.MatrixChart


