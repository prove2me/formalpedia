-- Prove2me | solution 1 for Auto.HeatData.scalar_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:31:40.699062+00:00
-- url     : https://prove2.me/submissions/9e6f7982-c237-49f4-93b7-9b14d7882859

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_abs_matCostBil_le
public import Theorems.Thm_Auto_posDef_add_smul_one
public import Theorems.Thm_Auto_HeatData_phi_nonneg
public import Theorems.Thm_Auto_HeatData_entry_bounds
public import Theorems.Thm_Auto_HeatData_phi_le_two
public import Theorems.Thm_Auto_HeatData_gram_scalar_bounds

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) {η : ℝ} (hη : 0 < η) {σa σb : ℝ} (ha : 0 < σa)
    (hab : σa ≤ σb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p σ : Fin 3 → ℝ, (∀ k, σ k ∈ Set.Icc σa σb) → ∀ v, |Hd.e p σ η v| ≤ C *
      phi σb v p ^ 2 ∧ |tr32 η (Hd.T p σ v) (Hd.Ui p σ v)| ≤ C * phi σb v p ^ 2 ∧ |tr32 η (Hd.T p
      σ v) (wGram (Hd.Brow p σ v) (Hd.ddw p σ v))| ≤ C * phi σb v p ^ 2 ∧ |tr32 η (Hd.S p σ v)
      (Hd.Pnext p σ v)| ≤ C * phi σb v p ^ 2 ∧ |tr32 η (Hd.S p σ v) (Hd.Pprev p σ v)| ≤ C * phi σb
      v p ^ 2 ∧ |tr32 η (Hd.S p σ v) (wGram (Hd.Bnext p σ v) (Hd.ddw p σ (v + 1)))| ≤ C * phi σb v
      p ^ 2 ∧ |tr32 η (Hd.S p σ v) (wGram (Hd.Bprev p σ v) (Hd.ddw p σ (v - 1)))| ≤ C * phi σb v p
      ^ 2 ∧ |Hd.V p σ η v| ≤ C * phi σb v p ^ 2 ∧ |Hd.Ynext p σ η v| ≤ C * phi σb v p ^ 2 ∧
      |Hd.Yprev p σ η v| ≤ C * phi σb v p ^ 2 ∧ |Hd.Z p σ η v| ≤ C * phi σb v p ^ 2 := by
  obtain ⟨C₀, hC₀, hent⟩ := Hd.entry_bounds hh ha hab
  have hb : 0 < σb := ha.trans_le hab
  set N : ℝ := Fintype.card (ι ⊕ ι) + Fintype.card ι
  have hN1 : (Fintype.card (ι ⊕ ι) : ℝ) ≤ N := by
    simp only [N]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  have hN2 : (Fintype.card ι : ℝ) ≤ N := by
    simp only [N]; linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (ι ⊕ ι))]
  set A1 := (3 / 2) * √(N * (4 * C₀) + N * η) * N * C₀
  set A2 := (3 / 4) * N ^ 2 * (4 * C₀) * C₀ / √η
  set A3 := 2 * N * C₀ * √(N * (4 * C₀) + η)
  have hN0 : 0 ≤ N := by positivity
  have hA1 : 0 ≤ A1 := by positivity
  have hA2 : 0 ≤ A2 := by positivity
  have hA3 : 0 ≤ A3 := by positivity
  refine ⟨A1 + A2 + A3, by positivity, fun p σ hσ v => ?_⟩
  obtain ⟨hT, hS⟩ := hent p σ hσ v
  set φ := phi σb v p
  have hφ : 0 ≤ φ := phi_nonneg _ _ _
  have hφ2 : φ ≤ 2 := phi_le_two hb v p
  have hφsq : 0 ≤ φ ^ 2 := sq_nonneg _
  have hTpsd : (Hd.T p σ v).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have hSpsd : (Hd.S p σ v).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _
  obtain ⟨gT, eT⟩ := gram_scalar_bounds hN1 hC₀ hφ hφ2 hη hTpsd (fun a b => (hT a b).1)
  obtain ⟨gS, -⟩ := gram_scalar_bounds hN2 hC₀ hφ hφ2 hη hSpsd (fun a b => (hS a b).1)
  have w1 : ∀ x, x ≤ A1 * φ ^ 2 → x ≤ (A1 + A2 + A3) * φ ^ 2 := fun x hx => by nlinarith
  have w2 : ∀ x, x ≤ A2 * φ ^ 2 → x ≤ (A1 + A2 + A3) * φ ^ 2 := fun x hx => by nlinarith
  have w3 : ∀ x, x ≤ A3 * φ ^ 2 → x ≤ (A1 + A2 + A3) * φ ^ 2 := fun x hx => by nlinarith
  have hY1 := (gS _ fun a b => (hS a b).2.1).2
  have hY2 := (gS _ fun a b => (hS a b).2.2.1).2
  refine ⟨w3 _ eT, w1 _ (gT _ fun a b => (hT a b).2.1).1,
    w1 _ (gT _ fun a b => (hT a b).2.2).1, w1 _ (gS _ fun a b => (hS a b).2.1).1,
    w1 _ (gS _ fun a b => (hS a b).2.2.1).1, w1 _ (gS _ fun a b => (hS a b).2.2.2.1).1,
    w1 _ (gS _ fun a b => (hS a b).2.2.2.2).1, w2 _ (gT _ fun a b => (hT a b).2.1).2,
    w2 _ hY1, w2 _ hY2, ?_⟩
  have hPD := posDef_add_smul_one hSpsd hη
  have hZ := abs_matCostBil_le hPD (Hd.Pnext p σ v) (Hd.Pprev p σ v)
  refine w2 _ (hZ.trans ?_)
  have e1 : 0 ≤ (matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pnext p σ v)).toReal :=
    ENNReal.toReal_nonneg
  have e2 : 0 ≤ (matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pprev p σ v)).toReal :=
    ENNReal.toReal_nonneg
  rw [abs_of_nonneg e1] at hY1
  rw [abs_of_nonneg e2] at hY2
  calc √(matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pnext p σ v)).toReal *
        √(matCost (Hd.S p σ v + (η : ℂ) • 1) (Hd.Pprev p σ v)).toReal
      ≤ √(A2 * φ ^ 2) * √(A2 * φ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hY1) (Real.sqrt_le_sqrt hY2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
    _ = A2 * φ ^ 2 := Real.mul_self_sqrt (by positivity)
end Auto.HeatData
