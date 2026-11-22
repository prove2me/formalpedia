-- Prove2me | solution 1 for Auto.HeatData.continuous_mats
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:27:54.523809+00:00
-- url     : https://prove2.me/submissions/30bce306-50dd-4f72-bb8b-335b62b7cbe6

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_continuous_rdiag
public import Theorems.Thm_Auto_continuous_wGram
public import Theorems.Thm_Auto_HeatData_continuous_dw
public import Theorems.Thm_Auto_HeatData_continuous_ddw
public import Theorems.Thm_Auto_HeatData_continuous_sqw

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [TopologicalSpace X]
open Auto.HeatData
variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}
namespace Auto.HeatData
theorem _root_.solution (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    (v : Fin 3) :
    Continuous (fun x => Hd.T (p x) (σ x) v) ∧ Continuous (fun x => Hd.S (p x) (σ x) v) ∧
      Continuous (fun x => Hd.Ui (p x) (σ x) v) ∧ Continuous (fun x => Hd.Pnext (p x) (σ x) v) ∧
      Continuous (fun x => Hd.Pprev (p x) (σ x) v) ∧ Continuous (fun x => wGram (Hd.Brow (p x) (σ
      x) v) (Hd.ddw (p x) (σ x) v)) ∧ Continuous (fun x => wGram (Hd.Bnext (p x) (σ x) v) (Hd.ddw
      (p x) (σ x) (v + 1))) ∧ Continuous (fun x => wGram (Hd.Bprev (p x) (σ x) v) (Hd.ddw (p x) (σ
      x) (v - 1))) := by
  have hsq := Hd.continuous_sqw hp hσ hpos
  have hW : ∀ k, Continuous fun x => Hd.W (p x) (σ x) k := fun k =>
    ((continuous_rdiag (hsq k)).matrix_mul continuous_const).matrix_mul (continuous_rdiag (hsq _))
  have hR : Continuous fun x => Hd.R (p x) (σ x) v := by
    refine continuous_matrix fun i a => ?_
    rcases a with j | j
    · simpa [R, rowMat] using (hW v).matrix_elem i j
    · simpa [R, rowMat] using (hW (v - 1)).matrix_conjTranspose.matrix_elem i j
  have hDc : Continuous fun x => Hd.Dc (p x) (σ x) v :=
    Continuous.matrix_fromBlocks (continuous_rdiag (hsq _)) continuous_const continuous_const
        (continuous_rdiag (hsq _))
  have hBrow : Continuous fun x => Hd.Brow (p x) (σ x) v := continuous_const.matrix_mul hDc
  have hBn : Continuous fun x => Hd.Bnext (p x) (σ x) v :=
    continuous_const.matrix_mul (continuous_rdiag (hsq v))
  have hBp : Continuous fun x => Hd.Bprev (p x) (σ x) v :=
    continuous_const.matrix_mul (continuous_rdiag (hsq v))
  exact ⟨hR.matrix_conjTranspose.matrix_mul hR, hR.matrix_mul hR.matrix_conjTranspose,
    continuous_wGram hBrow (Hd.continuous_dw hp hσ hpos v),
    continuous_wGram hBn (Hd.continuous_dw hp hσ hpos _),
    continuous_wGram hBp (Hd.continuous_dw hp hσ hpos _),
    continuous_wGram hBrow (Hd.continuous_ddw hp hσ hpos v),
    continuous_wGram hBn (Hd.continuous_ddw hp hσ hpos _),
    continuous_wGram hBp (Hd.continuous_ddw hp hσ hpos _)⟩
end Auto.HeatData
