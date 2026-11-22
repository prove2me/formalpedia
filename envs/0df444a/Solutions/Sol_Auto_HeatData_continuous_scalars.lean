-- Prove2me | solution 1 for Auto.HeatData.continuous_scalars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:29:49.624913+00:00
-- url     : https://prove2.me/submissions/5deed6e0-92c3-4345-8386-21324950617d

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_continuous_mats
public import Theorems.Thm_Auto_continuous_tr32
public import Theorems.Thm_Auto_continuous_energyReg
public import Theorems.Thm_Auto_continuous_matCost

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
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
open Auto.HeatData
variable (Hd : HeatData ι) {p σ : X → Fin 3 → ℝ}
namespace Auto.HeatData
theorem _root_.solution (hp : Continuous p) (hσ : Continuous σ) (hpos : ∀ x k, 0 < σ x k)
    {η : ℝ} (hη : 0 < η) (v : Fin 3) :
    Continuous (fun x => Hd.e (p x) (σ x) η v) ∧ Continuous (fun x => tr32 η (Hd.T (p x) (σ x)
      v) (Hd.Ui (p x) (σ x) v)) ∧ Continuous (fun x => tr32 η (Hd.T (p x) (σ x) v) (wGram (Hd.Brow
      (p x) (σ x) v) (Hd.ddw (p x) (σ x) v))) ∧ Continuous (fun x => tr32 η (Hd.S (p x) (σ x) v)
      (Hd.Pnext (p x) (σ x) v)) ∧ Continuous (fun x => tr32 η (Hd.S (p x) (σ x) v) (Hd.Pprev (p x)
      (σ x) v)) ∧ Continuous (fun x => tr32 η (Hd.S (p x) (σ x) v) (wGram (Hd.Bnext (p x) (σ x) v)
      (Hd.ddw (p x) (σ x) (v + 1)))) ∧ Continuous (fun x => tr32 η (Hd.S (p x) (σ x) v) (wGram
      (Hd.Bprev (p x) (σ x) v) (Hd.ddw (p x) (σ x) (v - 1)))) ∧ Continuous (fun x => Hd.V (p x) (σ
      x) η v) ∧ Continuous (fun x => Hd.Ynext (p x) (σ x) η v) ∧ Continuous (fun x => Hd.Yprev (p
      x) (σ x) η v) ∧ Continuous (fun x => Hd.Z (p x) (σ x) η v) := by
  obtain ⟨hT, hS, hU, hPn, hPp, hM1, hM2, hM3⟩ := Hd.continuous_mats hp hσ hpos v
  have hTp : ∀ x, (Hd.T (p x) (σ x) v).PosSemidef := fun x =>
    Matrix.posSemidef_conjTranspose_mul_self _
  have hSp : ∀ x, (Hd.S (p x) (σ x) v).PosSemidef := fun x =>
    Matrix.posSemidef_self_mul_conjTranspose _
  refine ⟨continuous_energyReg hT hTp hη, continuous_tr32 hT hU hTp hη,
    continuous_tr32 hT hM1 hTp hη, continuous_tr32 hS hPn hSp hη, continuous_tr32 hS hPp hSp hη,
    continuous_tr32 hS hM2 hSp hη, continuous_tr32 hS hM3 hSp hη,
    continuous_matCost hT hU hTp hη, continuous_matCost hS hPn hSp hη,
    continuous_matCost hS hPp hSp hη, ?_⟩
  exact ((continuous_matCost hS (hPn.add hPp) hSp hη).sub (continuous_matCost hS (hPn.sub hPp) hSp
      hη)).div_const 4
end Auto.HeatData
