-- Prove2me | solution 1 for Auto.HeatData.continuousOn_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:31:19.400743+00:00
-- url     : https://prove2.me/submissions/b4b9bc30-59c7-4846-9841-2af9266f2a21

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_continuous_scalars

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
variable (Hd : HeatData ι) (α : Fin 3 → ℝ)
namespace Auto.HeatData
theorem _root_.solution (hα : ∀ k, 0 < α k) {η : ℝ} (hη : 0 < η) (v : Fin 3) :
    let S : Set (ℝ × (Fin 3 → ℝ)) := Set.Ioi 0 ×ˢ Set.univ
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.e z.2 (sig α z.1) η v) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) =>
      tr32 η (Hd.T z.2 (sig α z.1) v) (Hd.Ui z.2 (sig α z.1) v)) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => tr32 η (Hd.T z.2 (sig α z.1) v) (wGram (Hd.Brow z.2
        (sig α z.1) v) (Hd.ddw z.2 (sig α z.1) v))) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) =>
      tr32 η (Hd.S z.2 (sig α z.1) v) (Hd.Pnext z.2 (sig α z.1) v)) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) =>
      tr32 η (Hd.S z.2 (sig α z.1) v) (Hd.Pprev z.2 (sig α z.1) v)) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => tr32 η (Hd.S z.2 (sig α z.1) v) (wGram (Hd.Bnext z.2
        (sig α z.1) v) (Hd.ddw z.2 (sig α z.1) (v + 1)))) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => tr32 η (Hd.S z.2 (sig α z.1) v) (wGram (Hd.Bprev z.2
        (sig α z.1) v) (Hd.ddw z.2 (sig α z.1) (v - 1)))) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.V z.2 (sig α z.1) η v) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.Ynext z.2 (sig α z.1) η v) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.Yprev z.2 (sig α z.1) η v) S ∧
    ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Hd.Z z.2 (sig α z.1) η v) S := by
  intro S
  have hp : Continuous fun x : S => (x : ℝ × (Fin 3 → ℝ)).2 := continuous_snd.comp
      continuous_subtype_val
  have hσ : Continuous fun x : S => sig α (x : ℝ × (Fin 3 → ℝ)).1 :=
    continuous_pi fun k => continuous_const.mul (continuous_fst.comp continuous_subtype_val)
  have hpos : ∀ (x : S) k, 0 < sig α (x : ℝ × (Fin 3 → ℝ)).1 k := fun x k =>
    mul_pos (hα k) x.2.1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ :=
    Hd.continuous_scalars hp hσ hpos hη v
  simp only [continuousOn_iff_continuous_domRestrict]
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩
end Auto.HeatData
