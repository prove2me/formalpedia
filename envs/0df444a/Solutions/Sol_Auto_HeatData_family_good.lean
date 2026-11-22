-- Prove2me | solution 1 for Auto.HeatData.family_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:33:58.814804+00:00
-- url     : https://prove2.me/submissions/401effc9-436c-4b76-802e-87507a33e57b

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_scalar_bounds
public import Theorems.Thm_Auto_HeatData_continuousOn_family

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
variable (Hd : HeatData ι) (α : Fin 3 → ℝ) (η : ℝ) (v : Fin 3)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) (hη : 0 < η) (hα1 : ∀ k, 1 ≤ α k)
    (hα2 : ∀ k, α k ≤ 2) {sa sb : ℝ} (hsa : 0 < sa) (hab : sa ≤ sb) :
    ∀ Q ∈ ({Hd.qE α η v, Hd.qDr α η v, Hd.qDn α η v, Hd.qDp α η v,
      Hd.qV α η v + Hd.qA α η v, Hd.qYn α η v + Hd.qB α η v,
      Hd.qYp α η v + Hd.qC α η v, Hd.qZ α η v, Hd.qV α η v,
      Hd.qYn α η v, Hd.qYp α η v, Hd.qA α η v, Hd.qB α η v, Hd.qC α η v} :
        Set (ℝ → (Fin 3 → ℝ) → ℝ)),
      ContinuousOn (fun z : ℝ × (Fin 3 → ℝ) => Q z.1 z.2) (Set.Ioi 0 ×ˢ Set.univ) ∧
      ∃ C, ∀ s ∈ Set.Icc sa sb, ∀ p, |Q s p| ≤ C * phi (2 * sb) v p ^ 2 := by
  have hα0 : ∀ k, 0 < α k := fun k => zero_lt_one.trans_le (hα1 k)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11⟩ := Hd.continuousOn_family α hα0 hη v
  obtain ⟨C, hC0, hC⟩ := Hd.scalar_bounds hh.le hη (σa := sa) (σb := 2 * sb) hsa (by linarith)
  have hrange : ∀ s ∈ Set.Icc sa sb, ∀ k, sig α s k ∈ Set.Icc sa (2 * sb) := by
    intro s hs k
    have hs0 : 0 < s := hsa.trans_le hs.1
    constructor
    · simp only [sig]; nlinarith [hα1 k, hs.1]
    · simp only [sig]; nlinarith [hα2 k, hs.2]
  have B := fun s (hs : s ∈ Set.Icc sa sb) p => hC p (sig α s) (hrange s hs) v
  intro Q hQ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨c1, C, fun s hs p => (B s hs p).1⟩
  · exact ⟨c2, C, fun s hs p => (B s hs p).2.1⟩
  · exact ⟨c4, C, fun s hs p => (B s hs p).2.2.2.1⟩
  · exact ⟨c5, C, fun s hs p => (B s hs p).2.2.2.2.1⟩
  · refine ⟨c8.add c3, 2 * C, fun s hs p => ?_⟩
    have h1 := (B s hs p).2.2.2.2.2.2.2.1
    have h2 := (B s hs p).2.2.1
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (by unfold qV qA; linarith)
  · refine ⟨c9.add c6, 2 * C, fun s hs p => ?_⟩
    have h1 := (B s hs p).2.2.2.2.2.2.2.2.1
    have h2 := (B s hs p).2.2.2.2.2.1
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (by unfold qYn qB; linarith)
  · refine ⟨c10.add c7, 2 * C, fun s hs p => ?_⟩
    have h1 := (B s hs p).2.2.2.2.2.2.2.2.2.1
    have h2 := (B s hs p).2.2.2.2.2.2.1
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (by unfold qYp qC; linarith)
  · exact ⟨c11, C, fun s hs p => (B s hs p).2.2.2.2.2.2.2.2.2.2⟩
  · exact ⟨c8, C, fun s hs p => (B s hs p).2.2.2.2.2.2.2.1⟩
  · exact ⟨c9, C, fun s hs p => (B s hs p).2.2.2.2.2.2.2.2.1⟩
  · exact ⟨c10, C, fun s hs p => (B s hs p).2.2.2.2.2.2.2.2.2.1⟩
  · exact ⟨c3, C, fun s hs p => (B s hs p).2.2.1⟩
  · exact ⟨c6, C, fun s hs p => (B s hs p).2.2.2.2.2.1⟩
  · exact ⟨c7, C, fun s hs p => (B s hs p).2.2.2.2.2.2.1⟩
end Auto.HeatData
