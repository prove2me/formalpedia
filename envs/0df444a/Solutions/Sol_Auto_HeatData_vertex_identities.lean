-- Prove2me | solution 1 for Auto.HeatData.vertex_identities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:35:43.129182+00:00
-- url     : https://prove2.me/submissions/64998eae-1df2-4d0a-b29b-22f34ea8d7c5

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_e_heat_row
public import Theorems.Thm_Auto_HeatData_e_heat_next
public import Theorems.Thm_Auto_HeatData_e_heat_prev
public import Theorems.Thm_Auto_HeatData_e_mixed
public import Theorems.Thm_Auto_integral_mul_deriv_coord
public import Theorems.Thm_Auto_hasDerivAt_Gm_coord
public import Theorems.Thm_Auto_good_integrable
public import Theorems.Thm_Auto_HeatData_family_good

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
theorem _root_.solution (hh : 0 < Hd.h) (hη : 0 < η) (hα1 : ∀ k, 1 ≤ α k) (hα2 : ∀ k, α k ≤ 2)
    {β sa sb : ℝ} (hβ : 0 < β) (hsa : 0 < sa) (hab : sa ≤ sb) {s : ℝ} (hs : s ∈ Set.Icc sa sb) :
    ∫ p, Gm β 0 s p * (Hd.qV α η v + Hd.qA α η v) s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p ∧ ∫ p,
      Gm β 0 s p * (Hd.qYn α η v + Hd.qB α η v) s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p ∧ ∫ p, Gm
      β 0 s p * (Hd.qYp α η v + Hd.qC α η v) s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p ∧ ∫ p, Gm β 0
      s p * Hd.qZ α η v s p = ∫ p, Gm β 2 s p * Hd.qE α η v s p := by
  have G := Hd.family_good α η v hh hη hα1 hα2 hsa hab
  have hsb : 0 < 2 * sb := by linarith
  have integ : ∀ Q ∈ ({Hd.qE α η v, Hd.qDr α η v, Hd.qDn α η v, Hd.qDp α η v,
      Hd.qV α η v + Hd.qA α η v, Hd.qYn α η v + Hd.qB α η v, Hd.qYp α η v + Hd.qC α η v,
      Hd.qZ α η v, Hd.qV α η v, Hd.qYn α η v, Hd.qYp α η v, Hd.qA α η v, Hd.qB α η v,
      Hd.qC α η v} : Set (ℝ → (Fin 3 → ℝ) → ℝ)),
      ∀ m, Integrable (fun p => Gm β m s p * Q s p) := fun Q hQ m =>
    (good_integrable (Q := fun z => Q z.1 z.2) hsa hsb hβ v (G Q hQ).1 (G Q hQ).2 m).1 s hs
  have iE := integ (Hd.qE α η v) (by simp)
  have iDr := integ (Hd.qDr α η v) (by simp)
  have iDn := integ (Hd.qDn α η v) (by simp)
  have iDp := integ (Hd.qDp α η v) (by simp)
  have iVA := integ (Hd.qV α η v + Hd.qA α η v) (by simp)
  have iYB := integ (Hd.qYn α η v + Hd.qB α η v) (by simp)
  have iYC := integ (Hd.qYp α η v + Hd.qC α η v) (by simp)
  have iZ := integ (Hd.qZ α η v) (by simp)
  have hσ : ∀ k, 0 < sig α s k := fun k =>
    mul_pos (zero_lt_one.trans_le (hα1 k)) (hsa.trans_le hs.1)
  have hrow := fun p => Hd.e_heat_row p (sig α s) hh.le hη hσ v
  have hnext := fun p => Hd.e_heat_next p (sig α s) hh.le hη hσ v
  have hprev := fun p => Hd.e_heat_prev p (sig α s) hh.le hη hσ v
  have hmix := fun p => Hd.e_mixed p (sig α s) hh.le hη hσ v
  have hG := fun m i p => hasDerivAt_Gm_coord β m s i p
  have hb : ∀ (i : Fin 3) (D : (Fin 3 → ℝ) → ℝ), (∀ p, HasDerivAt (fun x => Hd.qE α η v s
      (Function.update p i x)) (D p) (p i)) →
      Integrable (fun p => Gm β 1 s p * D p) →
      ∫ p, Gm β 1 s p * D p = -∫ p, Gm β 2 s p * Hd.qE α η v s p := fun i D hD hi =>
    integral_mul_deriv_coord i (F := Gm β 1 s) (F' := Gm β 2 s) (hG 1 i) hD hi (iE 2) (iE 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have ha := integral_mul_deriv_coord v (F := Gm β 0 s) (F' := Gm β 1 s) (G := Hd.qDr α η v s) (G'
      := (Hd.qV α η v + Hd.qA α η v) s) (hG 0 v) (fun p => (hrow p).2.1) (iVA 0) (iDr 1) (iDr 0)
    exact ha.trans ((congrArg Neg.neg (hb v (Hd.qDr α η v s) (fun p => (hrow p).1) (iDr 1))).trans
        (neg_neg _))
  · have ha := integral_mul_deriv_coord (v + 1) (F := Gm β 0 s) (F' := Gm β 1 s) (G := Hd.qDn α η v
      s) (G' := (Hd.qYn α η v + Hd.qB α η v) s) (hG 0 (v + 1)) (fun p => (hnext p).2.1) (iYB 0) (iDn
      1) (iDn 0)
    exact ha.trans ((congrArg Neg.neg (hb (v + 1) (Hd.qDn α η v s) (fun p => (hnext p).1) (iDn
        1))).trans (neg_neg _))
  · have ha := integral_mul_deriv_coord (v - 1) (F := Gm β 0 s) (F' := Gm β 1 s) (G := Hd.qDp α η v
      s) (G' := (Hd.qYp α η v + Hd.qC α η v) s) (hG 0 (v - 1)) (fun p => (hprev p).2.1) (iYC 0) (iDp
      1) (iDp 0)
    exact ha.trans ((congrArg Neg.neg (hb (v - 1) (Hd.qDp α η v s) (fun p => (hprev p).1) (iDp
        1))).trans (neg_neg _))
  · have ha := integral_mul_deriv_coord (v + 1) (F := Gm β 0 s) (F' := Gm β 1 s) (G := Hd.qDp α η v
      s) (G' := Hd.qZ α η v s) (hG 0 (v + 1)) (fun p => hmix p) (iZ 0) (iDp 1) (iDp 0)
    exact ha.trans ((congrArg Neg.neg (hb (v - 1) (Hd.qDp α η v s) (fun p => (hprev p).1) (iDp
        1))).trans (neg_neg _))
end Auto.HeatData
