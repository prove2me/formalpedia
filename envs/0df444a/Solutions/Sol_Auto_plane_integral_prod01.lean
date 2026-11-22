-- Prove2me | solution 1 for Auto.plane_integral_prod01
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:29:07.169012+00:00
-- url     : https://prove2.me/submissions/855ed183-12c9-4262-b92a-979f5cb810f7

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT

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
namespace Auto
theorem _root_.solution {k f g : ℝ → ℝ} (hk : Continuous k) (hf : Continuous f)
    (hg : Continuous g) (hki : Integrable k) (hfi : Integrable f) (hgi : Integrable g) :
    Integrable (fun p : Fin 3 → ℝ => k (p 0 + p 1 + p 2) * (f (p 0) * g (p 1))) ∧ ∫ p : Fin 3 →
      ℝ, k (p 0 + p 1 + p 2) * (f (p 0) * g (p 1)) = (∫ t, k t) * ((∫ t, f t) * (∫ t, g t)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have hmp : MeasurePreserving e.symm ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))
      volume := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
  set F : (Fin 3 → ℝ) → ℝ := fun p => k (p 0 + p 1 + p 2) * (f (p 0) * g (p 1))
  set F' : ℝ × (Fin 2 → ℝ) → ℝ := fun z => k (z.2 0 + z.2 1 + z.1) * (f (z.2 0) * g (z.2 1))
  have hFF : ∀ z, F (e.symm z) = F' z := fun z => rfl
  have hF'c : Continuous F' := by
    simp only [F']
    fun_prop
  have hprod : Integrable (fun q : Fin 2 → ℝ => |f (q 0)| * |g (q 1)|) := by
    have := Integrable.fintype_prod (f := ![fun t => |f t|, fun t => |g t|]) (μ := fun _ : Fin 2 =>
        (volume : Measure ℝ)) (fun i => by
        fin_cases i
        · exact hfi.abs
        · exact hgi.abs)
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    exact this
  have hF' : Integrable F' ((volume : Measure ℝ).prod volume) := by
    rw [integrable_prod_iff' hF'c.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun q => ?_, ?_⟩
    · change Integrable (fun x => k (q 0 + q 1 + x) * (f (q 0) * g (q 1)))
      exact (hki.comp_add_left (q 0 + q 1)).mul_const (f (q 0) * g (q 1))
    · have : (fun q : Fin 2 → ℝ => ∫ x, ‖F' (x, q)‖) =
          fun q => (∫ t, |k t|) * (|f (q 0)| * |g (q 1)|) := by
        funext q
        simp only [F', norm_mul, Real.norm_eq_abs]
        rw [integral_mul_const, integral_add_left_eq_self (fun t => |k t|)]
      rw [this]
      exact hprod.const_mul _
  have hF : Integrable F := by
    rw [← hmp.integrable_comp_emb e.symm.measurableEmbedding]
    exact hF'
  refine ⟨hF, ?_⟩
  rw [← hmp.integral_comp' (g := F)]
  simp only [hFF]
  rw [integral_prod_symm _ hF']
  have : ∀ q : Fin 2 → ℝ, ∫ x, F' (x, q) = (∫ t, k t) * (f (q 0) * g (q 1)) := by
    intro q
    simp only [F']
    rw [integral_mul_const, integral_add_left_eq_self k]
  simp only [this]
  rw [integral_const_mul]
  congr 1
  have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (f := ![f, g]) (μ := fun _ : Fin 2 => (volume :
      Measure ℝ))
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact this
end Auto
