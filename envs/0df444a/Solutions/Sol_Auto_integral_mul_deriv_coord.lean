-- Prove2me | solution 1 for Auto.integral_mul_deriv_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:20:16.259289+00:00
-- url     : https://prove2.me/submissions/526b95d9-d597-4cac-9d1f-07db272464f9

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
theorem _root_.solution {n : ℕ} (i : Fin (n + 1)) {F G F' G' : (Fin (n + 1) → ℝ) → ℝ}
    (hF : ∀ p, HasDerivAt (fun x => F (Function.update p i x)) (F' p) (p i))
    (hG : ∀ p, HasDerivAt (fun x => G (Function.update p i x)) (G' p) (p i))
    (h1 : Integrable (fun p => F p * G' p)) (h2 : Integrable (fun p => F' p * G p))
    (h3 : Integrable (fun p => F p * G p)) :
    ∫ p, F p * G' p = -∫ p, F' p * G p := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hmp : MeasurePreserving e.symm ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      volume := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hint : ∀ {f : (Fin (n + 1) → ℝ) → ℝ}, Integrable f →
      Integrable (fun z : ℝ × (Fin n → ℝ) => f (Fin.insertNth i z.1 z.2)) ((volume : Measure ℝ).prod
          volume) := by
    intro f hf
    exact (hmp.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  have hmain : ∀ {f : (Fin (n + 1) → ℝ) → ℝ}, Integrable f → ∫ p, f p =
      ∫ q : Fin n → ℝ, ∫ x : ℝ, f (Fin.insertNth i x q) := by
    intro f hf
    rw [← hmp.integral_comp' (g := f)]
    exact integral_prod_symm _ (hint hf)
  rw [hmain h1, hmain h2, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [(hint h1).prod_left_ae, (hint h2).prod_left_ae, (hint h3).prod_left_ae]
    with q hq1 hq2 hq3
  have hu : ∀ x, HasDerivAt (fun y => F (Fin.insertNth i y q)) (F' (Fin.insertNth i x q)) x := by
    intro x
    have := hF (Fin.insertNth i x q)
    simp only [Fin.update_insertNth, Fin.insertNth_apply_same] at this
    exact this
  have hv : ∀ x, HasDerivAt (fun y => G (Fin.insertNth i y q)) (G' (Fin.insertNth i x q)) x := by
    intro x
    have := hG (Fin.insertNth i x q)
    simp only [Fin.update_insertNth, Fin.insertNth_apply_same] at this
    exact this
  exact integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
    hq1 hq2 hq3
end Auto
