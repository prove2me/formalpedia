-- Prove2me | solution 1 for Auto.plane_integral_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:30:27.080579+00:00
-- url     : https://prove2.me/submissions/a39d85a0-9d41-49cb-b6da-e60dc95ae474

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_plane_integral_prod01

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
    (hg : Continuous g) (hki : Integrable k) (hfi : Integrable f) (hgi : Integrable g)
    {a b : Fin 3} (hab : a ≠ b) :
    Integrable (fun p : Fin 3 → ℝ => k (p 0 + p 1 + p 2) * (f (p a) * g (p b))) ∧ ∫ p : Fin 3 →
      ℝ, k (p 0 + p 1 + p 2) * (f (p a) * g (p b)) = (∫ t, k t) * ((∫ t, f t) * (∫ t, g t)) := by
  have hτ : ∀ a b : Fin 3, a ≠ b → ∃ τ : Equiv.Perm (Fin 3), τ 0 = a ∧ τ 1 = b := by decide
  obtain ⟨τ, h0, h1⟩ := hτ a b hab
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) τ
  set E := MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) τ
  have hE : ∀ (q : Fin 3 → ℝ) (c : Fin 3), E q c = q (τ.symm c) := fun q c => by
    simp [E, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have hsum : ∀ q : Fin 3 → ℝ, E q 0 + E q 1 + E q 2 = q 0 + q 1 + q 2 := by
    intro q
    simp only [hE]
    have := Equiv.sum_comp τ.symm q
    simp only [Fin.sum_univ_three] at this
    exact this
  have ha : ∀ q : Fin 3 → ℝ, E q a = q 0 := fun q => by rw [hE, ← h0, Equiv.symm_apply_apply]
  have hb : ∀ q : Fin 3 → ℝ, E q b = q 1 := fun q => by rw [hE, ← h1, Equiv.symm_apply_apply]
  obtain ⟨hI, hV⟩ := plane_integral_prod01 hk hf hg hki hfi hgi
  set F : (Fin 3 → ℝ) → ℝ := fun p => k (p 0 + p 1 + p 2) * (f (p a) * g (p b))
  have hFE : ∀ q, F (E q) = k (q 0 + q 1 + q 2) * (f (q 0) * g (q 1)) := fun q => by
    simp only [F, hsum, ha, hb]
  refine ⟨?_, ?_⟩
  · rw [← hmp.integrable_comp_emb E.measurableEmbedding]
    have : F ∘ E = fun q => k (q 0 + q 1 + q 2) * (f (q 0) * g (q 1)) := funext hFE
    rw [this]; exact hI
  · rw [← hmp.integral_comp' (g := F)]
    simp only [hFE]
    exact hV
end Auto
