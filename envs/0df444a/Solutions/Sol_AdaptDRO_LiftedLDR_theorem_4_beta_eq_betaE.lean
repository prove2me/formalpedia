-- Prove2me | solution 1 for AdaptDRO.LiftedLDR.theorem_4_beta_eq_betaE
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:58:34.863889+00:00
-- url     : https://prove2.me/submissions/d68c811b-28a7-4dc9-963a-b750577c607f

import Mathlib
import Definitions.Def_AdaptDRO_LiftedLDR_Model

open AdaptDRO.LiftedLDR MeasureTheory

namespace CE4

/-- Counterexample model: I1 = 1, M = 2, N2 = 1, W = univ, d = 0. -/
noncomputable def cm : Model 1 0 0 2 0 1 where
  A0 := 0
  A := fun _ => 0
  b0 := 0
  b := fun _ j => if j = 0 then 1 else -1
  recourse := { B := fun _ _ => 1, d := 0 }
  G := 0
  mu := 0
  sigma := 0
  W := Set.univ
  g := fun i => i.elim0

lemma socprod : IsSOCProduct (Set.univ : Set (Fin 0 → ℝ)) := by
  refine ⟨0, fun i => i.elim0, fun j => j.elim0, fun j => j.elim0, ?_⟩
  ext w; simp

lemma socdata : cm.SOCData := by
  refine ⟨⟨0, 0, 0, 0, 0, Set.univ, socprod, ?_⟩, fun i => i.elim0⟩
  ext z; simp [cm]

lemma assum : cm.Assumption1 (0 : Matrix (Fin 0) (Fin 1) ℝ) (0 : Matrix (Fin 0) (Fin 0) ℝ)
    (0 : Matrix (Fin 0) (Fin 0) ℝ) (0 : Fin 0 → ℝ) Set.univ := by
  refine ⟨socprod, ?_, 0, 0, 0, ?_, fun i => i.elim0, ?_⟩
  · ext zu; simp [Model.liftedSupport, cm]
  · funext i; exact i.elim0
  · simp

lemma comp : cm.recourse.Complete := by
  intro t
  refine ⟨fun _ => t 0 ⊔ t 1, ?_⟩
  intro i
  simp [cm, Matrix.mulVec, dotProduct]
  fin_cases i <;> simp

lemma dual : cm.recourse.DualFeasible := by
  refine ⟨0, le_rfl, ?_⟩
  simp [cm]

lemma betaE_top : cm.betaE (fun i => i.elim0) = ⊤ := by
  unfold Model.betaE
  have : IsEmpty {y : ExtendedRule 1 0 1 // cm.ExtendedFeasible (fun i => i.elim0) y} := by
    refine ⟨fun ⟨y, hy⟩ => ?_⟩
    have h1 := hy ((fun _ => y.y0 0 + 1, fun i => i.elim0)) (by simp [Model.liftedSupport, cm])
    have h2 := hy ((fun _ => -(y.y0 0 + 1), fun i => i.elim0)) (by simp [Model.liftedSupport, cm])
    have h1' := h1 0
    have h2' := h2 1
    simp [cm, Model.bvec, Model.Amat, ExtendedRule.eval, Matrix.mulVec, dotProduct] at h1' h2'
    nlinarith
  exact iInf_of_empty _

lemma beta_le : cm.beta (fun i => i.elim0) ≤ 0 := by
  unfold Model.beta
  refine iSup_le fun P => ?_
  have : ∀ z, cm.Q (fun i => i.elim0) z = 0 := by
    intro z
    unfold Model.Q RecourseLP.value
    have : {c : ℝ | ∃ y : Fin 1 → ℝ, cm.rhs (fun i => i.elim0) z ≤ cm.recourse.B.mulVec y ∧
        c = dotProduct cm.recourse.d y} = {0} := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y, -, rfl⟩; simp [cm]
      · rintro rfl
        obtain ⟨y, hy⟩ := comp (cm.rhs (fun i => i.elim0) z)
        exact ⟨y, hy, by simp [cm]⟩
    rw [this]; simp
  simp [this]

end CE4

theorem solution : ¬ (∀ {I1 I2 I3 L1 L2 M N1 : ℕ} (m : Model I1 I2 L1 M N1 1)
    (C : Matrix (Fin L2) (Fin I1) ℝ)
    (D : Matrix (Fin L2) (Fin I2) ℝ)
    (E : Matrix (Fin L2) (Fin I3) ℝ)
    (h : Fin L2 → ℝ) (K : Set (Fin L2 → ℝ))
    (hSOC : m.SOCData) (hAssumption1 : m.Assumption1 C D E h K)
    (hrec : m.recourse.Complete) (hdual : m.recourse.DualFeasible),
    ∀ x : Fin N1 → ℝ, m.beta x = m.betaE x) := by
  intro H
  have := H (I3 := 0) CE4.cm 0 0 0 0 Set.univ CE4.socdata CE4.assum CE4.comp CE4.dual (fun i => i.elim0)
  rw [CE4.betaE_top] at this
  have h2 := CE4.beta_le
  rw [this] at h2
  simp at h2
